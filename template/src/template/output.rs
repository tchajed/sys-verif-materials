//! Get the output for a template.

use crate::coq::{CoqConfig, CoqFile};

use super::{Directive, Tag, Template, TemplatePart};

use anyhow::Context;

fn push_template_directives(tmpl: &Template, file: &mut CoqFile) {
    for i in 0..tmpl.parts.len() {
        match &tmpl.parts[i] {
            TemplatePart::Coq(content) => {
                file.push_str(content);
            }
            TemplatePart::Directive(Directive::Output) => {
                file.add_output("out");
            }
            TemplatePart::Directive(Directive::Goals { num }) => {
                let num = *num;
                for i in 1..=num {
                    file.push_str(&format!(" Show {i}.\n"));
                    file.add_output("goal");
                }
            }
            TemplatePart::Directive(Directive::GoalDiff) => {
                // TODO: bug when there is a period in a comment prior to the
                // last sentence
                // TODO: seemed to be a bug in capturing a `Fail` command, not
                // sure what the cause is.
                let last_sentence = file.remove_sentence();
                // add a Show 1 to get the goal before the last sentence
                file.push_str(" Show 1.\n");
                file.add_output("goal");
                file.push_str(&last_sentence);
                // and add another Show 1 to get the goal afterward
                file.push_str(" Show 1.\n");
                file.add_output("goal");
            }
            TemplatePart::Tagged { tag, content } => {
                if *tag == Tag::OnlyWeb || *tag == Tag::OmitWeb {
                    push_template_directives(content, file);
                }
                // otherwise ignore
            }
            TemplatePart::Markdown { .. } => {
                // do nothing, these are ignored
            }
        }
    }
}

/// Construct a Coq file that will process the directives in a template.
///
/// The only tags used are OnlyWeb and OmitFromWeb; unwrap other tags to include
/// them.
///
/// This file does not preserve position info (not even line numbers) from the
/// original file. It is not intended to generate a vo file, only output text,
/// though it should not add any side effects or remove anything (other than
/// comments) from the original file.
fn template_directives_to_file(tmpl: &Template) -> CoqFile {
    let mut file = CoqFile::new();
    push_template_directives(tmpl, &mut file);
    file
}

impl Template {
    fn has_directives(&self) -> bool {
        for part in &self.parts {
            if let TemplatePart::Directive(_) = part {
                return true;
            }
            if let TemplatePart::Tagged { tag: _, content } = part {
                if content.has_directives() {
                    return true;
                }
            }
        }
        return false;
    }
    /// Get the coq output from a template.
    pub fn get_outputs(&self, coq_config: &impl CoqConfig) -> Result<Vec<String>, anyhow::Error> {
        if !self.has_directives() {
            return Ok(vec![]);
        }
        let coq_file = template_directives_to_file(self);
        let outputs = coq_config.get_outputs(&coq_file).with_context(|| {
            format!(
                "output directive file contents:\n\n{}\n",
                coq_file.contents()
            )
        })?;
        Ok(outputs)
    }
}
