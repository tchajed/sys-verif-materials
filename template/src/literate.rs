//! Convert literate Coq files to Markdown.
//!
//! Processes directives for capturing Coq's output and goal.
use std::{fs, path::Path};

use anyhow::{anyhow, Context as _};
use once_cell::sync::Lazy;
use regex::Regex;
use similar::{Algorithm, ChangeTag};

use crate::coq::CoqConfig;
use crate::template::{Directive, Tag, TagAction, Template, TemplatePart};

fn clean_goal_display(goal: &str) -> String {
    static PREFIX_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"(?m)^goal [0-9]+ is:\s*$").unwrap());
    let goal = PREFIX_RE.find(goal).map_or(goal, |m| &goal[m.end()..]);
    let goal = goal.trim_start_matches('\n');
    // remove these boilerplate lines of Context from web output, to keep goals
    // shorter
    static FILTER_RE: Lazy<Regex> = Lazy::new(|| {
        Regex::new(r"(Σ : gFunctors|heapGS0 : heapGS Σ|hG : heapGS Σ|sem : go.Semantics)").unwrap()
    });
    goal.lines()
        .filter(|line| FILTER_RE.find(line).is_none())
        .collect::<Vec<_>>()
        .join("\n")
}

fn md_code_block(lang: &str, title: Option<&str>, content: &str) -> String {
    let mut out = String::new();
    match title {
        Some(title) => out.push_str(&format!("```{lang} title=\"{title}\"\n")),
        None => out.push_str(&format!("```{lang}\n")),
    }
    out.push_str(content);
    if !content.ends_with('\n') {
        out.push('\n');
    }
    out.push_str("```\n");
    out
}

/// Create a diff between two strings with shiki "notation diff" annotations.
fn diff_code(before: &str, after: &str) -> String {
    // create a diff between before and after with shiki notation diff
    // annotations (eg, [!code --])
    //
    // note that these are written with // even though they're in Coq
    // output, but shiki will remove this anyway
    //
    // See https://shiki.style/packages/transformers#transformernotationdiff.

    let mut out = String::new();
    for (tag, line) in similar::utils::diff_lines(Algorithm::Patience, before, after) {
        let line = line.strip_suffix("\n").unwrap_or(line);
        match tag {
            ChangeTag::Equal => out.push_str(&format!("{line}\n")),
            ChangeTag::Delete => out.push_str(&format!("{line} // [!code --]\n")),
            ChangeTag::Insert => out.push_str(&format!("{line} // [!code ++]\n")),
        }
    }
    out
}

fn md_part(md: String) -> TemplatePart {
    TemplatePart::Markdown {
        content: md,
        whitespace_after: "".to_string(),
    }
}

fn process_directives(tmpl: &mut Template, mut outputs: &[String]) {
    for part in tmpl.parts.iter_mut() {
        let TemplatePart::Directive(d) = part else {
            continue;
        };
        let mut md = String::new();
        match d {
            Directive::Output => {
                let next_out;
                (next_out, outputs) = (&outputs[0], &outputs[1..]);
                md.push_str("\n\n");
                md.push_str(":::: note Output\n\n");
                md.push_str(&md_code_block("txt", None, next_out));
                md.push_str("\n::::\n\n");
            }
            Directive::Goals { num } => {
                let num = *num;
                md.push_str("\n\n");
                md.push_str(&format!(
                    ":::: info {}\n\n",
                    if num == 1 { "Goal" } else { "Goals" }
                ));
                for i in 1..=num {
                    let goal;
                    (goal, outputs) = (&outputs[0], &outputs[1..]);
                    let title = if num > 1 {
                        Some(format!("goal {i}"))
                    } else {
                        None
                    };
                    md.push_str(&md_code_block(
                        "txt",
                        title.as_deref(),
                        &clean_goal_display(goal),
                    ));
                    md.push('\n');
                }
                md.push_str("\n::::\n\n");
            }
            Directive::GoalDiff => {
                let (goal_before, goal_after);
                (goal_before, goal_after, outputs) = (&outputs[0], &outputs[1], &outputs[2..]);
                let goal_before = &clean_goal_display(goal_before);
                let goal_after = &clean_goal_display(goal_after);
                md.push_str("\n\n");
                md.push_str(":::: info Goal diff\n\n");
                md.push_str(&md_code_block(
                    "txt",
                    None,
                    &diff_code(goal_before, goal_after),
                ));
                md.push_str("\n::::\n\n");
            }
        }
        *part = md_part(md);
    }
    if !outputs.is_empty() {
        eprintln!(
            "[template] internal error: have {} extra outputs:",
            outputs.len()
        );
        for output in outputs {
            eprintln!("  {output}");
        }
    }
}

fn template_to_markdown(tmpl: &Template, outputs: &[String]) -> String {
    let mut tmpl = tmpl.clone();
    process_directives(&mut tmpl, outputs);
    let mut out = String::new();
    for part in tmpl.parts.iter() {
        match part {
            TemplatePart::Markdown {
                content: md,
                whitespace_after,
            } => {
                out.push_str(md);
                if !whitespace_after.is_empty() {
                    out.push('\n');
                }
            }
            TemplatePart::Coq(s) => {
                // remove initial empty lines but keep indentation
                let code = s.trim_start_matches('\n');
                if code.trim().is_empty() {
                    continue;
                }
                out.push('\n');
                out.push_str(&md_code_block("rocq", None, code));
                out.push('\n');
            }
            TemplatePart::Directive(_) => panic!("should be processed already"),
            // ignore tags - should be preprocessed with something like map_tags
            // first
            TemplatePart::Tagged { .. } => {}
        }
    }
    out
}

fn add_autogenerated_notice(md: &str) -> String {
    let notice = "Auto-generated from literate source. DO NOT EDIT.";
    // if the markdown starts with a YAML frontmatter block, add the notice as a
    // YAML comment, otherwise use a Markdown (HTML) comment.
    match md.strip_prefix("---\n") {
        Some(md) => format!("---\n# {notice}\n{md}"),
        None => format!("<!-- {notice} -->\n{md}"),
    }
}

/// Convert a literate file on disk at `tmpl_path` to Markdown, processing Coq
/// directives using `coq_config`. If `solution` is true then solution tags are
/// kept, while otherwise only exercise tags are kept.
pub fn literate_to_markdown(
    tmpl_path: &Path,
    solution: bool,
    coq_config: &impl CoqConfig,
) -> Result<String, anyhow::Error> {
    let tmpl_file = fs::read_to_string(tmpl_path)
        .with_context(|| format!("could not read literate file at {}", tmpl_path.display()))?;
    let mut tmpl = Template::parse(&tmpl_file)
        .map_err(|err| anyhow!("could not parse literate template: {err}"))?;
    tmpl.interpret_admitted_tags();
    tmpl.filter_tags(|tag| {
        let keep_solution = solution;
        let keep_exercise = !solution;
        #[allow(clippy::if_same_then_else)]
        if (tag == Tag::Solution && keep_solution) || (tag == Tag::Exercise && keep_exercise) {
            TagAction::Unwrap
        } else if tag == Tag::OnlyWeb {
            TagAction::Unwrap
        } else if tag == Tag::OmitWeb {
            TagAction::Keep
        } else {
            TagAction::Remove
        }
    });
    let outputs = tmpl.get_outputs(coq_config).with_context(|| {
        format!(
            "could not process template directives in {}",
            tmpl_path.display()
        )
    })?;
    tmpl.filter_tags(|tag| {
        if tag == Tag::OmitWeb {
            TagAction::Remove
        } else {
            TagAction::Keep
        }
    });
    let md = template_to_markdown(&tmpl, &outputs);
    let md = add_autogenerated_notice(&md);
    Ok(md)
}

#[cfg(test)]
mod tests {
    use insta::assert_snapshot;

    use crate::coq::{is_rocq_available, CoqArgs};

    use super::*;

    #[test]
    fn test_clean_goal_display() {
        let goal = r#"goal 1 is:

  m : gmap Z V
  k : Z
  v : V
  ============================
  delete k (<[k:=v]> m) !! k = delete k m !! k"#;
        let cleaned = clean_goal_display(goal);
        assert_eq!(
            cleaned,
            r#"  m : gmap Z V
  k : Z
  v : V
  ============================
  delete k (<[k:=v]> m) !! k = delete k m !! k"#,
        );
    }

    #[test]
    fn test_literate_example_intro() {
        // NOTE: this warning is not visible so if rocq isn't available the test is silently skipped
        if !is_rocq_available() {
            eprintln!("rocq not found in PATH; skipping test");
            return;
        }
        let md = literate_to_markdown(Path::new("tests/examples/intro.v"), true, &CoqArgs::new())
            .expect("template should parse");
        assert_snapshot!("intro.md", md);
    }

    /// Test that includes GoalDiff directives.
    #[test]
    fn test_literate_example_diff_ltac() {
        if !is_rocq_available() {
            eprintln!("rocq not found in PATH; skipping test");
            return;
        }
        let md = literate_to_markdown(Path::new("tests/examples/ltac.v"), true, &CoqArgs::new())
            .expect("template should parse");
        assert_snapshot!("ltac.md", md);
    }
}
