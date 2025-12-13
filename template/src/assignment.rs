//! Convert assignment templates to exercise files (for students) and solutions.
//!
//! Also works with demos with the "exercise" being the starting point for an
//! in-class assignment.

use std::mem;

use crate::template::{Tag, TagAction, Template, TemplatePart};

fn template_as_exercise_or_solution(tmpl: &Template, solution: bool) -> Template {
    let mut tmpl = tmpl.clone();
    tmpl.interpret_admitted_tags();
    tmpl.parts = mem::take(&mut tmpl.parts)
        .into_iter()
        .filter(|part| !matches!(part, TemplatePart::Directive(_)))
        .collect();
    let keep_tag = if solution {
        Tag::Solution
    } else {
        Tag::Exercise
    };
    tmpl.filter_tags(|tag| match tag {
        Tag::Exercise | Tag::Solution => {
            if tag == keep_tag {
                TagAction::Unwrap
            } else {
                TagAction::Remove
            }
        }
        Tag::Meta => TagAction::Remove,
        Tag::OmitWeb => TagAction::Unwrap,
        Tag::OnlyWeb => TagAction::Remove,
        Tag::Admitted => panic!("should have been interpreted"),
    });
    tmpl
}

fn template_to_coq(tmpl: &Template) -> String {
    let mut out = String::new();
    for part in tmpl.parts.iter() {
        match part {
            TemplatePart::Markdown {
                content: md,
                whitespace_after,
            } => {
                let inner_end_whitespace = if md.ends_with(char::is_whitespace) {
                    ""
                } else {
                    " "
                };
                out.push_str(&format!(
                    "(*| {md}{inner_end_whitespace}|*){whitespace_after}"
                ))
            }
            TemplatePart::Coq(s) => {
                out.push_str(s);
            }
            TemplatePart::Directive(_) => {}
            TemplatePart::Tagged { tag, .. } => {
                panic!("unexpected tag left {}", tag.as_str());
            }
        }
    }
    out
}

pub fn exercise_file(tmpl: &Template) -> String {
    template_to_coq(&template_as_exercise_or_solution(tmpl, false))
}

pub fn solution_file(tmpl: &Template) -> String {
    template_to_coq(&template_as_exercise_or_solution(tmpl, true))
}

#[cfg(test)]
mod tests {
    use std::fs;

    use insta::assert_snapshot;

    use super::*;

    #[test]
    fn exercise_output() {
        let src = fs::read_to_string("tests/examples/assignment.v").expect("could not find input");
        let tmpl = Template::parse(&src).expect("could not parse assignment template");
        assert_snapshot!("assignment_exercise.v", exercise_file(&tmpl));
    }

    #[test]
    fn solution_output() {
        let src = fs::read_to_string("tests/examples/assignment.v").expect("could not find input");
        let tmpl = Template::parse(&src).expect("could not parse assignment template");
        assert_snapshot!("assignment_solution.v", solution_file(&tmpl));
    }
}
