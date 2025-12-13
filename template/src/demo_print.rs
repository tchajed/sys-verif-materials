use crate::template::{Tag, TagAction, Template, TemplatePart};

pub fn demo_file(tmpl: &Template) -> String {
    let mut tmpl = tmpl.clone();
    tmpl.interpret_admitted_tags();
    tmpl.filter_tags(|tag| match tag {
        Tag::Exercise => TagAction::Unwrap,
        Tag::Solution => TagAction::Remove,
        Tag::OmitWeb => TagAction::Unwrap,
        _ => TagAction::Remove,
    });
    let mut out = String::new();
    for part in tmpl.parts.iter() {
        match part {
            // main point of demos is to not show markdown
            TemplatePart::Markdown { .. } => {}
            TemplatePart::Coq(s) => {
                out.push_str(s);
            }
            TemplatePart::Directive(d) => {
                out.push_str(&format!(" (* {d} *)"));
            }
            TemplatePart::Tagged { tag, .. } => {
                panic!("unexpected tag left {}", tag.as_str());
            }
        }
    }
    out
}
