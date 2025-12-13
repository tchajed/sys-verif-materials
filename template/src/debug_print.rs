use crate::template::{Template, TemplatePart};

fn debug_print_template_indent(indent: usize, tmpl: &Template) {
    for part in &tmpl.parts {
        if let TemplatePart::Tagged { tag, content } = part {
            println!("{}{}:", "  ".repeat(indent), tag.as_str());
            debug_print_template_indent(indent + 1, content);
        } else {
            println!("{}{:?}", "  ".repeat(indent), part);
        }
    }
}

pub fn debug_print_template(tmpl: &Template) {
    debug_print_template_indent(0, tmpl);
}
