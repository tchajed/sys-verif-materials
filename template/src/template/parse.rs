//! Parse Coq file as templates.

use std::mem;

use once_cell::sync::Lazy;
use regex::Regex;

use crate::coq::parse::{next_comment_at, Comment};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Tag {
    Meta,
    Solution,
    Exercise,
    Admitted,
    OnlyWeb,
    OmitWeb,
}

impl TryFrom<&str> for Tag {
    type Error = ();
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "META" => Ok(Tag::Meta),
            "SOLUTION" => Ok(Tag::Solution),
            "EXERCISE" => Ok(Tag::Exercise),
            "ADMITTED" => Ok(Tag::Admitted),
            "ONLY-WEB" => Ok(Tag::OnlyWeb),
            "OMIT-WEB" => Ok(Tag::OmitWeb),
            _ => Err(()),
        }
    }
}

impl Tag {
    pub fn as_str(&self) -> &'static str {
        match self {
            Tag::Meta => "META",
            Tag::Solution => "SOLUTION",
            Tag::Exercise => "EXERCISE",
            Tag::Admitted => "ADMITTED",
            Tag::OnlyWeb => "ONLY-WEB",
            Tag::OmitWeb => "OMIT-WEB",
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Directive {
    /// Record the output of the previous command.
    ///
    /// Implemented by using `Redirect`
    Output,
    /// Record the goal at this point.
    ///
    /// Implemented by running `Show 1.`
    Goals { num: usize },
    /// Record the goal and the previous goal to show the effect of the previous
    /// sentence, using `Show 1` commands.
    GoalDiff,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TemplatePart {
    Coq(String),
    Markdown {
        content: String,
        whitespace_after: String,
    },
    Tagged {
        tag: Tag,
        content: Template,
    },
    Directive(Directive),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Template {
    pub parts: Vec<TemplatePart>,
}

fn get_markdown_comment(s: Comment<'_>) -> Option<&str> {
    if s.mark == "|" {
        let comment = s.inner;
        let comment = comment.strip_suffix("|").unwrap_or(comment);
        let comment = comment.strip_suffix(" ").unwrap_or(comment);
        return Some(comment);
    }
    return None;
}

fn get_directive_comment(s: &str) -> Option<Directive> {
    static GOALS_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\{GOALS\s*([0-9]+)\}").unwrap());
    let s = s.trim();
    if let Some(m) = GOALS_RE.captures(s) {
        let num: &str = m.get(1).unwrap().as_str();
        let num = num.parse().unwrap();
        if num == 0 {
            panic!("cannot get 0 goals");
        }
        return Some(Directive::Goals { num });
    }
    match s.trim() {
        "{OUTPUT}" => Some(Directive::Output),
        "{GOAL}" => Some(Directive::Goals { num: 1 }),
        "{GOAL DIFF}" => Some(Directive::GoalDiff),
        _ => None,
    }
}

impl std::fmt::Display for Directive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // TODO: print num
            Directive::Goals { num: _ } => write!(f, "{{GOAL}}"),
            Directive::Output => write!(f, "{{OUTPUT}}"),
            Directive::GoalDiff => write!(f, "{{GOAL DIFF}}"),
        }
    }
}

enum TagPart {
    TagComplete(Tag, String),
    TagStart(Tag),
    NoTag,
}

fn parse_tagged_comment(s: &str) -> Result<TagPart, String> {
    static TAG_COMPLETE: Lazy<Regex> = Lazy::new(|| {
        Regex::new(
            r"(?x)
    ^\s* # leading whitespace after (*
    (?P<tagname>[A-Z_0-9-]*) # tags are upper-case but can contain _ and -
    :\s* # strip whitespace after TAG:",
        )
        .unwrap()
    });
    static TAG_START: Lazy<Regex> = Lazy::new(|| {
        Regex::new(
            r"(?x)
    ^\s* # leading whitespace after (*
    (?P<tagname>[A-Z_0-9-]*) # tags are upper-case
    \s*$ # no other text in comment
    ",
        )
        .unwrap()
    });
    if let Some(m) = TAG_COMPLETE.captures(s) {
        let tagname = &m["tagname"];
        if tagname == "TODO" || tagname == "FIXME" || tagname == "NOTE" {
            return Ok(TagPart::NoTag);
        }
        // unknown tags (which match the regular expressions above) are errors here
        let tag = Tag::try_from(tagname).map_err(|_| format!("invalid tag {tagname}"))?;
        let index = m.get(0).unwrap().end();
        Ok(TagPart::TagComplete(tag, s[index..].trim_end().to_string()))
    } else if let Some(m) = TAG_START.captures(s) {
        let tagname = &m["tagname"];
        let tag = Tag::try_from(&m["tagname"]).map_err(|_| format!("invalid tag {tagname}"))?;
        Ok(TagPart::TagStart(tag))
    } else {
        Ok(TagPart::NoTag)
    }
}

// skip one newline, if present
fn skip_newline(s: &str, mut index: usize) -> usize {
    if s[index..].starts_with("\n") {
        index += 1;
    }
    index
}

// get the index of the next non-newline character
fn skip_newlines(s: &str, mut index: usize) -> usize {
    while s[index..].starts_with("\n") {
        index += 1;
    }
    index
}

// get the index of the next non-whitespace character
fn skip_whitespace(s: &str, mut index: usize) -> usize {
    while s[index..].starts_with(char::is_whitespace) {
        index += 1;
    }
    index
}

// get the index of the next non-whitespace character
fn skip_empty_lines(s: &str, index: usize) -> usize {
    static EMPTY_LINES: Lazy<Regex> = Lazy::new(|| Regex::new(r"(?m)\A\s*\n").unwrap());
    match EMPTY_LINES.find(&s[index..]) {
        None => index,
        Some(m) => index + m.end(),
    }
}

// Find a closing tag, starting at index. Returns two indices: the first is the
// end of the inside of the match, the second is the end of the closing tag.
fn find_end_tag(s: &str, index: usize, tag: Tag) -> Result<(usize, usize), String> {
    let mut index = index;
    loop {
        match next_comment_at(s, index)? {
            None => return Err(format!("unterminated tag {}", tag.as_str())),
            Some(c) => {
                if c.inner == format!("/{}", tag.as_str()) {
                    return Ok((c.start(), c.end()));
                }
                index = c.end();
            }
        }
    }
}

fn pre_directive_whitespace_index(s: &str) -> usize {
    static TRAILING_WHITESPACE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\n?[\s--\n]*$").unwrap());
    TRAILING_WHITESPACE.find(s).unwrap().start()
}

fn parse_template(s: &str) -> Result<Template, String> {
    let mut parts = Vec::new();
    let mut index = 0;

    loop {
        match next_comment_at(s, index)? {
            None => {
                parts.push(TemplatePart::Coq(s[index..].to_string()));
                break;
            }
            Some(c) => {
                // pre-comment portion
                let comment = &c.inner;
                if let Some(md) = get_markdown_comment(c) {
                    let next_index = skip_empty_lines(s, c.end());
                    let whitespace_after = s[c.end()..next_index].to_string();
                    parts.push(TemplatePart::Coq(s[index..c.start()].to_string()));
                    parts.push(TemplatePart::Markdown {
                        content: md.to_string(),
                        whitespace_after,
                    });
                    index = next_index;
                } else if let Some(d) = get_directive_comment(comment) {
                    let comment_start =
                        pre_directive_whitespace_index(&s[index..c.start()]) + index;
                    parts.push(TemplatePart::Coq(s[index..comment_start].to_string()));
                    parts.push(TemplatePart::Directive(d));
                    index = c.end();
                } else {
                    match parse_tagged_comment(comment)
                        .map_err(|e| format!("{e} at index {}", c.start()))?
                    {
                        TagPart::TagComplete(tag, content) => {
                            parts.push(TemplatePart::Coq(s[index..c.start()].to_string()));
                            let inner = parse_template(&content)?;
                            parts.push(TemplatePart::Tagged {
                                tag,
                                content: inner,
                            });
                            // skip over the comment and "soak" any following
                            // whitespace, placing the next text at the start of the tag
                            index = skip_whitespace(s, c.end());
                        }
                        // For a start tag like (* META *) or (* SOLUTION *) we
                        // need to skip far ahead and find the end tag. Once we
                        // find the span of the tag, we recursively parse its
                        // inner contents.
                        TagPart::TagStart(tag) => {
                            parts.push(TemplatePart::Coq(s[index..c.start()].to_string()));
                            let (end_start, end_end) = find_end_tag(s, c.end(), tag)
                                .map_err(|e| format!("{e} at index {}", c.start()))?;
                            let tag_start = skip_newlines(s, c.end());
                            let inner = parse_template(&s[tag_start..end_start])?;
                            parts.push(TemplatePart::Tagged {
                                tag,
                                content: inner,
                            });
                            index = skip_newline(s, end_end);
                        }
                        TagPart::NoTag => {
                            // just a regular comment - add it literally
                            parts.push(TemplatePart::Coq(s[index..c.end()].to_string()));
                            index = c.end();
                        }
                    }
                }
            }
        }
    }

    Ok(Template { parts })
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TagAction {
    Unwrap,
    Remove,
    Keep,
}

impl Template {
    fn combine_adjacent_coq(&mut self) {
        let mut i = 0;
        while i + 1 < self.parts.len() {
            match (&self.parts[i], &self.parts[i + 1]) {
                (TemplatePart::Coq(s), TemplatePart::Coq(t)) => {
                    self.parts[i] = TemplatePart::Coq(format!("{s}{t}"));
                    self.parts.remove(i + 1);
                }
                _ => {
                    i += 1;
                }
            }
        }
    }

    fn remove_empty_coq(&mut self) {
        self.parts = mem::take(&mut self.parts)
            .into_iter()
            .filter(|part| match part {
                TemplatePart::Coq(s) => !s.is_empty(),
                _ => true,
            })
            .collect();
    }

    fn normalize(&mut self) {
        self.combine_adjacent_coq();
        self.remove_empty_coq();
        // recurse into tagged content
        for part in self.parts.iter_mut() {
            if let TemplatePart::Tagged { content, .. } = part {
                content.normalize();
            }
        }
    }

    fn normalized(self) -> Self {
        let mut template = self;
        template.normalize();
        template
    }

    pub fn parse(s: &str) -> Result<Self, String> {
        parse_template(s).map(|tmpl| tmpl.normalized())
    }

    /// Admitted tags are syntactic sugar for an Exercise-tagged "Admitted" and
    /// the original body tagged Solution. This should be processed relatively
    /// early.
    pub fn interpret_admitted_tags(self: &mut Template) {
        self.parts = mem::take(&mut self.parts)
            .into_iter()
            .flat_map(|part| match part {
                TemplatePart::Tagged {
                    tag: Tag::Admitted,
                    content,
                } => {
                    vec![
                        TemplatePart::Tagged {
                            tag: Tag::Exercise,
                            content: Template {
                                parts: vec![TemplatePart::Coq("Admitted.\n".to_string())],
                            },
                        },
                        TemplatePart::Tagged {
                            tag: Tag::Solution,
                            content,
                        },
                    ]
                }
                TemplatePart::Tagged { tag, content } => {
                    let mut new = content.clone();
                    new.interpret_admitted_tags();
                    vec![TemplatePart::Tagged { tag, content: new }]
                }
                _ => vec![part.clone()],
            })
            .collect();
    }

    /// Replace tags with Coq(...) blocks. Each block can either be unwrapped
    /// and replaced with its content, or removed.
    pub fn filter_tags<F>(&mut self, mut f: F)
    where
        F: FnMut(Tag) -> TagAction,
    {
        self.parts = mem::take(&mut self.parts)
            .into_iter()
            .flat_map(|part| match part {
                TemplatePart::Tagged { tag, content } => {
                    let action = f(tag);
                    match action {
                        TagAction::Unwrap => content.parts,
                        TagAction::Keep => vec![TemplatePart::Tagged { tag, content }],
                        TagAction::Remove => vec![],
                    }
                }
                _ => vec![part],
            })
            .collect();
        self.normalize();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_template_parts(s: &str) -> Vec<TemplatePart> {
        Template::parse(s).unwrap().parts
    }

    fn coq(s: &str) -> TemplatePart {
        TemplatePart::Coq(s.to_string())
    }

    fn markdown(s: &str, whitespace: &str) -> TemplatePart {
        TemplatePart::Markdown {
            content: s.to_string(),
            whitespace_after: whitespace.to_string(),
        }
    }

    fn meta(s: &str) -> TemplatePart {
        TemplatePart::Tagged {
            tag: Tag::Meta,
            content: Template::parse(s).unwrap(),
        }
    }

    #[test]
    fn test_no_comments() {
        let s = " Definition foo := bar.y.\n";
        assert_eq!(parse_template_parts(s), vec![coq(s)],);
    }

    #[test]
    fn test_just_comment() {
        let s = "(* coq *)\n";
        assert_eq!(parse_template_parts(s), vec![coq(s)],);
    }

    #[test]
    fn test_coq_nested_comment() {
        let s = "(* coq (* another comment *) *)\n";
        assert_eq!(parse_template_parts(s), vec![coq(s)],);
    }

    #[test]
    fn test_just_markdown() {
        let s = "(*| markdown |*)";
        assert_eq!(parse_template_parts(s), vec![markdown("markdown", "")],);
    }

    #[test]
    fn test_just_markdown_no_close_pipe() {
        // no pipe in ending brace
        let s = "(*| markdown *)";
        assert_eq!(parse_template_parts(s), vec![markdown("markdown", "")],);
    }

    #[test]
    fn test_markdown_nl() {
        let s = "(*| markdown |*)\n";
        assert_eq!(parse_template_parts(s), vec![markdown("markdown", "\n")],);
    }

    #[test]
    fn test_skip_empty_lines() {
        let s = "  \n  \n  ";
        assert_eq!(skip_empty_lines(s, 0), "  \n  \n".len());
        assert_eq!(skip_empty_lines(s, 1), "  \n  \n".len());
        assert_eq!(skip_empty_lines(s, "  \n  \n".len()), "  \n  \n".len());
    }

    #[test]
    fn test_markdown_indent_after() {
        let s = "(*| markdown |*)\n  Definition";
        assert_eq!(
            parse_template_parts(s),
            vec![markdown("markdown", "\n"), coq("  Definition")],
        );
    }

    #[test]
    fn test_unterminated_comment() {
        let r = Template::parse("(* some stuff");
        assert!(r.is_err(), "expected error, got {r:?}");
    }

    #[test]
    fn test_markdown_nested_comment() {
        let s = "(*| (* nested *) |*)";
        assert_eq!(parse_template_parts(s), vec![markdown("(* nested *)", "")],);
    }

    #[test]
    fn test_contained_tag() {
        let s = "(* META: some meta *)";
        assert_eq!(parse_template_parts(s), vec![meta("some meta")]);
    }

    #[test]
    fn test_contained_tag_soak_newline() {
        let s = "(* META: some meta *)\n\nsome more text";
        assert_eq!(
            parse_template_parts(s),
            vec![meta("some meta"), coq("some more text")],
        );
    }

    #[test]
    fn test_tag_pair() {
        let s = r"(* EXERCISE *)
(* FILL IN HERE *)
Admitted.
(* /EXERCISE *)";
        assert_eq!(
            parse_template_parts(s),
            vec![TemplatePart::Tagged {
                tag: Tag::Exercise,
                content: Template {
                    parts: vec![coq("(* FILL IN HERE *)\nAdmitted.\n")],
                },
            }],
        );
    }

    #[test]
    fn test_directive() {
        let s = "Check 1. (* {OUTPUT} *)";
        assert_eq!(
            parse_template_parts(s),
            vec![coq("Check 1."), TemplatePart::Directive(Directive::Output)],
        );
    }

    #[test]
    fn test_whole_file() {
        let s = r"
(*| # Introduction to Coq
|*)

(** META: This is a meta comment. *)

(* META *)
(* This file is an example of a literate Coq file. *)
(* /META *)
(*| In this lecture, we'll get an introduction to functional programming.

To write functional programs, we'll start by defining some data types for
our functions to operate on. |*)

Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

(*| Now what we have `day`, we can define functions on days: |*)

(* META: the following coqdoc comment will be inserted as Coq input rather
than surrounding text *)
(** next_weekday is a simple example of a function operating on [day] *)
Definition next_weekday (d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
(* {OUTPUT} *)
"
        .trim();

        let parts = parse_template_parts(s);
        let expected = vec![
            markdown("# Introduction to Coq\n", "\n\n"),
            meta("This is a meta comment."),
            meta("(* This file is an example of a literate Coq file. *)\n"),
            markdown(
                r"In this lecture, we'll get an introduction to functional programming.

To write functional programs, we'll start by defining some data types for
our functions to operate on.",
                "\n\n",
            ),
            coq(r"Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

"),
            markdown(
                "Now what we have `day`, we can define functions on days:",
                "\n\n",
            ),
            meta(
                r"the following coqdoc comment will be inserted as Coq input rather
than surrounding text",
            ),
            coq(
                r"(** next_weekday is a simple example of a function operating on [day] *)
Definition next_weekday (d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).",
            ),
            TemplatePart::Directive(Directive::Output),
        ];

        for i in 0..parts.len() {
            assert_eq!(parts[i], expected[i], "part {i} mismatch");
        }
        assert_eq!(parts.len(), expected.len(), "wrong number of parts");
    }

    #[test]
    fn test_goal_directive() {
        let s = r"Lemma foo : True.
Proof.
(* {GOAL} *)
Admitted.";

        assert_eq!(
            parse_template_parts(s),
            vec![
                coq("Lemma foo : True.\nProof."),
                TemplatePart::Directive(Directive::Goals { num: 1 }),
                coq("\nAdmitted."),
            ],
        );
    }

    #[test]
    fn test_tag_whitespace() {
        let s = r"(* EXERCISE:   has spaces *)";
        assert_eq!(
            parse_template_parts(s),
            vec![TemplatePart::Tagged {
                tag: Tag::Exercise,
                content: Template {
                    parts: vec![coq("has spaces")],
                },
            }],
        );
    }

    /// when a directive is at the end of a line with other content, its
    /// deletion should remove just the comment and preceding whitespace, not
    /// the newline.
    #[test]
    fn test_directive_same_line1() {
        let s = "  text. (* {OUTPUT} *)\n  after.";
        assert_eq!(
            parse_template_parts(s),
            vec![
                coq("  text."),
                TemplatePart::Directive(Directive::Output),
                coq("\n  after."),
            ],
        );
    }

    /// An obscure case that you probably don't want to write: following the
    /// rules, the directive soaks the whitespace before but not after.
    #[test]
    fn test_directive_same_line_between() {
        let s = "  text. (* {OUTPUT} *) after.";
        assert_eq!(
            parse_template_parts(s),
            vec![
                coq("  text."),
                TemplatePart::Directive(Directive::Output),
                coq(" after."),
            ],
        );
    }

    /// when a directive is on its own line, its deletion should remove an
    /// extra newline
    #[test]
    fn test_directive_own_line() {
        let s = r"
  text.
  (* {OUTPUT} *)
  after.";
        assert_eq!(
            parse_template_parts(s),
            vec![
                coq("\n  text."),
                TemplatePart::Directive(Directive::Output),
                coq("\n  after."),
            ],
        );
    }

    #[test]
    fn test_pre_directive_whitespace() {
        fn pre_directive_whitespace(s: &str) -> &str {
            &s[pre_directive_whitespace_index(s)..]
        }
        assert_eq!(pre_directive_whitespace("foo\n"), "\n");
        assert_eq!(pre_directive_whitespace("\n \nfoo\n"), "\n");
        assert_eq!(pre_directive_whitespace("\n \nfoo  "), "  ");
        assert_eq!(pre_directive_whitespace("foo\nbar\n\t"), "\n\t");
        assert_eq!(pre_directive_whitespace("foo\nbar\nx\t"), "\t");
    }

    #[test]
    fn test_only_web() {
        let s = "(* ONLY-WEB *)\ntext(* /ONLY-WEB *)";
        assert_eq!(
            parse_template_parts(s),
            vec![TemplatePart::Tagged {
                tag: Tag::OnlyWeb,
                content: Template {
                    parts: vec![coq("text")],
                },
            },]
        );
    }
}
