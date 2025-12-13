//! Parsing Coq code, especially oriented towards interpreting comments.

use once_cell::sync::Lazy;
use regex::Regex;

static NOT_SENTENCE: Lazy<Regex> = Lazy::new(|| Regex::new(r"^\.(\w|\()").unwrap());
static WHITESPACE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\s*").unwrap());

fn next_sentence_period(s: &str, index: usize) -> Option<usize> {
    let next_period = index + s[index..].find('.')?;
    // ignore next_period if it's in a comment
    if let Some(c) = next_comment_at(s, index).unwrap_or(None) {
        if c.start() < next_period {
            return next_sentence_period(s, c.end());
        }
    }
    if NOT_SENTENCE.is_match(&s[next_period..]) {
        return next_sentence_period(s, next_period + 1);
    }
    Some(next_period)
}

/// Get all sentence spans (start and end indices into string), ignoring
/// comments and leading whitespace for each sentence.
fn sentence_spans(s: &str) -> Vec<(usize, usize)> {
    let mut spans = vec![];
    let mut i = 0;
    while let Some(last_period) = next_sentence_period(s, i) {
        let sentence_start = WHITESPACE_RE.find_at(s, i).unwrap().end();
        let sentence_end = last_period + 1;
        assert!(sentence_start <= sentence_end);
        spans.push((sentence_start, sentence_end));
        i = last_period + 1;
    }
    // leaves an incomplete sentence past the span of the last sentence returned
    spans
}

/// Get the range of the last Coq sentence in a string.
///
/// The range excludes leading whitespace and includes the period at the end.
pub fn last_sentence_span(s: &str) -> Option<(usize, usize)> {
    return sentence_spans(s).last().cloned();
}

static COMMENT_START: Lazy<Regex> = Lazy::new(|| Regex::new(r"\(\*").unwrap());
static COMMENT_END: Lazy<Regex> = Lazy::new(|| Regex::new(r"\*\)").unwrap());

fn start_comment_at(s: &str, index: usize) -> Option<regex::Match<'_>> {
    COMMENT_START.find_at(s, index)
}

#[derive(Copy, Clone, Debug)]
pub struct Comment<'a> {
    // start and end positions of comment markers
    span: (usize, usize),
    #[allow(dead_code)]
    // the text within span excluding comment markers
    raw_inner: &'a str,
    /// The "mark" that starts the comment; any non-whitespace after the initial
    /// (*. This allows whitespace in `(** foo *)` to be treated as if the
    /// contents of the comment were ` foo ` even though its actually `* foo `.
    pub mark: &'a str,
    /// The contents of the comment with "intelligent" whitespace handling,
    /// after removing `mark`.
    ///
    /// If the comment starts with a space and no newline (like `(* comment
    /// *)`), then only the leading space and one trailing space are removed.
    ///
    /// If the comment starts with a newline (like `(*\ncomment\n*)`), then that
    /// newline is removed, and the trailing whitespace is replaced with a
    /// single newline (removing any indentation before the close marker, for
    /// example).
    pub inner: &'a str,
}

impl Comment<'_> {
    /// The index of the start of the comment's `(*`.
    pub fn start(&self) -> usize {
        self.span.0
    }

    /// The index of the end of the comment's `*)`.
    pub fn end(&self) -> usize {
        self.span.1
    }
}

// where does a comment started before index end?
//
// returns the end of the *) marker
fn end_comment_at(s: &str, index: usize) -> Option<usize> {
    let mut depth = 1;
    let mut index = index;
    while depth > 0 {
        let (start_m, end_m) = (
            COMMENT_START.find_at(s, index),
            COMMENT_END.find_at(s, index),
        );
        match (start_m, end_m) {
            (Some(start), Some(end)) => {
                if start.start() < end.start() {
                    index = start.end();
                    depth += 1;
                } else {
                    index = end.end();
                    depth -= 1;
                }
            }
            (None, Some(end)) => {
                index = end.end();
                depth -= 1;
            }
            (_, None) => {
                return None;
            }
        }
    }
    Some(index)
}

fn trim_end_except_newline(s: &str) -> &str {
    let trim_i = s.trim_end().len();
    if s[trim_i..].starts_with('\n') {
        &s[..trim_i + 1]
    } else {
        &s[..trim_i]
    }
}

// Remove whitespace intelligently in a comment.
fn remove_whitespace(comment: &str) -> &str {
    match comment.strip_prefix(" ") {
        Some(comment) => comment.strip_suffix(" ").unwrap_or(comment),
        None => match comment.strip_prefix("\n") {
            None => comment,
            Some(comment) => trim_end_except_newline(comment),
        },
    }
}

/// Return the position info for the comment after index. If there is no
/// comment, returns None. After calling this function, if it returns `Some(c)`
/// calling it again with index `c.end()` will allow parsing all the comment and
/// non-comment parts of the file.
pub fn next_comment_at<'a>(s: &'a str, index: usize) -> Result<Option<Comment<'a>>, String> {
    static MARK_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"^\S*").unwrap());
    // the ? here is where we early return if there is no comment
    let Some(start) = start_comment_at(s, index) else {
        return Ok(None);
    };
    let Some(end) = end_comment_at(s, start.end()) else {
        return Err("unterminated comment".to_string());
    };
    // just remove the comment markers, which are always (* and *) exactly
    let raw_inner = &s[start.end()..end - 2];
    let mark = MARK_RE.find(raw_inner).unwrap().as_str();
    let inner = remove_whitespace(&raw_inner[mark.len()..]);
    Ok(Some(Comment {
        span: (start.start(), end),
        mark,
        inner,
        raw_inner,
    }))
}

#[allow(clippy::bool_assert_comparison)]
#[cfg(test)]
mod tests {
    use super::*;

    fn last_sentence(s: &str) -> &str {
        let (i, j) = last_sentence_span(s).unwrap();
        &s[i..j]
    }

    #[test]
    fn test_last_sentence() {
        let s = r"
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
";
        assert_eq!(last_sentence(s), "Compute (next_weekday friday).");
    }

    #[test]
    fn test_last_sentence_from_require() {
        let s = r"From Coq Require Import Integer.ZArith.";
        assert_eq!(sentence_spans(s).len(), 1);
        assert_eq!(last_sentence(s), s);
    }

    #[test]
    fn test_last_sentence_module_path() {
        let s = r"Check foo.bar.";
        assert_eq!(next_sentence_period(s, 0), Some("Check foo.bar".len()));
        assert_eq!(sentence_spans(s).len(), 1);
        assert_eq!(last_sentence(s), s);
    }

    #[test]
    fn test_not_sentence() {
        let s = r"bar.

";
        assert_eq!(s.find('.'), Some(3));
        assert_eq!(NOT_SENTENCE.is_match(&s[3..]), false);
    }

    #[test]
    fn test_last_sentence_module_path_complex() {
        let s = r"Module foo := bar.

Check foo.bar.";
        // debugging to figure out NOT_SENTENCE wasn't anchored
        let sentence_len = "Module foo := bar".len();
        println!("{}", &s[sentence_len..]);
        assert!(next_comment_at(s, 0).unwrap().is_none());
        assert_eq!(s.find('.'), Some(sentence_len));
        assert_eq!(NOT_SENTENCE.is_match(&s[sentence_len..]), false);
        assert_eq!(next_sentence_period(s, 0), Some(sentence_len));
        assert_eq!(sentence_spans(s).len(), 2);
        assert_eq!(last_sentence(s), "Check foo.bar.");
    }

    #[test]
    fn test_last_sentence_comment() {
        let s = r"
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

(* this sentence should be ignored. *)
Compute (next_weekday friday).
";
        assert_eq!(
            last_sentence(s),
            "(* this sentence should be ignored. *)\nCompute (next_weekday friday)."
        );
    }

    #[test]
    fn test_comment() {
        let s = r"text (* next comment *) suffix";
        let c = next_comment_at(s, 0)
            .expect("comment does terminate")
            .unwrap();
        assert_eq!(c.start(), "text ".len());
        assert_eq!(c.end(), "text ".len() + "(* next comment *)".len());
        assert_eq!(c.inner, "next comment");
    }

    #[test]
    fn test_nested_comment() {
        let s = r"(* outer (* inner *) outer *)";
        assert_eq!(next_comment_at(s, 0).unwrap().unwrap().end(), s.len());
    }

    #[test]
    fn test_comment_mark() {
        let s = r"(** coqdoc *)";
        assert_eq!(next_comment_at(s, 0).unwrap().unwrap().inner, "coqdoc");
    }
}
