use chasa::error::LatestSink;
use chasa::input::{In, Input as _, IsCut};
use im::HashSet;

use yulang_parser::context::{Env, State};
use yulang_parser::lex::{TriviaInfo, TriviaKind};
use yulang_parser::op::standard_op_table;
use yulang_parser::scan::trivia::scan_trivia;
use yulang_parser::sink::VecSink;

fn scan_parts(source: &str) -> Vec<(TriviaKind, String)> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);
    let trivia = i.run(scan_trivia).unwrap();
    trivia
        .parts()
        .iter()
        .map(|p| (p.kind, p.text.to_string()))
        .collect()
}

fn scan_info(source: &str) -> TriviaInfo {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);
    i.run(scan_trivia).unwrap().info()
}

// ── TriviaInfo ───────────────────────────────────────────────────────────────

#[test]
fn trivia_info_no_trivia() {
    // non-trivia leading char → nothing consumed
    assert_eq!(scan_info("x"), TriviaInfo::None);
}

#[test]
fn trivia_info_space_only() {
    assert_eq!(scan_info("   "), TriviaInfo::Space);
}

#[test]
fn trivia_info_line_comment_no_newline() {
    // comment without trailing newline is treated as Space (no line break)
    assert_eq!(scan_info("// foo"), TriviaInfo::Space);
}

#[test]
fn trivia_info_newline() {
    assert_eq!(
        scan_info("\n"),
        TriviaInfo::Newline {
            indent: 0,
            quote_level: 0,
            blank_line: false
        }
    );
}

#[test]
fn trivia_info_newline_indent() {
    assert_eq!(
        scan_info("\n    "),
        TriviaInfo::Newline {
            indent: 4,
            quote_level: 0,
            blank_line: false
        }
    );
}

#[test]
fn trivia_info_blank_line() {
    assert_eq!(
        scan_info("\n\n"),
        TriviaInfo::Newline {
            indent: 0,
            quote_level: 0,
            blank_line: true
        }
    );
}

#[test]
fn trivia_info_line_comment_then_newline() {
    assert_eq!(
        scan_info("// foo\n  "),
        TriviaInfo::Newline {
            indent: 2,
            quote_level: 0,
            blank_line: false
        }
    );
}

#[test]
fn trivia_info_block_comment_no_newline() {
    // block comment without newlines is treated as Space
    assert_eq!(scan_info("/* comment */"), TriviaInfo::Space);
}

// ── parts: whitespace ────────────────────────────────────────────────────────

#[test]
fn trivia_parts_no_trivia() {
    let got = scan_parts("x");
    assert_eq!(got, vec![]);
}

#[test]
fn trivia_parts_spaces() {
    let got = scan_parts("   ");
    assert_eq!(got, vec![(TriviaKind::Space, "   ".into())]);
}

#[test]
fn trivia_parts_newline_indent() {
    let got = scan_parts("\n    ");
    assert_eq!(got, vec![(TriviaKind::Space, "\n    ".into())]);
}

// ── parts: line comment ──────────────────────────────────────────────────────

#[test]
fn trivia_parts_line_comment() {
    let got = scan_parts("// hello");
    assert_eq!(got, vec![(TriviaKind::LineComment, "// hello".into())]);
}

#[test]
fn trivia_parts_line_comment_then_newline() {
    let got = scan_parts("// hello\n  ");
    assert_eq!(
        got,
        vec![
            (TriviaKind::LineComment, "// hello".into()),
            (TriviaKind::Space, "\n  ".into()),
        ]
    );
}

// ── parts: block comment ─────────────────────────────────────────────────────

#[test]
fn trivia_parts_block_comment_empty() {
    // /**/ — no body
    let got = scan_parts("/**/");
    assert_eq!(
        got,
        vec![
            (TriviaKind::BlockCommentStart, "/*".into()),
            (TriviaKind::BlockCommentEnd, "*/".into()),
        ]
    );
}

#[test]
fn trivia_parts_block_comment_no_spaces() {
    // /*x*/ — body without surrounding spaces
    let got = scan_parts("/*x*/");
    assert_eq!(
        got,
        vec![
            (TriviaKind::BlockCommentStart, "/*".into()),
            (TriviaKind::BlockCommentText, "x".into()),
            (TriviaKind::BlockCommentEnd, "*/".into()),
        ]
    );
}

#[test]
fn trivia_parts_block_comment_with_spaces() {
    // /* x */ — spaces inside are emitted as separate Space parts
    let got = scan_parts("/* x */");
    assert_eq!(
        got,
        vec![
            (TriviaKind::BlockCommentStart, "/*".into()),
            (TriviaKind::Space, " ".into()),
            (TriviaKind::BlockCommentText, "x".into()),
            (TriviaKind::Space, " ".into()),
            (TriviaKind::BlockCommentEnd, "*/".into()),
        ]
    );
}

#[test]
fn trivia_parts_block_comment_then_space() {
    // trailing space after comment is a separate Space part
    let got = scan_parts("/*x*/ ");
    assert_eq!(
        got,
        vec![
            (TriviaKind::BlockCommentStart, "/*".into()),
            (TriviaKind::BlockCommentText, "x".into()),
            (TriviaKind::BlockCommentEnd, "*/".into()),
            (TriviaKind::Space, " ".into()),
        ]
    );
}

#[test]
fn trivia_parts_block_comment_slash_star_slash() {
    // /* /*/ */ — `/*/` は `*/` をスキップするのでネストしない単一コメント
    let got = scan_parts("/* /*/ */");
    assert_eq!(
        got,
        vec![
            (TriviaKind::BlockCommentStart, "/*".into()),
            (TriviaKind::Space, " ".into()),
            (TriviaKind::BlockCommentText, "/*/".into()),
            (TriviaKind::Space, " ".into()),
            (TriviaKind::BlockCommentEnd, "*/".into()),
        ]
    );
}

#[test]
fn trivia_parts_block_comment_nested() {
    // /* /* inner */ outer */ — two levels of nesting
    let got = scan_parts("/* /* inner */ outer */");
    assert_eq!(
        got,
        vec![
            (TriviaKind::BlockCommentStart, "/*".into()),
            (TriviaKind::Space, " ".into()),
            (TriviaKind::BlockCommentStart, "/*".into()),
            (TriviaKind::Space, " ".into()),
            (TriviaKind::BlockCommentText, "inner".into()),
            (TriviaKind::Space, " ".into()),
            (TriviaKind::BlockCommentEnd, "*/".into()),
            (TriviaKind::Space, " ".into()),
            (TriviaKind::BlockCommentText, "outer".into()),
            (TriviaKind::Space, " ".into()),
            (TriviaKind::BlockCommentEnd, "*/".into()),
        ]
    );
}
