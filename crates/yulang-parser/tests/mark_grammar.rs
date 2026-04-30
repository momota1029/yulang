use chasa::error::LatestSink;
use chasa::input::{In, Input as _, IsCut};
use im::HashSet;
use reborrow_generic::Reborrow as _;

use yulang_parser::context::{Env, State};
use yulang_parser::lex::Lex;
use yulang_parser::mark::parse::{parse_doc_body_pub, parse_doc_line};
use yulang_parser::mark::scan::scan_mark;
use yulang_parser::op::standard_op_table;
use yulang_parser::sink::{Event, VecSink};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn dump(events: &[Event], lexs: &[Lex]) -> Vec<String> {
    let mut result = Vec::new();
    let mut lex_iter = lexs.iter();
    let mut indent = 0usize;
    for event in events {
        match event {
            Event::Start(kind) => {
                result.push(format!("{}({kind:?}", "  ".repeat(indent)));
                indent += 1;
            }
            Event::Lex(kind) => {
                let text = lex_iter.next().map(|t| t.text.as_ref()).unwrap_or("");
                if indent == 0 {
                    result.push(format!("{kind:?} {text:?}"));
                } else {
                    result.push(format!("{}  {kind:?} {text:?}", "  ".repeat(indent - 1)));
                }
            }
            Event::Finish => {
                indent -= 1;
                result.push(format!("{})", "  ".repeat(indent)));
            }
        }
    }
    result
}

fn make_env(state: &mut State<VecSink>) -> Env<'_, VecSink> {
    Env::new(state, standard_op_table(), 0, HashSet::new())
}

/// Run `parse_doc_body_pub` and return the dumped events.
fn doc_body(source: &str) -> Vec<String> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = make_env(&mut state);
    let mut i = base_in.set_env(env);
    let _ = parse_doc_body_pub(i.rb());
    let (events, lexs) = std::mem::take(&mut i.env.state.sink).into_parts();
    dump(&events, &lexs)
}

/// Run `parse_doc_line` (inline mode) and return the dumped events inside YmDoc.
fn doc_line(source: &str) -> Vec<String> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = make_env(&mut state);
    let mut i = base_in.set_env(env);
    parse_doc_line(i.rb());
    let (events, lexs) = std::mem::take(&mut i.env.state.sink).into_parts();
    dump(&events, &lexs)
}

/// Run `scan_mark` once and return a human-readable summary.
fn scan_one(source: &str) -> Vec<String> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = make_env(&mut state);
    let mut i = base_in.set_env(env);

    let mark = scan_mark(i.rb()).expect("scan_mark returned None");
    let mut lines = vec![format!("text {:?}", mark.text.as_ref())];

    // trivia parts
    if mark.trivia.parts().is_empty() {
        lines.push(String::from("trivia []"));
    } else {
        for part in mark.trivia.parts() {
            lines.push(format!("trivia {:?} {:?}", part.kind, part.text.as_ref()));
        }
    }

    // nud lex
    match &mark.nud.lex {
        Some(lex) => lines.push(format!("nud {:?} {:?}", lex.kind, lex.text.as_ref())),
        None => lines.push(String::from("nud None")),
    }
    lines.push(format!("nud tag {:?}", mark.nud.tag));
    lines
}

// ---------------------------------------------------------------------------
// scan tests
// ---------------------------------------------------------------------------

#[test]
fn scan_close_bracket_boundary() {
    let got = scan_one("]");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud BracketR \"]\"",
        "nud tag Inline(CloseBracket)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_close_brace_boundary() {
    let got = scan_one("}");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud BraceR \"}\"",
        "nud tag Inline(CloseBrace)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_backslash_boundary() {
    let got = scan_one("\\cmd");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud YmBackslash \"\\\\\"",
        "nud tag Inline(Backslash)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_section_close_boundary() {
    let got = scan_one("#.");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud YmHashDotSigil \"#.\"",
        "nud tag Inline(SectionClose)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_bang_boundary() {
    let got = scan_one("![");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud YmBang \"!\"",
        "nud tag Inline(Bang)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_star_emphasis_boundary() {
    let got = scan_one("*em*");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud YmStarSigil \"*\"",
        "nud tag Inline(Emphasis)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_double_star_strong_boundary() {
    let got = scan_one("**strong**");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud YmStrongSigil \"**\"",
        "nud tag Inline(Strong)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_plain_text_before_emphasis() {
    let got = scan_one("hello*world");
    let expected = vec![
        "text \"hello\"",
        "trivia []",
        "nud YmStarSigil \"*\"",
        "nud tag Inline(Emphasis)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_text_with_newline_leading_to_heading() {
    let got = scan_one("foo\n# head\n");
    let expected = vec![
        "text \"foo\"",
        "trivia Space \"\\n\"",
        "nud YmHashSigil \"# \"",
        "nud tag Block(Heading)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_text_with_newline_leading_to_list() {
    let got = scan_one("foo\n- item\n");
    let expected = vec![
        "text \"foo\"",
        "trivia Space \"\\n\"",
        "nud YmListDashSigil \"- \"",
        "nud tag Block(ListMinus)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_heading_at_start() {
    let got = scan_one("# head\n");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud YmHashSigil \"# \"",
        "nud tag Block(Heading)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_fence_at_start() {
    let got = scan_one("```rust\n");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud YmFenceSigil \"```\"",
        "nud tag Block(Fence)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_blockquote_at_start() {
    let got = scan_one("> foo\n");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud YmChevronPrefixSigil \"> \"",
        "nud tag Block(BlockQuote)",
    ];
    assert_eq!(got, expected);
}

#[test]
fn scan_list_at_start() {
    let got = scan_one("- item\n");
    let expected = vec![
        "text \"\"",
        "trivia []",
        "nud YmListDashSigil \"- \"",
        "nud tag Block(ListMinus)",
    ];
    assert_eq!(got, expected);
}

// ---------------------------------------------------------------------------
// doc_body: block mode parse tests
// ---------------------------------------------------------------------------

#[test]
fn block_heading_only() {
    let got = doc_body("# head\n");
    let expected = vec![
        "(YmHeading",
        "  YmHashSigil \"# \"",
        "  YmText \"head\"",
        "  YmNewline \"\\n\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_list_simple() {
    let got = doc_body("- item\n");
    let expected = vec![
        "(YmList",
        "  (YmListItem",
        "    YmListDashSigil \"- \"",
        "    (YmListItemBody",
        "      YmText \"item\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_fence_plain() {
    let got = doc_body("```rust\nlet x = 1;\n```\n");
    let expected = vec![
        "(YmCodeFence",
        "  YmFenceSigil \"```\"",
        "  (YmCodeFenceInfo",
        "    YmText \"rust\"",
        "  )",
        "  YmNewline \"\\n\"",
        "  (YmCodeFenceText",
        "    YmText \"let x = 1;\"",
        "    Space \"\\n\"",
        "  )",
        "  YmFenceSigil \"```\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_fence_no_info() {
    let got = doc_body("```\ncode\n```\n");
    // Empty YmCodeFenceInfo is always created (even if empty)
    let expected = vec![
        "(YmCodeFence",
        "  YmFenceSigil \"```\"",
        "  (YmCodeFenceInfo",
        "  )",
        "  YmNewline \"\\n\"",
        "  (YmCodeFenceText",
        "    YmText \"code\"",
        "    Space \"\\n\"",
        "  )",
        "  YmFenceSigil \"```\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_heading_then_paragraph_text() {
    let got = doc_body("# head\nnext\n");
    let expected = vec![
        "(YmHeading",
        "  YmHashSigil \"# \"",
        "  YmText \"head\"",
        "  YmNewline \"\\n\"",
        ")",
        "(YmParagraph",
        "  YmText \"next\"",
        "  Space \"\\n\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_list_then_text() {
    let got = doc_body("- item\nnext\n");
    let expected = vec![
        "(YmList",
        "  (YmListItem",
        "    YmListDashSigil \"- \"",
        "    (YmListItemBody",
        "      YmText \"item\"",
        "    )",
        "  )",
        ")",
        "(YmParagraph",
        "  YmText \"next\"",
        "  Space \"\\n\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_blockquote_simple() {
    let got = doc_body("> foo\n");
    let expected = vec![
        "(YmQuoteBlock",
        "  YmChevronPrefixSigil \"> \"",
        "  (YmParagraph",
        "    YmText \"foo\"",
        "    Space \"\\n\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_blockquote_then_paragraph() {
    let got = doc_body("> foo\nbar\n");
    let expected = vec![
        "(YmQuoteBlock",
        "  YmChevronPrefixSigil \"> \"",
        "  (YmParagraph",
        "    YmText \"foo\"",
        "    Space \"\\n\"",
        "  )",
        ")",
        "(YmParagraph",
        "  YmText \"bar\"",
        "  Space \"\\n\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_blank_line() {
    let got = doc_body("# a\n\n# b\n");
    let expected = vec![
        "(YmHeading",
        "  YmHashSigil \"# \"",
        "  YmText \"a\"",
        "  YmNewline \"\\n\"",
        ")",
        "(YmBlankLine",
        ")",
        "(YmHeading",
        "  YmHashSigil \"# \"",
        "  YmText \"b\"",
        "  YmNewline \"\\n\"",
        ")",
    ];
    assert_eq!(got, expected);
}

// ---------------------------------------------------------------------------
// doc_line: inline mode parse tests
// ---------------------------------------------------------------------------

#[test]
fn inline_plain_text() {
    let got = doc_line("hello");
    let expected = vec!["(YmDoc", "  YmText \"hello\"", ")"];
    assert_eq!(got, expected);
}

#[test]
fn inline_text_with_emphasis() {
    let got = doc_line("*hello*");
    // emphasis wraps content
    let expected = vec![
        "(YmDoc",
        "  (YmEmphasis",
        "    YmStarSigil \"*\"",
        "    YmText \"hello\"",
        "    YmStarSigil \"*\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn inline_text_with_strong() {
    let got = doc_line("**bold**");
    let expected = vec![
        "(YmDoc",
        "  (YmStrong",
        "    YmStrongSigil \"**\"",
        "    YmText \"bold\"",
        "    YmStrongSigil \"**\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn inline_multiline_text_continuation() {
    // inline mode (doc_line) は改行で停止する
    let got = doc_line("hello\nworld");
    let expected = vec!["(YmDoc", "  YmText \"hello\"", ")"];
    assert_eq!(got, expected);
}

// ---------------------------------------------------------------------------
// Unimplemented features — kept as #[ignore] stubs
// ---------------------------------------------------------------------------

#[test]
fn inline_bracket_expr() {
    let got = doc_line("[hello]");
    let expected = vec![
        "(YmDoc",
        "  (YmInlineExpr",
        "    BracketL \"[\"",
        "    YmText \"hello\"",
        "    BracketR \"]\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_backslash_command() {
    let got = doc_body("\\cmd\n");
    let expected = vec![
        "(YmCommand",
        "  YmBackslash \"\\\\\"",
        "  YmIdent \"cmd\"",
        "  YmNewline \"\\n\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_section_close() {
    let got = doc_body("#.\n");
    let expected = vec![
        "(YmSectionClose",
        "  YmHashDotSigil \"#.\"",
        "  YmNewline \"\\n\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn inline_image() {
    let got = doc_line("![alt]");
    let expected = vec![
        "(YmDoc",
        "  (YmInlineExpr",
        "    YmBang \"!\"",
        "    YmLBracket \"[\"",
        "    YmText \"alt\"",
        "    BracketR \"]\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_fence_yulang() {
    let got = doc_body("```yulang\nmy x = 1\n```\n");
    let expected = vec![
        "(YmCodeFence",
        "  YmFenceSigil \"```\"",
        "  (YmCodeFenceInfo",
        "    YmText \"yulang\"",
        "  )",
        "  YmNewline \"\\n\"",
        "  (Binding",
        "    (BindingHeader",
        "      My \"my\"",
        "      (Pattern",
        "        Ident \"x\"",
        "      )",
        "      Equal \"=\"",
        "    )",
        "    (BindingBody",
        "      (Expr",
        "        Number \"1\"",
        "      )",
        "    )",
        "  )",
        "  YmFenceSigil \"```\"",
        ")",
    ];
    assert_eq!(got, expected);
}

// ---------------------------------------------------------------------------
// Mixed blockquote / fence tests
// ---------------------------------------------------------------------------

#[test]
fn block_fence_with_quote_in_body() {
    // Raw fence body: `>` is treated as literal text, not a blockquote
    let got = doc_body("```\n> not a quote\n```\n");
    let expected = vec![
        "(YmCodeFence",
        "  YmFenceSigil \"```\"",
        "  (YmCodeFenceInfo",
        "  )",
        "  YmNewline \"\\n\"",
        "  (YmCodeFenceText",
        "    YmChevronPrefixSigil \"> \"",
        "    YmText \"not a quote\"",
        "    Space \"\\n\"",
        "  )",
        "  YmFenceSigil \"```\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_quote_then_fence() {
    let got = doc_body("> foo\n```rust\ncode\n```\n");
    let expected = vec![
        "(YmQuoteBlock",
        "  YmChevronPrefixSigil \"> \"",
        "  (YmParagraph",
        "    YmText \"foo\"",
        "    Space \"\\n\"",
        "  )",
        ")",
        "(YmCodeFence",
        "  YmFenceSigil \"```\"",
        "  (YmCodeFenceInfo",
        "    YmText \"rust\"",
        "  )",
        "  YmNewline \"\\n\"",
        "  (YmCodeFenceText",
        "    YmText \"code\"",
        "    Space \"\\n\"",
        "  )",
        "  YmFenceSigil \"```\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_nested_blockquote() {
    let got = doc_body("> > deep\n> outer\n");
    let expected = vec![
        "(YmQuoteBlock",
        "  YmChevronPrefixSigil \"> \"",
        "  (YmQuoteBlock",
        "    YmChevronPrefixSigil \"> \"",
        "    (YmParagraph",
        "      YmText \"deep\"",
        "      QuotePrefix \"\\n> \"",
        "    )",
        "  )",
        "  (YmParagraph",
        "    YmText \"outer\"",
        "    Space \"\\n\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_quote_fence_per_line() {
    // `> ` continuation trivia makes "> " lines part of the same blockquote,
    // so the fence open/close ARE matched within the single YmQuoteBlock.
    let got = doc_body("> ```rust\n> code\n> ```\n");
    let expected = vec![
        "(YmQuoteBlock",
        "  YmChevronPrefixSigil \"> \"",
        "  (YmCodeFence",
        "    YmFenceSigil \"```\"",
        "    (YmCodeFenceInfo",
        "      YmText \"rust\"",
        "    )",
        "    QuotePrefix \"\\n> \"",
        "    (YmCodeFenceText",
        "      YmText \"code\"",
        "      QuotePrefix \"\\n> \"",
        "    )",
        "    YmFenceSigil \"```\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_quote_empty_line_within() {
    // `>` alone (without space) acts as a blank line within the blockquote.
    // Result: ONE YmQuoteBlock with YmBlankLine separating the two paragraphs.
    let got = doc_body("> foo\n>\n> bar\n");
    let expected = vec![
        "(YmQuoteBlock",
        "  YmChevronPrefixSigil \"> \"",
        "  (YmParagraph",
        "    YmText \"foo\"",
        "    QuotePrefix \"\\n>\\n> \"",
        "  )",
        "  (YmBlankLine",
        "  )",
        "  (YmParagraph",
        "    YmText \"bar\"",
        "    Space \"\\n\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_quote_blank_line_between_paragraphs() {
    // A blank line (no `>`) between `> ` lines ends the blockquote.
    // Result: TWO separate YmQuoteBlock nodes.
    let got = doc_body("> foo\n\n> bar\n");
    let expected = vec![
        "(YmQuoteBlock",
        "  YmChevronPrefixSigil \"> \"",
        "  (YmParagraph",
        "    YmText \"foo\"",
        "    Space \"\\n\\n\"",
        "  )",
        ")",
        "(YmQuoteBlock",
        "  YmChevronPrefixSigil \"> \"",
        "  (YmParagraph",
        "    YmText \"bar\"",
        "    Space \"\\n\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn block_quote_no_space_sigil() {
    // `>` without a trailing space should still open a blockquote.
    let got = doc_body(">foo\n");
    let expected = vec![
        "(YmQuoteBlock",
        "  YmChevronPrefixSigil \">\"",
        "  (YmParagraph",
        "    YmText \"foo\"",
        "    Space \"\\n\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn debug_scan_mark_at_fence_body() {
    // Directly test scan_mark at what should be the fence body start
    let got = scan_one("let x = 1;\n```\n");
    assert_eq!(got[0], "text \"let x = 1;\"");
    assert_eq!(got[1], "trivia Space \"\\n\"");
    assert_eq!(got[3], "nud tag Block(Fence)");
}
