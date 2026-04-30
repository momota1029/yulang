use chasa::error::LatestSink;
use chasa::input::{In, Input as _, IsCut};
use im::HashSet;
use reborrow_generic::Reborrow as _;

use yulang_parser::context::{Env, State};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::op::standard_op_table;
use yulang_parser::pat::parse::parse_pattern;
use yulang_parser::scan::trivia::scan_trivia;
use yulang_parser::sink::{Event, EventSink, VecSink};

fn parse_pat(source: &str) -> Vec<String> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    let leading = i.run(scan_trivia).map(|t| t.info());
    let parsed = leading.and_then(|info| parse_pattern(info, i.rb()));
    if let Some(either::Either::Right(stop)) = parsed {
        i.env.state.sink.start(SyntaxKind::InvalidToken);
        i.env.state.sink.lex(&stop);
        i.env.state.sink.finish();
    }

    let (events, lexs) = std::mem::take(&mut i.env.state.sink).into_parts();
    dump(&events, &lexs)
}

fn dump(events: &[Event], lexs: &[yulang_parser::lex::Lex]) -> Vec<String> {
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
                result.push(format!("{}  {kind:?} {text:?}", "  ".repeat(indent - 1)));
            }
            Event::Finish => {
                indent -= 1;
                result.push(format!("{})", "  ".repeat(indent)));
            }
        }
    }
    result
}

#[test]
fn pat_paren_newline_separator() {
    let got = parse_pat("(A\nB)");
    let expected = vec![
        "(Pattern",
        "  (PatParenGroup",
        "    ParenL \"(\"",
        "    (Pattern",
        "      Ident \"A\"",
        "    )",
        "    (Separator",
        "    )",
        "    (Pattern",
        "      Ident \"B\"",
        "    )",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_call_newline_separator() {
    let got = parse_pat("f(A\nB)");
    let expected = vec![
        "(Pattern",
        "  Ident \"f\"",
        "  (ApplyC",
        "    ParenL \"(\"",
        "    (Pattern",
        "      Ident \"A\"",
        "    )",
        "    (Separator",
        "    )",
        "    (Pattern",
        "      Ident \"B\"",
        "    )",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_record_newline_separator() {
    let got = parse_pat("{a\nb}");
    let expected = vec![
        "(Pattern",
        "  (PatRecord",
        "    BraceL \"{\"",
        "    (PatField",
        "      Ident \"a\"",
        "    )",
        "    (Separator",
        "    )",
        "    (PatField",
        "      Ident \"b\"",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_record_head_spread() {
    let got = parse_pat("{ ..rest, width = 1 }");
    let expected = vec![
        "(Pattern",
        "  (PatRecord",
        "    BraceL \"{\"",
        "    (PatSpread",
        "      DotDot \"..\"",
        "      (Pattern",
        "        Ident \"rest\"",
        "      )",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (PatField",
        "      Ident \"width\"",
        "      Equal \"=\"",
        "      (Expr",
        "        Number \"1\"",
        "      )",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_record_tail_spread() {
    let got = parse_pat("{ width = 1, ..rest }");
    let expected = vec![
        "(Pattern",
        "  (PatRecord",
        "    BraceL \"{\"",
        "    (PatField",
        "      Ident \"width\"",
        "      Equal \"=\"",
        "      (Expr",
        "        Number \"1\"",
        "      )",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (PatSpread",
        "      DotDot \"..\"",
        "      (Pattern",
        "        Ident \"rest\"",
        "      )",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_list_prefix_spread_suffix() {
    let got = parse_pat("[head, ..middle, tail]");
    let expected = vec![
        "(Pattern",
        "  (PatList",
        "    BracketL \"[\"",
        "    (Pattern",
        "      Ident \"head\"",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (PatSpread",
        "      DotDot \"..\"",
        "      (Pattern",
        "        Ident \"middle\"",
        "      )",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (Pattern",
        "      Ident \"tail\"",
        "    )",
        "    BracketR \"]\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_record_field_with_named_pattern() {
    let got = parse_pat("{ width: local_width }");
    let expected = vec![
        "(Pattern",
        "  (PatRecord",
        "    BraceL \"{\"",
        "    (PatField",
        "      Ident \"width\"",
        "      Colon \":\"",
        "      (Pattern",
        "        Ident \"local_width\"",
        "      )",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_record_field_with_named_pattern_and_default_expr() {
    let got = parse_pat("{ width: local_width = 1 }");
    let expected = vec![
        "(Pattern",
        "  (PatRecord",
        "    BraceL \"{\"",
        "    (PatField",
        "      Ident \"width\"",
        "      Colon \":\"",
        "      (Pattern",
        "        Ident \"local_width\"",
        "      )",
        "      Equal \"=\"",
        "      (Expr",
        "        Number \"1\"",
        "      )",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_or_as_type_ann() {
    let got = parse_pat("A | B as c: Int");
    let expected = vec![
        "(Pattern",
        "  Ident \"A\"",
        "  (PatOr",
        "    Pipe \"|\"",
        "    (Pattern",
        "      Ident \"B\"",
        "      (PatAs",
        "        As \"as\"",
        "        Ident \"c\"",
        "      )",
        "      (TypeAnn",
        "        Colon \":\"",
        "        (TypeExpr",
        "          Ident \"Int\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_unknown_char_root_is_invalid() {
    let got = parse_pat("@");
    let expected = vec!["(InvalidToken", "  Unknown \"@\"", ")"];
    assert_eq!(got, expected);
}

#[test]
fn pat_sigil_ident() {
    let got = parse_pat("$foo");
    let expected = vec!["(Pattern", "  SigilIdent \"$foo\"", ")"];
    assert_eq!(got, expected);
}

#[test]
fn pat_sigil_ident_underscore() {
    let got = parse_pat("_bar");
    let expected = vec!["(Pattern", "  SigilIdent \"_bar\"", ")"];
    assert_eq!(got, expected);
}

#[test]
fn pat_path_sep() {
    let got = parse_pat("Foo::Bar");
    let expected = vec![
        "(Pattern",
        "  Ident \"Foo\"",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"Bar\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_number_literal() {
    let got = parse_pat("42");
    let expected = vec!["(Pattern", "  Number \"42\"", ")"];
    assert_eq!(got, expected);
}

#[test]
fn pat_symbol_after_space_is_ml_head() {
    let got = parse_pat(" :foo y z");
    let expected = vec![
        "(Pattern",
        "  Symbol \":foo\"",
        "  (ApplyML",
        "    (Pattern",
        "      Ident \"y\"",
        "    )",
        "  )",
        "  (ApplyML",
        "    (Pattern",
        "      Ident \"z\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_symbol_at_paren_pattern_start() {
    let got = parse_pat("(:foo y)");
    let expected = vec![
        "(Pattern",
        "  (PatParenGroup",
        "    ParenL \"(\"",
        "    (Pattern",
        "      Symbol \":foo\"",
        "      (ApplyML",
        "        (Pattern",
        "          Ident \"y\"",
        "        )",
        "      )",
        "    )",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_or_simple() {
    let got = parse_pat("A | B");
    let expected = vec![
        "(Pattern",
        "  Ident \"A\"",
        "  (PatOr",
        "    Pipe \"|\"",
        "    (Pattern",
        "      Ident \"B\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_as_simple() {
    let got = parse_pat("A as x");
    let expected = vec![
        "(Pattern",
        "  Ident \"A\"",
        "  (PatAs",
        "    As \"as\"",
        "    Ident \"x\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_record_field_with_type_ann() {
    let got = parse_pat("{a: Int, b: String}");
    let expected = vec![
        "(Pattern",
        "  (PatRecord",
        "    BraceL \"{\"",
        "    (PatField",
        "      Ident \"a\"",
        "      Colon \":\"",
        "      (Pattern",
        "        Ident \"Int\"",
        "      )",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (PatField",
        "      Ident \"b\"",
        "      Colon \":\"",
        "      (Pattern",
        "        Ident \"String\"",
        "      )",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_record_field_with_default_expr() {
    let got = parse_pat("{width = 1, height = 1}");
    let expected = vec![
        "(Pattern",
        "  (PatRecord",
        "    BraceL \"{\"",
        "    (PatField",
        "      Ident \"width\"",
        "      Equal \"=\"",
        "      (Expr",
        "        Number \"1\"",
        "      )",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (PatField",
        "      Ident \"height\"",
        "      Equal \"=\"",
        "      (Expr",
        "        Number \"1\"",
        "      )",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_string_lit_simple() {
    // パターン内の "" はルールリテラルとして扱われる（~"" と同じ）
    let got = parse_pat("\"hello\"");
    let expected = vec![
        "(Pattern",
        "  (RuleLit",
        "    StringStart \"\\\"\"",
        "    RuleLitText \"hello\"",
        "    RuleLitEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_string_lit_lazy_capture() {
    // "hello, :world" — :world は lazy capture として認識される
    let got = parse_pat("\"hello, :world\"");
    let expected = vec![
        "(Pattern",
        "  (RuleLit",
        "    StringStart \"\\\"\"",
        "    RuleLitText \"hello, \"",
        "    (RuleLazyCapture",
        "      RuleLitColon \":\"",
        "      RuleLitText \"world\"",
        "    )",
        "    RuleLitEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_string_lit_heredoc() {
    let got = parse_pat("\"\"\"hello\"\"\"");
    let expected = vec![
        "(Pattern",
        "  (StringLit",
        "    StringStart \"\\\"\\\"\\\"\"",
        "    StringText \"hello\"",
        "    StringEnd \"\\\"\\\"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_type_ann_simple() {
    let got = parse_pat("x: Int");
    let expected = vec![
        "(Pattern",
        "  Ident \"x\"",
        "  (TypeAnn",
        "    Colon \":\"",
        "    (TypeExpr",
        "      Ident \"Int\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_symbol_head_with_ml_argument() {
    let got = parse_pat(":leaf x");
    let expected = vec![
        "(Pattern",
        "  Symbol \":leaf\"",
        "  (ApplyML",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_empty_paren_group() {
    let got = parse_pat("()");
    let expected = vec![
        "(Pattern",
        "  (PatParenGroup",
        "    ParenL \"(\"",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn pat_rule_expr_simple() {
    // rule { "hello" } をパターンとして使う
    let got = parse_pat("rule { \"hello\" }");
    let expected = vec![
        "(Pattern",
        "  (RuleExpr",
        "    Rule \"rule\"",
        "    (BraceGroup",
        "      BraceL \"{\"",
        "      (Expr",
        "        (StringLit",
        "          StringStart \"\\\"\"",
        "          StringText \"hello\"",
        "          StringEnd \"\\\"\"",
        "        )",
        "      )",
        "      BraceR \"}\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}
