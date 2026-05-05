use chasa::error::LatestSink;
use chasa::input::{In, Input as _, IsCut};
use im::HashSet;
use reborrow_generic::Reborrow as _;

use yulang_parser::context::{Env, State};
use yulang_parser::expr::parse_expr;
use yulang_parser::lex::SyntaxKind;
use yulang_parser::op::standard_op_table;
use yulang_parser::scan::trivia::scan_trivia;
use yulang_parser::sink::{Event, EventSink, VecSink};

fn parse_expression_result(source: &str) -> Option<Vec<String>> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    let leading = i.run(scan_trivia).map(|t| t.info());
    let parsed = leading.and_then(|info| parse_expr(info, i.rb()));
    let ok = parsed.is_some();
    if let Some(either::Either::Right(stop)) = parsed {
        i.env.state.sink.start(SyntaxKind::InvalidToken);
        i.env.state.sink.lex(&stop);
        i.env.state.sink.finish();
    }

    let (events, lexs) = std::mem::take(&mut i.env.state.sink).into_parts();
    ok.then(|| dump(&events, &lexs))
}

fn parse_expression(source: &str) -> Vec<String> {
    parse_expression_result(source).expect("expression")
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
fn expr_prefix_not() {
    let got = parse_expression("not x");
    let expected = vec![
        "(Expr",
        "  (PrefixNode",
        "    Prefix \"not\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_loop_control_nullfix_last() {
    let got = parse_expression("last");
    let expected = vec!["(Expr", "  Nullfix \"last\"", ")"];
    assert_eq!(got, expected);
}

#[test]
fn expr_loop_control_call_remains_ident_call() {
    let got = parse_expression("last()");
    let expected = vec![
        "(Expr",
        "  Ident \"last\"",
        "  (ApplyC",
        "    ParenL \"(\"",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_loop_control_value_arg_remains_ident_apply() {
    let got = parse_expression("last xs");
    let expected = vec![
        "(Expr",
        "  Ident \"last\"",
        "  (ApplyML",
        "    (Expr",
        "      Ident \"xs\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_loop_control_qualified_name_remains_path() {
    let got = parse_expression("last::sub");
    let expected = vec![
        "(Expr",
        "  Ident \"last\"",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"sub\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_loop_control_label_form_is_nullfix_apply() {
    let got = parse_expression("last 'outer");
    let expected = vec![
        "(Expr",
        "  Nullfix \"last\"",
        "  (ApplyML",
        "    (Expr",
        "      SigilIdent \"'outer\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_return_prefix() {
    let got = parse_expression("return x");
    let expected = vec![
        "(Expr",
        "  (PrefixNode",
        "    Prefix \"return\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_return_call_remains_ident_call() {
    let got = parse_expression("return()");
    let expected = vec![
        "(Expr",
        "  Ident \"return\"",
        "  (ApplyC",
        "    ParenL \"(\"",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_return_qualified_name_remains_path() {
    let got = parse_expression("sub::return");
    let expected = vec![
        "(Expr",
        "  Ident \"sub\"",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"return\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_prefix_then_infix() {
    // `not x and y` → PrefixNode[not, x] then InfixNode[and, y]
    // not(bp=70) > and(lbp=20), so `and` stops rhs parse and continues outer tail
    let got = parse_expression("not x and y");
    let expected = vec![
        "(Expr",
        "  (PrefixNode",
        "    Prefix \"not\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        "  (InfixNode",
        "    Infix \"and\"",
        "    (Expr",
        "      Ident \"y\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_prefix_minus() {
    let got = parse_expression("-x");
    let expected = vec![
        "(Expr",
        "  (PrefixNode",
        "    Prefix \"-\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_suffix_dotdot() {
    // EOF は post_ws=true 扱いなので `x..` も Suffix として判定される
    let got = parse_expression("x..");
    let expected = vec![
        "(Expr",
        "  Ident \"x\"",
        "  (SuffixNode",
        "    Suffix \"..\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_bracket_group() {
    let got = parse_expression("[1, 2]");
    let expected = vec![
        "(Expr",
        "  (Bracket",
        "    BracketL \"[\"",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (Expr",
        "      Number \"2\"",
        "    )",
        "    BracketR \"]\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_bracket_group_accepts_newline_separated_items() {
    let got = parse_expression("[\n    1\n    2\n    3\n    4\n]");
    let expected = vec![
        "(Expr",
        "  (Bracket",
        "    BracketL \"[\"",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "    (Separator",
        "    )",
        "    (Expr",
        "      Number \"2\"",
        "    )",
        "    (Separator",
        "    )",
        "    (Expr",
        "      Number \"3\"",
        "    )",
        "    (Separator",
        "    )",
        "    (Expr",
        "      Number \"4\"",
        "    )",
        "    (Separator",
        "    )",
        "    BracketR \"]\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_bracket_group_with_spread() {
    let got = parse_expression("[1, ..xs, 3]");
    let expected = vec![
        "(Expr",
        "  (Bracket",
        "    BracketL \"[\"",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (ExprSpread",
        "      DotDot \"..\"",
        "      (Expr",
        "        Ident \"xs\"",
        "      )",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (Expr",
        "      Number \"3\"",
        "    )",
        "    BracketR \"]\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_quoted_mark_inline() {
    let got = parse_expression("'[hello]");
    let expected = vec![
        "(Expr",
        "  (MarkExpr",
        "    (MarkInlineBody",
        "      MarkLitStart \"'[\"",
        "      (YmDoc",
        "        YmText \"hello\"",
        "      )",
        "      MarkLitEnd \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_ident_named_mark_is_plain_ident() {
    let got = parse_expression("mark");
    let expected = vec!["(Expr", "  Ident \"mark\"", ")"];
    assert_eq!(got, expected);
}

#[test]
fn expr_mark_call_is_plain_ml_apply() {
    let got = parse_expression("mark x");
    let expected = vec![
        "(Expr",
        "  Ident \"mark\"",
        "  (ApplyML",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_string_lit_after_space_is_ml_argument() {
    let got = parse_expression("f \"ok\"");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyML",
        "    (Expr",
        "      (StringLit",
        "        StringStart \"\\\"\"",
        "        StringText \"ok\"",
        "        StringEnd \"\\\"\"",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_as_type_ann() {
    let got = parse_expression("x as int");
    let expected = vec![
        "(Expr",
        "  Ident \"x\"",
        "  (TypeAnn",
        "    As \"as\"",
        "    (TypeExpr",
        "      Ident \"int\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_quoted_mark_inline_empty() {
    let got = parse_expression("'[]");
    let expected = vec![
        "(Expr",
        "  (MarkExpr",
        "    (MarkInlineBody",
        "      MarkLitStart \"'[\"",
        "      (YmDoc",
        "      )",
        "      MarkLitEnd \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_quoted_mark_inline_multiline() {
    let got = parse_expression("'[hello\nworld]");
    let expected = vec![
        "(Expr",
        "  (MarkExpr",
        "    (MarkInlineBody",
        "      MarkLitStart \"'[\"",
        "      (YmDoc",
        "        YmText \"hello\"",
        "        Space \"\\n\"",
        "        YmText \"world\"",
        "      )",
        "      MarkLitEnd \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_quoted_mark_inline_rejects_heading_after_newline() {
    let got = parse_expression("'[hello\n# Title]");
    let expected = vec![
        "(Expr",
        "  (MarkExpr",
        "    (MarkInlineBody",
        "      MarkLitStart \"'[\"",
        "      (YmDoc",
        "        YmText \"hello\"",
        "        (InvalidToken",
        "          YmHashSigil \"# \"",
        "        )",
        "        (InvalidToken",
        "          Unknown \"Title\"",
        "        )",
        "      )",
        "      MarkLitEnd \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_quoted_mark_inline_rejects_list_after_newline() {
    let got = parse_expression("'[hello\n- item]");
    let expected = vec![
        "(Expr",
        "  (MarkExpr",
        "    (MarkInlineBody",
        "      MarkLitStart \"'[\"",
        "      (YmDoc",
        "        YmText \"hello\"",
        "        (InvalidToken",
        "          YmListDashSigil \"- \"",
        "        )",
        "        (InvalidToken",
        "          Unknown \"item\"",
        "        )",
        "      )",
        "      MarkLitEnd \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_quoted_mark_block() {
    let got = parse_expression("'{# Title\n}");
    let expected = vec![
        "(Expr",
        "  (MarkExpr",
        "    (MarkHeredocBody",
        "      MarkLitStart \"'{\"",
        "      (YmDoc",
        "        (YmHeading",
        "          YmHashSigil \"# \"",
        "          YmText \"Title\"",
        "          YmNewline \"\\n\"",
        "        )",
        "        (YmParagraph",
        "        )",
        "      )",
        "      MarkLitEnd \"}\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_quoted_mark_block_empty() {
    let got = parse_expression("'{}");
    let expected = vec![
        "(Expr",
        "  (MarkExpr",
        "    (MarkHeredocBody",
        "      MarkLitStart \"'{\"",
        "      (YmDoc",
        "      )",
        "      MarkLitEnd \"}\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_index_access() {
    let got = parse_expression("a[0]");
    let expected = vec![
        "(Expr",
        "  Ident \"a\"",
        "  (Index",
        "    (Bracket",
        "      BracketL \"[\"",
        "      (Expr",
        "        Number \"0\"",
        "      )",
        "      BracketR \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_index_open_range_suffix() {
    let got = parse_expression("xs[2..]");
    let expected = vec![
        "(Expr",
        "  Ident \"xs\"",
        "  (Index",
        "    (Bracket",
        "      BracketL \"[\"",
        "      (Expr",
        "        Number \"2\"",
        "        (SuffixNode",
        "          Suffix \"..\"",
        "        )",
        "      )",
        "      BracketR \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_index_open_range_prefix() {
    let got = parse_expression("xs[..2]");
    let expected = vec![
        "(Expr",
        "  Ident \"xs\"",
        "  (Index",
        "    (Bracket",
        "      BracketL \"[\"",
        "      (Expr",
        "        (PrefixNode",
        "          Prefix \"..\"",
        "          (Expr",
        "            Number \"2\"",
        "          )",
        "        )",
        "      )",
        "      BracketR \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_apply_ml_two_args() {
    let got = parse_expression("f x y");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyML",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        "  (ApplyML",
        "    (Expr",
        "      Ident \"y\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_apply_c_two_args() {
    let got = parse_expression("f(x, y)");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyC",
        "    ParenL \"(\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (Expr",
        "      Ident \"y\"",
        "    )",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_field_access() {
    let got = parse_expression("x.foo");
    let expected = vec![
        "(Expr",
        "  Ident \"x\"",
        "  (Field",
        "    DotField \".foo\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_field_then_path_sep_for_qualified_method_notation() {
    let got = parse_expression("x.foo::bar::baz");
    let expected = vec![
        "(Expr",
        "  Ident \"x\"",
        "  (Field",
        "    DotField \".foo\"",
        "  )",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"bar\"",
        "  )",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"baz\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_path_sep() {
    let got = parse_expression("Foo::bar");
    let expected = vec![
        "(Expr",
        "  Ident \"Foo\"",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"bar\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_infix_precedence() {
    let got = parse_expression("a + b * c");
    let expected = vec![
        "(Expr",
        "  Ident \"a\"",
        "  (InfixNode",
        "    Infix \"+\"",
        "    (Expr",
        "      Ident \"b\"",
        "      (InfixNode",
        "        Infix \"*\"",
        "        (Expr",
        "          Ident \"c\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_pipeline_is_left_associative() {
    let got = parse_expression("x | f y | g");
    let expected = vec![
        "(Expr",
        "  Ident \"x\"",
        "  (PipeNode",
        "    Pipe \"|\"",
        "    (Expr",
        "      Ident \"f\"",
        "      (ApplyML",
        "        (Expr",
        "          Ident \"y\"",
        "        )",
        "      )",
        "    )",
        "  )",
        "  (PipeNode",
        "    Pipe \"|\"",
        "    (Expr",
        "      Ident \"g\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_pipeline_binds_weaker_than_infix() {
    let got = parse_expression("a + b | f");
    let expected = vec![
        "(Expr",
        "  Ident \"a\"",
        "  (InfixNode",
        "    Infix \"+\"",
        "    (Expr",
        "      Ident \"b\"",
        "    )",
        "  )",
        "  (PipeNode",
        "    Pipe \"|\"",
        "    (Expr",
        "      Ident \"f\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_apply_colon_inline() {
    let got = parse_expression("f: x + y");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyColon",
        "    Colon \":\"",
        "    (Expr",
        "      Ident \"x\"",
        "      (InfixNode",
        "        Infix \"+\"",
        "        (Expr",
        "          Ident \"y\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_symbol_after_space_is_ml_argument() {
    let got = parse_expression("f :foo");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyML",
        "    (Expr",
        "      Symbol \":foo\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_symbol_at_paren_expr_start() {
    let got = parse_expression("(:foo 1)");
    let expected = vec![
        "(Expr",
        "  (Paren",
        "    ParenL \"(\"",
        "    (Expr",
        "      Symbol \":foo\"",
        "      (ApplyML",
        "        (Expr",
        "          Number \"1\"",
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
fn expr_symbol_without_leading_trivia_keeps_colon_application() {
    let got = parse_expression("f:foo");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyColon",
        "    Colon \":\"",
        "    (Expr",
        "      Ident \"foo\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_apply_colon_after_ml_arg() {
    let got = parse_expression("f x: g y z");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyML",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        "  (ApplyColon",
        "    Colon \":\"",
        "    (Expr",
        "      Ident \"g\"",
        "      (ApplyML",
        "        (Expr",
        "          Ident \"y\"",
        "        )",
        "      )",
        "      (ApplyML",
        "        (Expr",
        "          Ident \"z\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_apply_colon_indent_block() {
    let got = parse_expression("f:\n  x\n  y");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyColon",
        "    Colon \":\"",
        "    (IndentBlock",
        "      (Expr",
        "        Ident \"x\"",
        "      )",
        "      (Expr",
        "        Ident \"y\"",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_apply_colon_indent_block_after_path() {
    let got = parse_expression("std::sub::sub:\n  my x = 1\n  x");
    let expected = vec![
        "(Expr",
        "  Ident \"std\"",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"sub\"",
        "  )",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"sub\"",
        "  )",
        "  (ApplyColon",
        "    Colon \":\"",
        "    (IndentBlock",
        "      (Binding",
        "        (BindingHeader",
        "          My \"my\"",
        "          (Pattern",
        "            Ident \"x\"",
        "          )",
        "          Equal \"=\"",
        "        )",
        "        (BindingBody",
        "          (Expr",
        "            Number \"1\"",
        "          )",
        "        )",
        "      )",
        "      (Expr",
        "        Ident \"x\"",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_lambda_inline() {
    let got = parse_expression("\\x -> x + 1");
    let expected = vec![
        "(Expr",
        "  (LambdaExpr",
        "    Backslash \"\\\\\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    Arrow \"->\"",
        "    (Expr",
        "      Ident \"x\"",
        "      (InfixNode",
        "        Infix \"+\"",
        "        (Expr",
        "          Number \"1\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_lambda_multiple_params() {
    let got = parse_expression("\\() x -> x");
    let expected = vec![
        "(Expr",
        "  (LambdaExpr",
        "    Backslash \"\\\\\"",
        "    (Pattern",
        "      (PatParenGroup",
        "        ParenL \"(\"",
        "        ParenR \")\"",
        "      )",
        "    )",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    Arrow \"->\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_if_inline_else() {
    let got = parse_expression("if x: 1 else: 0");
    let expected = vec![
        "(Expr",
        "  (IfExpr",
        "    (IfArm",
        "      If \"if\"",
        "      (Cond",
        "        (Expr",
        "          Ident \"x\"",
        "        )",
        "      )",
        "      Colon \":\"",
        "      (Expr",
        "        Number \"1\"",
        "      )",
        "    )",
        "    (ElseArm",
        "      Else \"else\"",
        "      Colon \":\"",
        "      (Expr",
        "        Number \"0\"",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_if_indent_block_else() {
    let got = parse_expression("if x:\n  1\nelse: 0");
    let expected = vec![
        "(Expr",
        "  (IfExpr",
        "    (IfArm",
        "      If \"if\"",
        "      (Cond",
        "        (Expr",
        "          Ident \"x\"",
        "        )",
        "      )",
        "      Colon \":\"",
        "      (IndentBlock",
        "        (Expr",
        "          Number \"1\"",
        "        )",
        "      )",
        "    )",
        "    (ElseArm",
        "      Else \"else\"",
        "      Colon \":\"",
        "      (Expr",
        "        Number \"0\"",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_case_inline_arms() {
    let got = parse_expression("case x: 1 -> a, 2 -> b");
    let expected = vec![
        "(Expr",
        "  (CaseExpr",
        "    Case \"case\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "    (CaseBlock",
        "      Colon \":\"",
        "      (CaseArm",
        "        (Pattern",
        "          Number \"1\"",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"a\"",
        "        )",
        "      )",
        "      (Separator",
        "        Comma \",\"",
        "      )",
        "      (CaseArm",
        "        (Pattern",
        "          Number \"2\"",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"b\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_case_indent_block() {
    let got = parse_expression("case x:\n  1 -> a\n  _ -> b");
    let expected = vec![
        "(Expr",
        "  (CaseExpr",
        "    Case \"case\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "    (CaseBlock",
        "      Colon \":\"",
        "      (CaseArm",
        "        (Pattern",
        "          Number \"1\"",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"a\"",
        "        )",
        "      )",
        "      (CaseArm",
        "        (Pattern",
        "          Ident \"_\"",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"b\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_case_guard() {
    let got = parse_expression("case x:\n  n if n > 0 -> pos\n  _ -> neg");
    let expected = vec![
        "(Expr",
        "  (CaseExpr",
        "    Case \"case\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "    (CaseBlock",
        "      Colon \":\"",
        "      (CaseArm",
        "        (Pattern",
        "          Ident \"n\"",
        "        )",
        "        (CaseGuard",
        "          If \"if\"",
        "          (Expr",
        "            Ident \"n\"",
        "            (InfixNode",
        "              Infix \">\"",
        "              (Expr",
        "                Number \"0\"",
        "              )",
        "            )",
        "          )",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"pos\"",
        "        )",
        "      )",
        "      (CaseArm",
        "        (Pattern",
        "          Ident \"_\"",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"neg\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_case_qualified_variant_and_call_body() {
    let got = parse_expression(
        "case std::list::view_raw xs:\n  std::list::list_view::empty -> z\n  std::list::list_view::leaf x -> f(z, x)\n  std::list::list_view::node(left, right) -> z",
    );
    let expected = vec![
        "(Expr",
        "  (CaseExpr",
        "    Case \"case\"",
        "    (Expr",
        "      Ident \"std\"",
        "      (PathSep",
        "        ColonColon \"::\"",
        "        Ident \"list\"",
        "      )",
        "      (PathSep",
        "        ColonColon \"::\"",
        "        Ident \"view_raw\"",
        "      )",
        "      (ApplyML",
        "        (Expr",
        "          Ident \"xs\"",
        "        )",
        "      )",
        "    )",
        "    (CaseBlock",
        "      Colon \":\"",
        "      (CaseArm",
        "        (Pattern",
        "          Ident \"std\"",
        "          (PathSep",
        "            ColonColon \"::\"",
        "            Ident \"list\"",
        "          )",
        "          (PathSep",
        "            ColonColon \"::\"",
        "            Ident \"list_view\"",
        "          )",
        "          (PathSep",
        "            ColonColon \"::\"",
        "            Ident \"empty\"",
        "          )",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"z\"",
        "        )",
        "      )",
        "      (CaseArm",
        "        (Pattern",
        "          Ident \"std\"",
        "          (PathSep",
        "            ColonColon \"::\"",
        "            Ident \"list\"",
        "          )",
        "          (PathSep",
        "            ColonColon \"::\"",
        "            Ident \"list_view\"",
        "          )",
        "          (PathSep",
        "            ColonColon \"::\"",
        "            Ident \"leaf\"",
        "          )",
        "          (ApplyML",
        "            (Pattern",
        "              Ident \"x\"",
        "            )",
        "          )",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"f\"",
        "          (ApplyC",
        "            ParenL \"(\"",
        "            (Expr",
        "              Ident \"z\"",
        "            )",
        "            (Separator",
        "              Comma \",\"",
        "            )",
        "            (Expr",
        "              Ident \"x\"",
        "            )",
        "            ParenR \")\"",
        "          )",
        "        )",
        "      )",
        "      (CaseArm",
        "        (Pattern",
        "          Ident \"std\"",
        "          (PathSep",
        "            ColonColon \"::\"",
        "            Ident \"list\"",
        "          )",
        "          (PathSep",
        "            ColonColon \"::\"",
        "            Ident \"list_view\"",
        "          )",
        "          (PathSep",
        "            ColonColon \"::\"",
        "            Ident \"node\"",
        "          )",
        "          (ApplyC",
        "            ParenL \"(\"",
        "            (Pattern",
        "              Ident \"left\"",
        "            )",
        "            (Separator",
        "              Comma \",\"",
        "            )",
        "            (Pattern",
        "              Ident \"right\"",
        "            )",
        "            ParenR \")\"",
        "          )",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"z\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_catch_with_handler_name() {
    let got = parse_expression("catch f x:\n  Ok v -> v\n  Err e, h -> h e");
    let expected = vec![
        "(Expr",
        "  (CatchExpr",
        "    Catch \"catch\"",
        "    (Expr",
        "      Ident \"f\"",
        "      (ApplyML",
        "        (Expr",
        "          Ident \"x\"",
        "        )",
        "      )",
        "    )",
        "    (CatchBlock",
        "      Colon \":\"",
        "      (CatchArm",
        "        (Pattern",
        "          Ident \"Ok\"",
        "          (ApplyML",
        "            (Pattern",
        "              Ident \"v\"",
        "            )",
        "          )",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"v\"",
        "        )",
        "      )",
        "      (CatchArm",
        "        (Pattern",
        "          Ident \"Err\"",
        "          (ApplyML",
        "            (Pattern",
        "              Ident \"e\"",
        "            )",
        "          )",
        "        )",
        "        Comma \",\"",
        "        (Pattern",
        "          Ident \"h\"",
        "        )",
        "        Arrow \"->\"",
        "        (Expr",
        "          Ident \"h\"",
        "          (ApplyML",
        "            (Expr",
        "              Ident \"e\"",
        "            )",
        "          )",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_string_lit_simple() {
    let got = parse_expression("\"hello\"");
    let expected = vec![
        "(Expr",
        "  (StringLit",
        "    StringStart \"\\\"\"",
        "    StringText \"hello\"",
        "    StringEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_string_lit_empty() {
    let got = parse_expression("\"\"");
    let expected = vec![
        "(Expr",
        "  (StringLit",
        "    StringStart \"\\\"\"",
        "    StringEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_string_lit_escape_simple() {
    let got = parse_expression("\"a\\nb\"");
    let expected = vec![
        "(Expr",
        "  (StringLit",
        "    StringStart \"\\\"\"",
        "    StringText \"a\"",
        "    StringEscapeLead \"\\\\\"",
        "    StringEscapeSimple \"n\"",
        "    StringText \"b\"",
        "    StringEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_string_lit_unicode_escape() {
    let got = parse_expression("\"\\u{1F600}\"");
    let expected = vec![
        "(Expr",
        "  (StringLit",
        "    StringStart \"\\\"\"",
        "    StringEscapeLead \"\\\\\"",
        "    StringEscapeUnicodeStart \"u{\"",
        "    StringEscapeUnicodeHex \"1F600\"",
        "    StringEscapeUnicodeEnd \"}\"",
        "    StringEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_string_lit_interp() {
    let got = parse_expression("\"%{x}\"");
    let expected = vec![
        "(Expr",
        "  (StringLit",
        "    StringStart \"\\\"\"",
        "    (StringInterp",
        "      StringInterpPercent \"%\"",
        "      StringInterpOpenBrace \"{\"",
        "      (Expr",
        "        Ident \"x\"",
        "      )",
        "      StringInterpCloseBrace \"}\"",
        "    )",
        "    StringEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_string_lit_heredoc() {
    let got = parse_expression("\"\"\"hello\"\"\"");
    let expected = vec![
        "(Expr",
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
fn expr_string_lit_heredoc_multiline() {
    let got = parse_expression("\"\"\"line1\nline2\"\"\"");
    let expected = vec![
        "(Expr",
        "  (StringLit",
        "    StringStart \"\\\"\\\"\\\"\"",
        "    StringText \"line1\\nline2\"",
        "    StringEnd \"\\\"\\\"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_do_as_continuation_marker() {
    // do は継続渡し糖衣の差し込みマーカー（CST 上はアトム）
    // `my b = f(do); rest` => `my b = f(\b -> { rest })` に AST 変換フェーズで展開される
    let got = parse_expression("f(do)");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyC",
        "    ParenL \"(\"",
        "    (Expr",
        "      Do \"do\"",
        "    )",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_sigil_ident() {
    let got = parse_expression("$foo");
    let expected = vec!["(Expr", "  SigilIdent \"$foo\"", ")"];
    assert_eq!(got, expected);
}

#[test]
fn expr_empty_paren_group() {
    let got = parse_expression("()");
    let expected = vec![
        "(Expr",
        "  (Paren",
        "    ParenL \"(\"",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_chained_path_sep() {
    let got = parse_expression("Foo::bar::baz");
    let expected = vec![
        "(Expr",
        "  Ident \"Foo\"",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"bar\"",
        "  )",
        "  (PathSep",
        "    ColonColon \"::\"",
        "    Ident \"baz\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_infix_chained_mixed_precedence() {
    // x + y * z + w  =>  (x + (y * z)) + w
    let got = parse_expression("x + y * z + w");
    let expected = vec![
        "(Expr",
        "  Ident \"x\"",
        "  (InfixNode",
        "    Infix \"+\"",
        "    (Expr",
        "      Ident \"y\"",
        "      (InfixNode",
        "        Infix \"*\"",
        "        (Expr",
        "          Ident \"z\"",
        "        )",
        "      )",
        "    )",
        "  )",
        "  (InfixNode",
        "    Infix \"+\"",
        "    (Expr",
        "      Ident \"w\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_field_on_paren_group() {
    let got = parse_expression("(x, y).foo");
    let expected = vec![
        "(Expr",
        "  (Paren",
        "    ParenL \"(\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (Expr",
        "      Ident \"y\"",
        "    )",
        "    ParenR \")\"",
        "  )",
        "  (Field",
        "    DotField \".foo\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_rule_expr_simple() {
    // rule { "hello" }
    let got = parse_expression("rule { \"hello\" }");
    let expected = vec![
        "(Expr",
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

#[test]
fn expr_rule_lit_simple() {
    // ~"hello"
    let got = parse_expression("~\"hello\"");
    let expected = vec![
        "(Expr",
        "  (RuleLit",
        "    RuleLitStart \"~\\\"\"",
        "    RuleLitText \"hello\"",
        "    RuleLitEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_rule_lit_interp() {
    // ~"users/{id}" — {id} はパーサー参照（キャプチャなし）
    let got = parse_expression("~\"users/{id}\"");
    let expected = vec![
        "(Expr",
        "  (RuleLit",
        "    RuleLitStart \"~\\\"\"",
        "    RuleLitText \"users/\"",
        "    (RuleLitInterp",
        "      RuleLitOpenBrace \"{\"",
        "      (Expr",
        "        Ident \"id\"",
        "      )",
        "      RuleLitCloseBrace \"}\"",
        "    )",
        "    RuleLitEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_rule_lit_lazy_capture() {
    // ~"users/:id/posts" — :id は lazy capture
    let got = parse_expression("~\"users/:id/posts\"");
    let expected = vec![
        "(Expr",
        "  (RuleLit",
        "    RuleLitStart \"~\\\"\"",
        "    RuleLitText \"users/\"",
        "    (RuleLazyCapture",
        "      RuleLitColon \":\"",
        "      RuleLitText \"id\"",
        "    )",
        "    RuleLitText \"/posts\"",
        "    RuleLitEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_rule_body_capture() {
    // rule { a b = c(d) e } — b = c(d) はキャプチャバインディング
    let got = parse_expression("rule { a b = c(d) e }");
    let expected = vec![
        "(Expr",
        "  (RuleExpr",
        "    Rule \"rule\"",
        "    (BraceGroup",
        "      BraceL \"{\"",
        "      (Expr",
        "        Ident \"a\"",
        "      )",
        "      (Expr",
        "        Ident \"b\"",
        "        (RuleCapture",
        "          Equal \"=\"",
        "          (Expr",
        "            Ident \"c\"",
        "            (ApplyC",
        "              ParenL \"(\"",
        "              (Expr",
        "                Ident \"d\"",
        "              )",
        "              ParenR \")\"",
        "            )",
        "          )",
        "        )",
        "      )",
        "      (Expr",
        "        Ident \"e\"",
        "      )",
        "      BraceR \"}\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_rule_body_alternation() {
    // rule { a b* | c+ d } — | で alternation
    let got = parse_expression("rule { a b* | c+ d }");
    let expected = vec![
        "(Expr",
        "  (RuleExpr",
        "    Rule \"rule\"",
        "    (BraceGroup",
        "      BraceL \"{\"",
        "      (Expr",
        "        Ident \"a\"",
        "      )",
        "      (Expr",
        "        Ident \"b\"",
        "        (RuleQuant",
        "          RuleQuantStar \"*\"",
        "        )",
        "      )",
        "      (Separator",
        "        Pipe \"|\"",
        "      )",
        "      (Expr",
        "        Ident \"c\"",
        "        (RuleQuant",
        "          RuleQuantPlus \"+\"",
        "        )",
        "      )",
        "      (Expr",
        "        Ident \"d\"",
        "      )",
        "      BraceR \"}\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_rule_lit_interp_capture() {
    // ~"users/{id = ident}/posts" — {id = ident} はキャプチャ
    let got = parse_expression("~\"users/{id = ident}/posts\"");
    let expected = vec![
        "(Expr",
        "  (RuleLit",
        "    RuleLitStart \"~\\\"\"",
        "    RuleLitText \"users/\"",
        "    (RuleLitInterp",
        "      RuleLitOpenBrace \"{\"",
        "      (Expr",
        "        Ident \"id\"",
        "        (RuleCapture",
        "          Equal \"=\"",
        "          (Expr",
        "            Ident \"ident\"",
        "          )",
        "        )",
        "      )",
        "      RuleLitCloseBrace \"}\"",
        "    )",
        "    RuleLitText \"/posts\"",
        "    RuleLitEnd \"\\\"\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_rule_body_quantifier_lazy() {
    // rule { a*? b+? c? } — lazy 量化子
    let got = parse_expression("rule { a*? b+? c? }");
    let expected = vec![
        "(Expr",
        "  (RuleExpr",
        "    Rule \"rule\"",
        "    (BraceGroup",
        "      BraceL \"{\"",
        "      (Expr",
        "        Ident \"a\"",
        "        (RuleQuant",
        "          RuleQuantStarLazy \"*?\"",
        "        )",
        "      )",
        "      (Expr",
        "        Ident \"b\"",
        "        (RuleQuant",
        "          RuleQuantPlusLazy \"+?\"",
        "        )",
        "      )",
        "      (Expr",
        "        Ident \"c\"",
        "        (RuleQuant",
        "          RuleQuantOpt \"?\"",
        "        )",
        "      )",
        "      BraceR \"}\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_rule_body_path_and_field() {
    // rule { peg::digit.many } — パスとフィールドアクセス
    let got = parse_expression("rule { peg::digit.many }");
    let expected = vec![
        "(Expr",
        "  (RuleExpr",
        "    Rule \"rule\"",
        "    (BraceGroup",
        "      BraceL \"{\"",
        "      (Expr",
        "        Ident \"peg\"",
        "        (PathSep",
        "          ColonColon \"::\"",
        "          Ident \"digit\"",
        "        )",
        "        (Field",
        "          DotField \".many\"",
        "        )",
        "      )",
        "      BraceR \"}\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

// ── block comment transparency ───────────────────────────────────────────────

#[test]
fn expr_block_comment_between_ml_args() {
    // comment between tokens is transparent — same AST as without it
    let without = parse_expression("f x");
    let with_comment = parse_expression("f /* comment */ x");
    assert_eq!(with_comment, without);
}

#[test]
fn expr_block_comment_in_infix() {
    let without = parse_expression("a + b");
    let with_comment = parse_expression("a + /* comment */ b");
    assert_eq!(with_comment, without);
}

#[test]
fn expr_ml_arg_brace_block_parses_inner_ml_apply() {
    let got = parse_expression("f { g x }");
    let expected = vec![
        "(Expr",
        "  Ident \"f\"",
        "  (ApplyML",
        "    (Expr",
        "      (BraceGroup",
        "        BraceL \"{\"",
        "        (Expr",
        "          Ident \"g\"",
        "          (ApplyML",
        "            (Expr",
        "              Ident \"x\"",
        "            )",
        "          )",
        "        )",
        "        BraceR \"}\"",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn expr_nested_block_comment() {
    let without = parse_expression("f x");
    let with_comment = parse_expression("f /* /* nested */ comment */ x");
    assert_eq!(with_comment, without);
}

#[test]
fn expr_line_comment_in_multiline_infix() {
    // line comment on continuation line is transparent
    let without = parse_expression("a\n+ b");
    let with_comment = parse_expression("a\n// comment\n+ b");
    assert_eq!(with_comment, without);
}
