use chasa::error::LatestSink;
use chasa::input::{In, Input as _, IsCut};
use im::HashSet;
use reborrow_generic::Reborrow as _;

use yulang_parser::context::{Env, State};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::op::standard_op_table;
use yulang_parser::scan::trivia::scan_trivia;
use yulang_parser::sink::{Event, EventSink, VecSink};
use yulang_parser::typ::parse::parse_type;

fn parse_typ(source: &str) -> Vec<String> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    let leading = i.run(scan_trivia).map(|t| t.info());
    let parsed = leading.and_then(|info| parse_type(info, i.rb()));
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
fn typ_paren_newline_separator() {
    let got = parse_typ("(A\nB)");
    let expected = vec![
        "(TypeExpr",
        "  (TypeParenGroup",
        "    ParenL \"(\"",
        "    (TypeExpr",
        "      Ident \"A\"",
        "    )",
        "    (Separator",
        "    )",
        "    (TypeExpr",
        "      Ident \"B\"",
        "    )",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_call_newline_separator() {
    let got = parse_typ("f(A\nB)");
    let expected = vec![
        "(TypeExpr",
        "  Ident \"f\"",
        "  (TypeCall",
        "    ParenL \"(\"",
        "    (TypeExpr",
        "      Ident \"A\"",
        "    )",
        "    (Separator",
        "    )",
        "    (TypeExpr",
        "      Ident \"B\"",
        "    )",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_record_newline_separator() {
    let got = parse_typ("{a: A\nb: B}");
    let expected = vec![
        "(TypeExpr",
        "  (TypeRecord",
        "    BraceL \"{\"",
        "    (TypeField",
        "      Ident \"a\"",
        "      Colon \":\"",
        "      (TypeExpr",
        "        Ident \"A\"",
        "      )",
        "    )",
        "    (Separator",
        "    )",
        "    (TypeField",
        "      Ident \"b\"",
        "      Colon \":\"",
        "      (TypeExpr",
        "        Ident \"B\"",
        "      )",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_paren_comma_separator() {
    let got = parse_typ("(A, B)");
    let expected = vec![
        "(TypeExpr",
        "  (TypeParenGroup",
        "    ParenL \"(\"",
        "    (TypeExpr",
        "      Ident \"A\"",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (TypeExpr",
        "      Ident \"B\"",
        "    )",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_record_shorthand_is_invalid() {
    let got = parse_typ("{a: A, b}");
    assert!(
        got.iter().any(|line| line.contains("InvalidToken")),
        "expected InvalidToken for shorthand field, got: {got:?}"
    );
}

#[test]
fn typ_poly_variant_basic() {
    let got = parse_typ(":{A Int, B}");
    let expected = vec![
        "(TypeExpr",
        "  (TypePolyVariant",
        "    Colon \":\"",
        "    BraceL \"{\"",
        "    (TypePolyVariantItem",
        "      Ident \"A\"",
        "      (TypeExpr",
        "        Ident \"Int\"",
        "      )",
        "    )",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    (TypePolyVariantItem",
        "      Ident \"B\"",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_poly_variant_multiple_payloads() {
    let got = parse_typ(":{A Int Bool}");
    let expected = vec![
        "(TypeExpr",
        "  (TypePolyVariant",
        "    Colon \":\"",
        "    BraceL \"{\"",
        "    (TypePolyVariantItem",
        "      Ident \"A\"",
        "      (TypeExpr",
        "        Ident \"Int\"",
        "      )",
        "      (TypeExpr",
        "        Ident \"Bool\"",
        "      )",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_poly_variant_newline_separator() {
    let got = parse_typ(":{A Int\nB}");
    let expected = vec![
        "(TypeExpr",
        "  (TypePolyVariant",
        "    Colon \":\"",
        "    BraceL \"{\"",
        "    (TypePolyVariantItem",
        "      Ident \"A\"",
        "      (TypeExpr",
        "        Ident \"Int\"",
        "      )",
        "    )",
        "    (Separator",
        "    )",
        "    (TypePolyVariantItem",
        "      Ident \"B\"",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_unknown_char_root_is_invalid() {
    let got = parse_typ("@");
    let expected = vec!["(InvalidToken", "  Unknown \"@\"", ")"];
    assert_eq!(got, expected);
}

#[test]
fn typ_unknown_char_in_group_recovers() {
    let got = parse_typ("(A @ B)");
    let expected = vec![
        "(TypeExpr",
        "  (TypeParenGroup",
        "    ParenL \"(\"",
        "    (TypeExpr",
        "      Ident \"A\"",
        "    )",
        "    (InvalidToken",
        "      Unknown \"@\"",
        "    )",
        "    (TypeExpr",
        "      Ident \"B\"",
        "    )",
        "    ParenR \")\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_arrow_simple() {
    let got = parse_typ("Int -> String");
    let expected = vec![
        "(TypeExpr",
        "  Ident \"Int\"",
        "  (TypeArrow",
        "    Arrow \"->\"",
        "    (TypeExpr",
        "      Ident \"String\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_arrow_chained() {
    let got = parse_typ("Int -> String -> Bool");
    let expected = vec![
        "(TypeExpr",
        "  Ident \"Int\"",
        "  (TypeArrow",
        "    Arrow \"->\"",
        "    (TypeExpr",
        "      Ident \"String\"",
        "      (TypeArrow",
        "        Arrow \"->\"",
        "        (TypeExpr",
        "          Ident \"Bool\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_apply_ml() {
    let got = parse_typ("List Int");
    let expected = vec![
        "(TypeExpr",
        "  Ident \"List\"",
        "  (TypeApply",
        "    (TypeExpr",
        "      Ident \"Int\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_apply_ml_two_args() {
    let got = parse_typ("Dict String Int");
    let expected = vec![
        "(TypeExpr",
        "  Ident \"Dict\"",
        "  (TypeApply",
        "    (TypeExpr",
        "      Ident \"String\"",
        "    )",
        "  )",
        "  (TypeApply",
        "    (TypeExpr",
        "      Ident \"Int\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_effect_row_basic() {
    let got = parse_typ("'[e]");
    let expected = vec![
        "(TypeExpr",
        "  (TypeEffectRow",
        "    Apostrophe \"'\"",
        "    (TypeRow",
        "      BracketL \"[\"",
        "      (TypeExpr",
        "        Ident \"e\"",
        "      )",
        "      BracketR \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_effect_row_variable() {
    let got = parse_typ("'['e]");
    let expected = vec![
        "(TypeExpr",
        "  (TypeEffectRow",
        "    Apostrophe \"'\"",
        "    (TypeRow",
        "      BracketL \"[\"",
        "      (TypeExpr",
        "        SigilIdent \"'e\"",
        "      )",
        "      BracketR \"]\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn typ_effect_row_as_type_arg() {
    let got = parse_typ("Foo '['e]");
    let expected = vec![
        "(TypeExpr",
        "  Ident \"Foo\"",
        "  (TypeApply",
        "    (TypeExpr",
        "      (TypeEffectRow",
        "        Apostrophe \"'\"",
        "        (TypeRow",
        "          BracketL \"[\"",
        "          (TypeExpr",
        "            SigilIdent \"'e\"",
        "          )",
        "          BracketR \"]\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}
