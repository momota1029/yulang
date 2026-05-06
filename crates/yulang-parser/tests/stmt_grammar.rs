use chasa::error::LatestSink;
use chasa::input::{In, Input as _, IsCut};
use chasa::prelude::eoi;
use im::HashSet;
use reborrow_generic::Reborrow as _;
use rowan::SyntaxNode;

use yulang_parser::context::{Env, State};
use yulang_parser::lex::{Lex, SyntaxKind, Trivia, TriviaInfo};
use yulang_parser::op::standard_op_table;
use yulang_parser::scan::trivia::scan_trivia;
use yulang_parser::sink::{Event, EventSink, GreenSink, VecSink, YulangLanguage};
use yulang_parser::stmt::parse_statement;

fn parse_stmt_once(source: &str) -> Vec<String> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    let leading = i.run(scan_trivia).map(|t| t.info());
    let parsed = leading.and_then(|info| parse_statement(info, i.rb()));
    if let Some(either::Either::Right(stop)) = parsed {
        i.env.state.sink.start(SyntaxKind::InvalidToken);
        i.env.state.sink.lex(&stop);
        i.env.state.sink.finish();
    }

    let (events, lexs) = std::mem::take(&mut i.env.state.sink).into_parts();
    dump(&events, &lexs)
}

fn parse_stmt_all(source: &str) -> Vec<String> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    let mut next_info = None;
    loop {
        let info = if let Some(info) = next_info.take() {
            info
        } else {
            let leading = i.run(scan_trivia).unwrap_or_else(Trivia::empty);
            leading.info()
        };
        if matches!(info, yulang_parser::lex::TriviaInfo::None) && i.lookahead(eoi).is_some() {
            break;
        }
        let Some(parsed) = parse_statement(info, i.rb()) else {
            break;
        };
        match parsed {
            either::Either::Left(info) => {
                next_info = Some(info);
            }
            either::Either::Right(stop) => {
                i.env.state.sink.start(SyntaxKind::InvalidToken);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
            }
        }
    }

    let (events, lexs) = std::mem::take(&mut i.env.state.sink).into_parts();
    dump(&events, &lexs)
}

fn parse_stmt_all_lexs(source: &str) -> Vec<Lex> {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    let mut next_info = None;
    loop {
        let info = if let Some(info) = next_info.take() {
            info
        } else {
            let leading = i.run(scan_trivia).unwrap_or_else(Trivia::empty);
            leading.info()
        };
        if matches!(info, yulang_parser::lex::TriviaInfo::None) && i.lookahead(eoi).is_some() {
            break;
        }
        let Some(parsed) = parse_statement(info, i.rb()) else {
            break;
        };
        match parsed {
            either::Either::Left(info) => {
                next_info = Some(info);
            }
            either::Either::Right(stop) => {
                i.env.state.sink.start(SyntaxKind::InvalidToken);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
            }
        }
    }

    let (_events, lexs) = std::mem::take(&mut i.env.state.sink).into_parts();
    lexs
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

fn parse_stmt_once_green(source: &str) -> SyntaxNode<YulangLanguage> {
    let mut state: State<GreenSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    i.env.state.sink.start(SyntaxKind::Root);
    let leading = i.run(scan_trivia).unwrap_or_else(Trivia::empty).info();
    let parsed = parse_statement(leading, i.rb());
    if let Some(either::Either::Right(stop)) = parsed {
        i.env.state.sink.start(SyntaxKind::InvalidToken);
        i.env.state.sink.lex(&stop);
        i.env.state.sink.finish();
    }
    i.env.state.sink.finish();
    SyntaxNode::<YulangLanguage>::new_root(std::mem::take(&mut i.env.state.sink).finish_green())
}

fn parse_stmt_all_green(source: &str) -> SyntaxNode<YulangLanguage> {
    let mut state: State<GreenSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    i.env.state.sink.start(SyntaxKind::Root);
    let mut next_info = None;
    loop {
        let info = if let Some(info) = next_info.take() {
            info
        } else {
            let leading = i.run(scan_trivia).unwrap_or_else(Trivia::empty);
            leading.info()
        };
        if matches!(info, TriviaInfo::None) && i.lookahead(eoi).is_some() {
            break;
        }
        let Some(parsed) = parse_statement(info, i.rb()) else {
            break;
        };
        match parsed {
            either::Either::Left(info) => {
                next_info = Some(info);
            }
            either::Either::Right(stop) => {
                i.env.state.sink.start(SyntaxKind::InvalidToken);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
            }
        }
    }
    i.env.state.sink.finish();
    SyntaxNode::<YulangLanguage>::new_root(std::mem::take(&mut i.env.state.sink).finish_green())
}

fn parse_module_green(source: &str) -> SyntaxNode<YulangLanguage> {
    SyntaxNode::<YulangLanguage>::new_root(yulang_parser::parse_module_to_green(source))
}

#[test]
fn stmt_expr_fallback() {
    let got = parse_stmt_once("x + y");
    let expected = vec![
        "(Expr",
        "  Ident \"x\"",
        "  (InfixNode",
        "    Infix \"+\"",
        "    (Expr",
        "      Ident \"y\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_binding_basic() {
    let got = parse_stmt_once("my x = 1");
    let expected = vec![
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_pub_binding_head_only() {
    let got = parse_stmt_once("pub x");
    let expected = vec![
        "(Binding",
        "  (BindingHeader",
        "    Pub \"pub\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_pub_binding_with_body() {
    let got = parse_stmt_once("pub x = 1");
    let expected = vec![
        "(Binding",
        "  (BindingHeader",
        "    Pub \"pub\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_for_in_indent_body() {
    let got = parse_stmt_once("for x in xs:\n  x");
    let expected = vec![
        "(ForStmt",
        "  (ForHeader",
        "    For \"for\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    In \"in\"",
        "    (Expr",
        "      Ident \"xs\"",
        "    )",
        "    Colon \":\"",
        "  )",
        "  (ForBody",
        "    (IndentBlock",
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
fn stmt_for_in_label_indent_body() {
    let got = parse_stmt_once("for 'outer x in xs:\n  x");
    let expected = vec![
        "(ForStmt",
        "  (ForHeader",
        "    For \"for\"",
        "    (ForLabel",
        "      SigilIdent \"'outer\"",
        "    )",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    In \"in\"",
        "    (Expr",
        "      Ident \"xs\"",
        "    )",
        "    Colon \":\"",
        "  )",
        "  (ForBody",
        "    (IndentBlock",
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
fn stmt_for_in_brace_body() {
    let got = parse_stmt_once("for x in xs { x }");
    let expected = vec![
        "(ForStmt",
        "  (ForHeader",
        "    For \"for\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    In \"in\"",
        "    (Expr",
        "      Ident \"xs\"",
        "    )",
        "  )",
        "  (ForBody",
        "    (BraceGroup",
        "      BraceL \"{\"",
        "      (Expr",
        "        Ident \"x\"",
        "      )",
        "      BraceR \"}\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_type_decl_bare_stops_at_newline() {
    let got = parse_stmt_all("type value\nour x = 1");
    let expected = vec![
        "(TypeDecl",
        "  Type \"type\"",
        "  Ident \"value\"",
        "  (TypeVars",
        "  )",
        ")",
        "(Binding",
        "  (BindingHeader",
        "    Our \"our\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_doc_comment_block_basic() {
    let got = parse_stmt_once("---\n# Title\n---");
    let expected = vec![
        "(DocCommentDecl",
        "  DocComment \"---\"",
        "  (YmDoc",
        "    YmNewline \"\\n\"",
        "    (YmHeading",
        "      YmHashSigil \"# \"",
        "      YmText \"Title\"",
        "      YmNewline \"\\n\"",
        "    )",
        "  )",
        "  DocComment \"---\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_doc_comment_line_basic() {
    let got = parse_stmt_once("-- hello");
    let expected = vec![
        "(DocCommentDecl",
        "  DocComment \"--\"",
        "  (YmDoc",
        "    (YmParagraph",
        "      YmText \" hello\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_doc_comment_line_with_newline() {
    let got = parse_stmt_all("-- hello\n");
    let expected = vec![
        "(DocCommentDecl",
        "  DocComment \"--\"",
        "  (YmDoc",
        "    (YmParagraph",
        "      YmText \" hello\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_doc_comment_block_then_binding() {
    let got = parse_stmt_all("---\n# Title\n---\nmy x = 1");
    let expected = vec![
        "(DocCommentDecl",
        "  DocComment \"---\"",
        "  (YmDoc",
        "    YmNewline \"\\n\"",
        "    (YmHeading",
        "      YmHashSigil \"# \"",
        "      YmText \"Title\"",
        "      YmNewline \"\\n\"",
        "    )",
        "  )",
        "  DocComment \"---\"",
        ")",
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_doc_comment_block_yulang_fence() {
    let got = parse_stmt_once("---\n二つの座標を足す。\n```yulang\nmy x = 1\n```\n---");
    let expected = vec![
        "(DocCommentDecl",
        "  DocComment \"---\"",
        "  (YmDoc",
        "    (YmParagraph",
        "      Space \"\\n\"",
        "      YmText \"二つの座標を足す。\"",
        "      Space \"\\n\"",
        "    )",
        "    (YmCodeFence",
        "      YmFenceSigil \"```\"",
        "      (YmCodeFenceInfo",
        "        YmText \"yulang\"",
        "      )",
        "      YmNewline \"\\n\"",
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
        "      YmFenceSigil \"```\"",
        "    )",
        "  )",
        "  DocComment \"---\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_doc_comment_block_yulang_fence_then_binding() {
    let got = parse_stmt_all("---\n二つの座標を足す。\n```yulang\nmy x = 1\n```\n---\nmy y = 2");
    let expected = vec![
        "(DocCommentDecl",
        "  DocComment \"---\"",
        "  (YmDoc",
        "    (YmParagraph",
        "      Space \"\\n\"",
        "      YmText \"二つの座標を足す。\"",
        "      Space \"\\n\"",
        "    )",
        "    (YmCodeFence",
        "      YmFenceSigil \"```\"",
        "      (YmCodeFenceInfo",
        "        YmText \"yulang\"",
        "      )",
        "      YmNewline \"\\n\"",
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
        "      YmFenceSigil \"```\"",
        "    )",
        "  )",
        "  DocComment \"---\"",
        ")",
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"y\"",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Number \"2\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_doc_comment_line_then_binding() {
    let got = parse_stmt_all("-- hello\nmy x = 1");
    let expected = vec![
        "(DocCommentDecl",
        "  DocComment \"--\"",
        "  (YmDoc",
        "    (YmParagraph",
        "      YmText \" hello\"",
        "    )",
        "  )",
        ")",
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_doc_comment_line_then_binding_keeps_newline_leading_info() {
    let lexs = parse_stmt_all_lexs("-- hello\nmy x = 1");
    let my = lexs
        .iter()
        .find(|lex| lex.kind == SyntaxKind::My)
        .expect("expected My token");
    assert_eq!(
        my.leading_trivia_info,
        TriviaInfo::Newline {
            indent: 0,
            quote_level: 0,
            blank_line: false
        }
    );
}

#[test]
fn stmt_doc_comment_line_blank_line_then_binding() {
    let got = parse_stmt_all("-- hello\n\nmy x = 1");
    let expected = vec![
        "(DocCommentDecl",
        "  DocComment \"--\"",
        "  (YmDoc",
        "    (YmParagraph",
        "      YmText \" hello\"",
        "    )",
        "  )",
        ")",
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_doc_comment_line_blank_line_then_binding_keeps_newline_leading_info() {
    let lexs = parse_stmt_all_lexs("-- hello\n\nmy x = 1");
    let my = lexs
        .iter()
        .find(|lex| lex.kind == SyntaxKind::My)
        .expect("expected My token");
    assert_eq!(
        my.leading_trivia_info,
        TriviaInfo::Newline {
            indent: 0,
            quote_level: 0,
            blank_line: false
        }
    );
}

#[test]
fn stmt_mod_decl_semicolon() {
    let got = parse_stmt_once("mod Foo;");
    let expected = vec![
        "(ModDecl",
        "  Mod \"mod\"",
        "  Ident \"Foo\"",
        "  Semicolon \";\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_mod_decl_brace_body() {
    let got = parse_stmt_once("mod Foo { x; }");
    let expected = vec![
        "(ModDecl",
        "  Mod \"mod\"",
        "  Ident \"Foo\"",
        "  (BraceGroup",
        "    BraceL \"{\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "    (Separator",
        "      Semicolon \";\"",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_brace_body_newline_implicit_separator() {
    let got = parse_stmt_once("mod Foo { x\ny }");
    let expected = vec![
        "(ModDecl",
        "  Mod \"mod\"",
        "  Ident \"Foo\"",
        "  (BraceGroup",
        "    BraceL \"{\"",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "    (Separator",
        "    )",
        "    (Expr",
        "      Ident \"y\"",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_role_decl_semicolon() {
    let got = parse_stmt_once("role Eq;");
    let expected = vec![
        "(RoleDecl",
        "  Role \"role\"",
        "  (TypeExpr",
        "    Ident \"Eq\"",
        "  )",
        "  Semicolon \";\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_impl_decl_via_semicolon() {
    let got = parse_stmt_once("impl Eq via Ord;");
    let expected = vec![
        "(ImplDecl",
        "  Impl \"impl\"",
        "  (TypeExpr",
        "    Ident \"Eq\"",
        "  )",
        "  Via \"via\"",
        "  (TypeExpr",
        "    Ident \"Ord\"",
        "  )",
        "  Semicolon \";\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_cast_decl_inline_body() {
    let got = parse_stmt_once("cast(x: user_id): int = x.raw");
    let expected = vec![
        "(CastDecl",
        "  Cast \"cast\"",
        "  ParenL \"(\"",
        "  (Pattern",
        "    Ident \"x\"",
        "    (TypeAnn",
        "      Colon \":\"",
        "      (TypeExpr",
        "        Ident \"user_id\"",
        "      )",
        "    )",
        "  )",
        "  ParenR \")\"",
        "  (TypeAnn",
        "    Colon \":\"",
        "    (TypeExpr",
        "      Ident \"int\"",
        "    )",
        "  )",
        "  Equal \"=\"",
        "  (BindingBody",
        "    (Expr",
        "      Ident \"x\"",
        "      (Field",
        "        DotField \".raw\"",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_pub_cast_decl_inline_body() {
    let got = parse_stmt_once("pub cast(x: int): user_id = user_id { raw: x }");
    let expected = vec![
        "(CastDecl",
        "  Pub \"pub\"",
        "  Cast \"cast\"",
        "  ParenL \"(\"",
        "  (Pattern",
        "    Ident \"x\"",
        "    (TypeAnn",
        "      Colon \":\"",
        "      (TypeExpr",
        "        Ident \"int\"",
        "      )",
        "    )",
        "  )",
        "  ParenR \")\"",
        "  (TypeAnn",
        "    Colon \":\"",
        "    (TypeExpr",
        "      Ident \"user_id\"",
        "    )",
        "  )",
        "  Equal \"=\"",
        "  (BindingBody",
        "    (Expr",
        "      Ident \"user_id\"",
        "      (ApplyML",
        "        (Expr",
        "          (BraceGroup",
        "            BraceL \"{\"",
        "            (Expr",
        "              Ident \"raw\"",
        "              (ApplyColon",
        "                Colon \":\"",
        "                (Expr",
        "                  Ident \"x\"",
        "                )",
        "              )",
        "            )",
        "            BraceR \"}\"",
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
fn stmt_act_decl_path_semicolon() {
    let got = parse_stmt_once("act Console::Read;");
    let expected = vec![
        "(ActDecl",
        "  Act \"act\"",
        "  Ident \"Console\"",
        "  ColonColon \"::\"",
        "  Ident \"Read\"",
        "  Semicolon \";\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_act_decl_copy_with_type_arg() {
    let got = parse_stmt_once("act local 't = var 't");
    let expected = vec![
        "(ActDecl",
        "  Act \"act\"",
        "  Ident \"local\"",
        "  (TypeExpr",
        "    SigilIdent \"'t\"",
        "  )",
        "  Equal \"=\"",
        "  (TypeExpr",
        "    Ident \"var\"",
        "    (TypeApply",
        "      (TypeExpr",
        "        SigilIdent \"'t\"",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_where_clause_block() {
    let got = parse_stmt_once("where:\n    Self: Sized\n    Int: Add Int");
    let expected = vec![
        "(WhereClause",
        "  Where \"where\"",
        "  Colon \":\"",
        "  (WhereConstraint",
        "    (TypeExpr",
        "      Ident \"Self\"",
        "    )",
        "    Colon \":\"",
        "    (TypeExpr",
        "      Ident \"Sized\"",
        "    )",
        "  )",
        "  (WhereConstraint",
        "    (TypeExpr",
        "      Ident \"Int\"",
        "    )",
        "    Colon \":\"",
        "    (TypeExpr",
        "      Ident \"Add\"",
        "      (TypeApply",
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
fn stmt_act_decl_binding_type_ann_without_equal() {
    let got = parse_stmt_once("act a:\n    our r: a -> b");
    let expected = vec![
        "(ActDecl",
        "  Act \"act\"",
        "  Ident \"a\"",
        "  Colon \":\"",
        "  (IndentBlock",
        "    (Binding",
        "      (BindingHeader",
        "        Our \"our\"",
        "        (Pattern",
        "          Ident \"r\"",
        "          (TypeAnn",
        "            Colon \":\"",
        "            (TypeExpr",
        "              Ident \"a\"",
        "              (TypeArrow",
        "                Arrow \"->\"",
        "                (TypeExpr",
        "                  Ident \"b\"",
        "                )",
        "              )",
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
fn stmt_type_decl_equal_semicolon() {
    let got = parse_stmt_once("type T = Int;");
    let expected = vec![
        "(TypeDecl",
        "  Type \"type\"",
        "  Ident \"T\"",
        "  (TypeVars",
        "  )",
        "  Equal \"=\"",
        "  (TypeExpr",
        "    Ident \"Int\"",
        "  )",
        "  Semicolon \";\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_struct_decl_brace_fields() {
    let got = parse_stmt_once("struct S { x: Int }");
    let expected = vec![
        "(StructDecl",
        "  Struct \"struct\"",
        "  Ident \"S\"",
        "  (TypeVars",
        "  )",
        "  BraceL \"{\"",
        "  (StructField",
        "    Ident \"x\"",
        "    Colon \":\"",
        "    (TypeExpr",
        "      Ident \"Int\"",
        "    )",
        "  )",
        "  BraceR \"}\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_enum_decl_brace_variants() {
    let got = parse_stmt_once("enum E { A, B }");
    let expected = vec![
        "(EnumDecl",
        "  Enum \"enum\"",
        "  Ident \"E\"",
        "  (TypeVars",
        "  )",
        "  BraceL \"{\"",
        "  (EnumVariant",
        "    Ident \"A\"",
        "  )",
        "  (Separator",
        "    Comma \",\"",
        "  )",
        "  (EnumVariant",
        "    Ident \"B\"",
        "  )",
        "  BraceR \"}\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_enum_decl_brace_variants_with_block() {
    let got = parse_stmt_once("enum E { A, B } with:\n  our x.foo = true");
    let expected = vec![
        "(EnumDecl",
        "  Enum \"enum\"",
        "  Ident \"E\"",
        "  (TypeVars",
        "  )",
        "  BraceL \"{\"",
        "  (EnumVariant",
        "    Ident \"A\"",
        "  )",
        "  (Separator",
        "    Comma \",\"",
        "  )",
        "  (EnumVariant",
        "    Ident \"B\"",
        "  )",
        "  BraceR \"}\"",
        "  With \"with\"",
        "  Colon \":\"",
        "  (IndentBlock",
        "    (Binding",
        "      (BindingHeader",
        "        Our \"our\"",
        "        (Pattern",
        "          Ident \"x\"",
        "          (Field",
        "            DotField \".foo\"",
        "          )",
        "        )",
        "        Equal \"=\"",
        "      )",
        "      (BindingBody",
        "        (Expr",
        "          Ident \"true\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_enum_decl_inline_variants() {
    let got = parse_stmt_once("enum opt 't = nil | just 't");
    let expected = vec![
        "(EnumDecl",
        "  Enum \"enum\"",
        "  Ident \"opt\"",
        "  (TypeVars",
        "    SigilIdent \"'t\"",
        "  )",
        "  Equal \"=\"",
        "  (EnumVariant",
        "    Ident \"nil\"",
        "  )",
        "  Pipe \"|\"",
        "  (EnumVariant",
        "    Ident \"just\"",
        "    (TypeExpr",
        "      SigilIdent \"'t\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_enum_decl_inline_with_block() {
    let got = parse_stmt_once("enum E = A with:\n  our x.foo = true");
    let expected = vec![
        "(EnumDecl",
        "  Enum \"enum\"",
        "  Ident \"E\"",
        "  (TypeVars",
        "  )",
        "  Equal \"=\"",
        "  (EnumVariant",
        "    Ident \"A\"",
        "  )",
        "  With \"with\"",
        "  Colon \":\"",
        "  (IndentBlock",
        "    (Binding",
        "      (BindingHeader",
        "        Our \"our\"",
        "        (Pattern",
        "          Ident \"x\"",
        "          (Field",
        "            DotField \".foo\"",
        "          )",
        "        )",
        "        Equal \"=\"",
        "      )",
        "      (BindingBody",
        "        (Expr",
        "          Ident \"true\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_use_decl_simple_path() {
    let got = parse_stmt_once("use std::io");
    let expected = vec![
        "(UseDecl",
        "  Use \"use\"",
        "  Ident \"std\"",
        "  ColonColon \"::\"",
        "  Ident \"io\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_use_decl_glob() {
    let got = parse_stmt_once("use std::io::*");
    let expected = vec![
        "(UseDecl",
        "  Use \"use\"",
        "  Ident \"std\"",
        "  ColonColon \"::\"",
        "  Ident \"io\"",
        "  ColonColon \"::\"",
        "  OpName \"*\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_use_decl_group() {
    let got = parse_stmt_once("use std::io::{Read, Write}");
    let expected = vec![
        "(UseDecl",
        "  Use \"use\"",
        "  Ident \"std\"",
        "  ColonColon \"::\"",
        "  Ident \"io\"",
        "  ColonColon \"::\"",
        "  (BraceGroup",
        "    BraceL \"{\"",
        "    Ident \"Read\"",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    Ident \"Write\"",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_use_decl_slash_path() {
    let got = parse_stmt_once("use a/b::c");
    let expected = vec![
        "(UseDecl",
        "  Use \"use\"",
        "  Ident \"a\"",
        "  Slash \"/\"",
        "  Ident \"b\"",
        "  ColonColon \"::\"",
        "  Ident \"c\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_use_decl_alias() {
    let got = parse_stmt_once("use std::io as io");
    let expected = vec![
        "(UseDecl",
        "  Use \"use\"",
        "  Ident \"std\"",
        "  ColonColon \"::\"",
        "  Ident \"io\"",
        "  As \"as\"",
        "  Ident \"io\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_use_decl_operator() {
    let got = parse_stmt_once("use m::(+)");
    let expected = vec![
        "(UseDecl",
        "  Use \"use\"",
        "  Ident \"m\"",
        "  ColonColon \"::\"",
        "  ParenL \"(\"",
        "  OpName \"+\"",
        "  ParenR \")\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_use_decl_group_operator() {
    let got = parse_stmt_once("use m::{(+), id}");
    let expected = vec![
        "(UseDecl",
        "  Use \"use\"",
        "  Ident \"m\"",
        "  ColonColon \"::\"",
        "  (BraceGroup",
        "    BraceL \"{\"",
        "    ParenL \"(\"",
        "    OpName \"+\"",
        "    ParenR \")\"",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    Ident \"id\"",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_use_decl_glob_without_operator_and_ident() {
    let got = parse_stmt_once("use m::* without (+), id");
    let expected = vec![
        "(UseDecl",
        "  Use \"use\"",
        "  Ident \"m\"",
        "  ColonColon \"::\"",
        "  OpName \"*\"",
        "  Ident \"without\"",
        "  ParenL \"(\"",
        "  OpName \"+\"",
        "  ParenR \")\"",
        "  Comma \",\"",
        "  Ident \"id\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_op_def_nullfix() {
    let got = parse_stmt_once("nullfix (+) = x");
    let expected = vec![
        "(OpDef",
        "  (OpDefHeader",
        "    Nullfix \"nullfix\"",
        "    ParenL \"(\"",
        "    OpName \"+\"",
        "    ParenR \")\"",
        "    Equal \"=\"",
        "  )",
        "  (OpDefBody",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_op_def_prefix() {
    let got = parse_stmt_once("prefix (not) 70 = x");
    let expected = vec![
        "(OpDef",
        "  (OpDefHeader",
        "    Prefix \"prefix\"",
        "    ParenL \"(\"",
        "    OpName \"not\"",
        "    ParenR \")\"",
        "    Number \"70\"",
        "    Equal \"=\"",
        "  )",
        "  (OpDefBody",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_op_def_infix() {
    let got = parse_stmt_once("infix (+) 50 50 = x");
    let expected = vec![
        "(OpDef",
        "  (OpDefHeader",
        "    Infix \"infix\"",
        "    ParenL \"(\"",
        "    OpName \"+\"",
        "    ParenR \")\"",
        "    Number \"50\"",
        "    Number \"50\"",
        "    Equal \"=\"",
        "  )",
        "  (OpDefBody",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_op_def_suffix() {
    let got = parse_stmt_once("suffix (!) 80 = x");
    let expected = vec![
        "(OpDef",
        "  (OpDefHeader",
        "    Suffix \"suffix\"",
        "    ParenL \"(\"",
        "    OpName \"!\"",
        "    ParenR \")\"",
        "    Number \"80\"",
        "    Equal \"=\"",
        "  )",
        "  (OpDefBody",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_op_def_bp_vec() {
    let got = parse_stmt_once("infix (+) 5.0.1 5.0.2 = x");
    let expected = vec![
        "(OpDef",
        "  (OpDefHeader",
        "    Infix \"infix\"",
        "    ParenL \"(\"",
        "    OpName \"+\"",
        "    ParenR \")\"",
        "    Number \"5.0.1\"",
        "    Number \"5.0.2\"",
        "    Equal \"=\"",
        "  )",
        "  (OpDefBody",
        "    (Expr",
        "      Ident \"x\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_pub_use_decl() {
    let got = parse_stmt_once("pub use foo");
    let expected = vec![
        "(UseDecl",
        "  Pub \"pub\"",
        "  Use \"use\"",
        "  Ident \"foo\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_use_group_alias_consumes_closing_brace() {
    let got = parse_stmt_once("use m::{id, other as o}");
    let expected = vec![
        "(UseDecl",
        "  Use \"use\"",
        "  Ident \"m\"",
        "  ColonColon \"::\"",
        "  (BraceGroup",
        "    BraceL \"{\"",
        "    Ident \"id\"",
        "    (Separator",
        "      Comma \",\"",
        "    )",
        "    Ident \"other\"",
        "    As \"as\"",
        "    Ident \"o\"",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_pub_struct_decl() {
    let got = parse_stmt_once("pub struct Foo;");
    let expected = vec![
        "(StructDecl",
        "  Pub \"pub\"",
        "  Struct \"struct\"",
        "  Ident \"Foo\"",
        "  (TypeVars",
        "  )",
        "  Semicolon \";\"",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_binding_multi_arg_pattern() {
    let got = parse_stmt_once("my f x = 1");
    let expected = vec![
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"f\"",
        "      (ApplyML",
        "        (Pattern",
        "          Ident \"x\"",
        "        )",
        "      )",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_binding_number_arg_pattern() {
    let got = parse_stmt_once("my is_zero 0 = true");
    let expected = vec![
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"is_zero\"",
        "      (ApplyML",
        "        (Pattern",
        "          Number \"0\"",
        "        )",
        "      )",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Ident \"true\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_binding_inline_body_ml_apply() {
    let got = parse_stmt_once("my z2 = f z x");
    let expected = vec![
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"z2\"",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Ident \"f\"",
        "      (ApplyML",
        "        (Expr",
        "          Ident \"z\"",
        "        )",
        "      )",
        "      (ApplyML",
        "        (Expr",
        "          Ident \"x\"",
        "        )",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_binding_inline_body_with_block() {
    let got = parse_stmt_once("my x = y with:\n  my y = 1");
    let expected = vec![
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"x\"",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Ident \"y\"",
        "      (WithBlock",
        "        With \"with\"",
        "        Colon \":\"",
        "        (IndentBlock",
        "          (Binding",
        "            (BindingHeader",
        "              My \"my\"",
        "              (Pattern",
        "                Ident \"y\"",
        "              )",
        "              Equal \"=\"",
        "            )",
        "            (BindingBody",
        "              (Expr",
        "                Number \"1\"",
        "              )",
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
fn stmt_binding_block_contains_inline_body_ml_apply() {
    let got = parse_stmt_once("my p z x f =\n  my z2 = f z x\n  z2");
    let expected = vec![
        "(Binding",
        "  (BindingHeader",
        "    My \"my\"",
        "    (Pattern",
        "      Ident \"p\"",
        "      (ApplyML",
        "        (Pattern",
        "          Ident \"z\"",
        "        )",
        "      )",
        "      (ApplyML",
        "        (Pattern",
        "          Ident \"x\"",
        "        )",
        "      )",
        "      (ApplyML",
        "        (Pattern",
        "          Ident \"f\"",
        "        )",
        "      )",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (IndentBlock",
        "      (Binding",
        "        (BindingHeader",
        "          My \"my\"",
        "          (Pattern",
        "            Ident \"z2\"",
        "          )",
        "          Equal \"=\"",
        "        )",
        "        (BindingBody",
        "          (Expr",
        "            Ident \"f\"",
        "            (ApplyML",
        "              (Expr",
        "                Ident \"z\"",
        "              )",
        "            )",
        "            (ApplyML",
        "              (Expr",
        "                Ident \"x\"",
        "              )",
        "            )",
        "          )",
        "        )",
        "      )",
        "      (Expr",
        "        Ident \"z2\"",
        "      )",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_pub_binding_multi_arg_pattern() {
    let got = parse_stmt_once("pub f x = 1");
    let expected = vec![
        "(Binding",
        "  (BindingHeader",
        "    Pub \"pub\"",
        "    (Pattern",
        "      Ident \"f\"",
        "      (ApplyML",
        "        (Pattern",
        "          Ident \"x\"",
        "        )",
        "      )",
        "    )",
        "    Equal \"=\"",
        "  )",
        "  (BindingBody",
        "    (Expr",
        "      Number \"1\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_role_decl_brace_body() {
    let got = parse_stmt_once("role Eq {\n  our eq: Self -> Self -> Bool\n}");
    let expected = vec![
        "(RoleDecl",
        "  Role \"role\"",
        "  (TypeExpr",
        "    Ident \"Eq\"",
        "  )",
        "  (BraceGroup",
        "    BraceL \"{\"",
        "    (Binding",
        "      (BindingHeader",
        "        Our \"our\"",
        "        (Pattern",
        "          Ident \"eq\"",
        "          (TypeAnn",
        "            Colon \":\"",
        "            (TypeExpr",
        "              Ident \"Self\"",
        "              (TypeArrow",
        "                Arrow \"->\"",
        "                (TypeExpr",
        "                  Ident \"Self\"",
        "                  (TypeArrow",
        "                    Arrow \"->\"",
        "                    (TypeExpr",
        "                      Ident \"Bool\"",
        "                    )",
        "                  )",
        "                )",
        "              )",
        "            )",
        "          )",
        "        )",
        "      )",
        "    )",
        "    (Separator",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_impl_decl_brace_body() {
    let got = parse_stmt_once("impl Eq Int {\n  our eq = id\n}");
    let expected = vec![
        "(ImplDecl",
        "  Impl \"impl\"",
        "  (TypeExpr",
        "    Ident \"Eq\"",
        "    (TypeApply",
        "      (TypeExpr",
        "        Ident \"Int\"",
        "      )",
        "    )",
        "  )",
        "  (BraceGroup",
        "    BraceL \"{\"",
        "    (Binding",
        "      (BindingHeader",
        "        Our \"our\"",
        "        (Pattern",
        "          Ident \"eq\"",
        "        )",
        "        Equal \"=\"",
        "      )",
        "      (BindingBody",
        "        (Expr",
        "          Ident \"id\"",
        "        )",
        "      )",
        "    )",
        "    (Separator",
        "    )",
        "    BraceR \"}\"",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_struct_decl_indent_body() {
    let got = parse_stmt_once("struct S:\n  x: Int\n  y: String");
    let expected = vec![
        "(StructDecl",
        "  Struct \"struct\"",
        "  Ident \"S\"",
        "  (TypeVars",
        "  )",
        "  Colon \":\"",
        "  (StructField",
        "    Ident \"x\"",
        "    Colon \":\"",
        "    (TypeExpr",
        "      Ident \"Int\"",
        "    )",
        "  )",
        "  (StructField",
        "    Ident \"y\"",
        "    Colon \":\"",
        "    (TypeExpr",
        "      Ident \"String\"",
        "    )",
        "  )",
        ")",
    ];
    assert_eq!(got, expected);
}

#[test]
fn stmt_role_decl_indent_body() {
    let got = parse_stmt_once("role Printable:\n  our print: Self -> ()");
    let expected = vec![
        "(RoleDecl",
        "  Role \"role\"",
        "  (TypeExpr",
        "    Ident \"Printable\"",
        "  )",
        "  Colon \":\"",
        "  (IndentBlock",
        "    (Binding",
        "      (BindingHeader",
        "        Our \"our\"",
        "        (Pattern",
        "          Ident \"print\"",
        "          (TypeAnn",
        "            Colon \":\"",
        "            (TypeExpr",
        "              Ident \"Self\"",
        "              (TypeArrow",
        "                Arrow \"->\"",
        "                (TypeExpr",
        "                  (TypeParenGroup",
        "                    ParenL \"(\"",
        "                    ParenR \")\"",
        "                  )",
        "                )",
        "              )",
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
fn stmt_binding_case_body_with_indented_arms() {
    let got = parse_stmt_once(
        "my fold xs z f = case std::list::view_raw xs:\n  std::list::list_view::empty -> z\n  std::list::list_view::leaf x -> f z x\n  std::list::list_view::node (left, right) ->\n    my z2 = fold left z f\n    fold right z2 f",
    );
    assert!(got.iter().any(|line| line.contains("(CaseArm")));
    assert!(got.iter().any(|line| line.contains("(IndentBlock")));
    assert!(got.iter().any(|line| line.contains("(Binding")));
    assert!(got.iter().any(|line| line.contains("Ident \"z2\"")));
    assert!(got.iter().any(|line| line.contains("Ident \"fold\"")));
}

#[test]
fn stmt_binding_case_body_with_indented_arms_in_module_loop() {
    let got = parse_stmt_all(
        "my fold xs z f = case std::list::view_raw xs:\n  std::list::list_view::empty -> z\n  std::list::list_view::leaf x -> f z x\n  std::list::list_view::node (left, right) ->\n    my z2 = fold left z f\n    fold right z2 f\n",
    );
    assert!(got.iter().any(|line| line.contains("(CaseArm")));
    assert!(got.iter().any(|line| line.contains("(IndentBlock")));
    assert!(got.iter().any(|line| line.contains("(Binding")));
}

#[test]
fn stmt_binding_case_body_with_indented_arms_green_tree_keeps_case_arms() {
    let source = "my fold xs z f = case std::list::view_raw xs:\n  std::list::list_view::empty -> z\n  std::list::list_view::leaf x -> f z x\n  std::list::list_view::node (left, right) ->\n    my z2 = fold left z f\n    fold right z2 f\n";
    let single = parse_stmt_once_green(source);
    let all = parse_stmt_all_green(source);
    let module = parse_module_green(source);
    eprintln!("parser module tree = {module:#?}");
    let single_arms = single
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::CaseArm)
        .count();
    let all_arms = all
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::CaseArm)
        .count();
    let module_arms = module
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::CaseArm)
        .count();
    assert_eq!(single_arms, 3);
    assert_eq!(all_arms, 3);
    assert_eq!(module_arms, 3);
}

#[test]
fn stmt_binding_case_body_with_guarded_arms_keeps_case_arms() {
    let source = "my f(x: bool) = case 1:\n  1 if x -> 1\n  _ -> 0\n";
    let got = parse_stmt_once(source);
    assert!(got.iter().any(|line| line.contains("(CaseArm")));
    assert!(got.iter().any(|line| line.contains("(CaseGuard")));
}
