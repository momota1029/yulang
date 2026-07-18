pub mod context;
pub mod expr;
pub mod lex;
pub mod mark;
pub mod op;
pub mod parse;
pub mod pat;
pub mod scan;
pub mod sink;
pub mod stmt;
pub mod string;
pub mod typ;

use chasa::back::Front;
use chasa::input::SeqInput;
use lex::{SyntaxKind, TriviaInfo};
use sink::GreenSinkStats;
use std::time::{Duration, Instant};

pub trait EventInput: SeqInput<Item = char, Seq: AsRef<str>> + Front {}

impl<I> EventInput for I where I: SeqInput<Item = char, Seq: AsRef<str>> + Front {}

// ── 公開ユーティリティ ────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GreenParseMeasurement {
    pub elapsed: Duration,
    pub sink: GreenSinkStats,
}

/// ソース文字列をパースして Rowan の `GreenNode`（Root ノード）を返す。
/// `SyntaxNode::new_root(green)` で走査可能な CST が得られる。
pub fn parse_module_to_green(source: &str) -> rowan::GreenNode {
    parse_module_to_green_with_ops(source, crate::op::standard_op_table())
}

pub fn parse_module_to_green_measured(source: &str) -> (rowan::GreenNode, GreenParseMeasurement) {
    parse_module_to_green_with_ops_measured(source, crate::op::standard_op_table())
}

pub fn parse_module_to_green_with_ops(source: &str, ops: crate::op::OpTable) -> rowan::GreenNode {
    parse_module_to_green_with_ops_inner(source, ops).0
}

pub fn parse_module_to_green_with_ops_measured(
    source: &str,
    ops: crate::op::OpTable,
) -> (rowan::GreenNode, GreenParseMeasurement) {
    let started = Instant::now();
    let (green, sink) = parse_module_to_green_with_ops_inner(source, ops);
    (
        green,
        GreenParseMeasurement {
            elapsed: started.elapsed(),
            sink,
        },
    )
}

fn parse_module_to_green_with_ops_inner(
    source: &str,
    ops: crate::op::OpTable,
) -> (rowan::GreenNode, GreenSinkStats) {
    use chasa::error::LatestSink;
    use chasa::input::{Input as _, IsCut};
    use either::Either;
    use im::HashSet;
    use reborrow_generic::Reborrow as _;

    use crate::context::{Env, State};
    use crate::parse::emit_invalid;
    use crate::scan::trivia::scan_trivia;
    use crate::sink::{EventSink as _, GreenSink};
    use crate::stmt::parse_statement;

    let mut state = State::<GreenSink>::default();
    state.sink.start(SyntaxKind::Root);

    {
        let mut input = source.with_counter(0usize);
        let mut errors = LatestSink::new();
        let mut cut_flag = false;
        let base_in = chasa::prelude::In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
        let env = Env::new(&mut state, ops, 0, HashSet::new());
        let mut i = base_in.set_env(env);

        let leading_trivia = i.run(scan_trivia).unwrap_or_else(crate::lex::Trivia::empty);
        let leading = leading_trivia.info();
        i.env.state.sink.trivia(&leading_trivia);
        let mut info = leading;
        loop {
            match parse_statement(info, i.rb()) {
                None => break,
                Some(Either::Left(next_info)) => {
                    if matches!(next_info, TriviaInfo::None) {
                        break;
                    }
                    info = next_info;
                }
                Some(Either::Right(stop)) => {
                    let next_info = stop.trailing_trivia_info();
                    if stop.kind == SyntaxKind::Semicolon {
                        i.env.state.sink.start(SyntaxKind::Separator);
                        i.env.state.sink.lex(&stop);
                        i.env.state.sink.finish();
                    } else {
                        emit_invalid(i.rb(), stop);
                    }
                    info = next_info;
                }
            }
        }
    }

    state.sink.finish(); // Root
    state.sink.finish_green_with_stats()
}

/// ヘッダ先読み: 先頭の use / op_def 宣言だけをパースした CST を返す。
/// body には踏み込まず、最初の式・定義文で停止する。`sources` がファイル間の
/// op テーブルと use 依存グラフを組むために使う（standard_op_table 始まりで、
/// 自前 op は parse 中に `update_op_table` が育てる）。
pub fn parse_header_to_green(source: &str) -> rowan::GreenNode {
    parse_header_to_green_inner(source, crate::op::standard_op_table()).0
}

pub fn parse_header_to_green_measured(source: &str) -> (rowan::GreenNode, GreenParseMeasurement) {
    let ops = crate::op::standard_op_table();
    let started = Instant::now();
    let (green, sink) = parse_header_to_green_inner(source, ops);
    (
        green,
        GreenParseMeasurement {
            elapsed: started.elapsed(),
            sink,
        },
    )
}

fn parse_header_to_green_inner(
    source: &str,
    ops: crate::op::OpTable,
) -> (rowan::GreenNode, GreenSinkStats) {
    use chasa::error::LatestSink;
    use chasa::input::{Input as _, IsCut};
    use im::HashSet;
    use reborrow_generic::Reborrow as _;

    use crate::context::{Env, State};
    use crate::scan::trivia::scan_trivia;
    use crate::sink::{EventSink as _, GreenSink};
    use crate::stmt::{HeaderStep, parse_header_statement};

    let mut state = State::<GreenSink>::default();
    state.sink.start(SyntaxKind::Root);

    {
        let mut input = source.with_counter(0usize);
        let mut errors = LatestSink::new();
        let mut cut_flag = false;
        let base_in = chasa::prelude::In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
        let mut env = Env::new(&mut state, ops, 0, HashSet::new());
        env.header_only = true;
        let mut i = base_in.set_env(env);

        let leading_trivia = i.run(scan_trivia).unwrap_or_else(crate::lex::Trivia::empty);
        let leading = leading_trivia.info();
        i.env.state.sink.trivia(&leading_trivia);
        let mut info = leading;
        loop {
            match parse_header_statement(info, i.rb()) {
                None => break,
                Some(HeaderStep::Continue(next_info)) => {
                    if matches!(next_info, TriviaInfo::None) {
                        break;
                    }
                    info = next_info;
                }
                Some(HeaderStep::Stop) => break,
            }
        }
    }

    state.sink.finish(); // Root
    state.sink.finish_green_with_stats()
}

#[cfg(test)]
mod tests {
    use rowan::{NodeOrToken, SyntaxNode};

    use crate::sink::YulangLanguage;

    use super::*;

    #[test]
    fn header_parse_collects_ops_and_stops_at_def() {
        let source = "infix (<+>) 50 50 = a b\ninfix (<*>) 60 60 = c d\nmy main = 1\n";
        let root = SyntaxNode::<YulangLanguage>::new_root(parse_header_to_green(source));
        let text = root.text().to_string();
        // 先頭の op はどちらも拾う（body は読み捨てられる）
        assert!(text.contains("<+>"), "first op missing: {text:?}");
        assert!(text.contains("<*>"), "second op missing: {text:?}");
        // 最初の定義文 `my main` で止まる（CST に取り込まない）
        assert!(!text.contains("main"), "should stop before def: {text:?}");
    }

    #[test]
    fn header_parse_stops_before_raw_catch_brace_scrutinee() {
        for source in ["catch {:", "catch {:\n"] {
            let root = SyntaxNode::<YulangLanguage>::new_root(parse_header_to_green(source));
            assert_eq!(root.text().to_string(), "");
        }
    }

    #[test]
    fn parse_module_recovers_raw_catch_brace_scrutinee() {
        for source in ["catch {:", "catch {:\n"] {
            let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green(source));
            assert_eq!(root.text().to_string(), source);
            assert!(
                root.descendants()
                    .any(|node| node.kind() == SyntaxKind::CatchExpr),
                "catch expression should remain visible in recovered CST"
            );
        }
    }

    #[test]
    fn parse_module_keeps_leading_line_comment_in_cst() {
        let source = "// note\nmy value = 1\n";
        let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green(source));
        let tokens = root
            .descendants_with_tokens()
            .filter_map(NodeOrToken::into_token)
            .map(|token| {
                (
                    token.kind(),
                    token.text().to_string(),
                    usize::from(token.text_range().start()),
                )
            })
            .collect::<Vec<_>>();

        assert!(tokens.contains(&(SyntaxKind::LineComment, "// note".to_string(), 0)));
        assert!(tokens.contains(&(SyntaxKind::My, "my".to_string(), 8)));
    }

    #[test]
    fn parse_module_keeps_leading_block_comment_in_cst() {
        let source = "/* note */\nmy value = 1\n";
        let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green(source));
        let my = root
            .descendants_with_tokens()
            .filter_map(NodeOrToken::into_token)
            .find(|token| token.kind() == SyntaxKind::My)
            .expect("my token");

        assert_eq!(
            usize::from(my.text_range().start()),
            source.find("my").unwrap()
        );
    }

    #[test]
    fn parse_module_preserves_line_doc_comment_text_ranges() {
        let source = "-- doc\nmy value = 1\n";
        let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green(source));
        let my = root
            .descendants_with_tokens()
            .filter_map(NodeOrToken::into_token)
            .find(|token| token.kind() == SyntaxKind::My)
            .expect("my token");

        assert_eq!(root.text().to_string(), source);
        assert_eq!(
            usize::from(my.text_range().start()),
            source.find("my").unwrap()
        );
    }

    #[test]
    fn characterizes_physical_line_docs_as_independent_declarations() {
        for (source, expected_declarations) in [
            ("-- first\n-- second\nmy value = 1\n", 2),
            ("-- first\r\n-- second\r\nmy value = 1\r\n", 2),
            ("-- first\n--\n-- second\nmy value = 1\n", 3),
        ] {
            let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green(source));
            let declarations = root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::DocCommentDecl)
                .collect::<Vec<_>>();

            assert_eq!(root.text().to_string(), source);
            assert_eq!(declarations.len(), expected_declarations, "{source:?}");
            assert!(declarations.iter().all(|decl| {
                decl.descendants()
                    .filter(|node| node.kind() == SyntaxKind::YmDoc)
                    .count()
                    == 1
            }));
        }
    }

    #[test]
    fn characterizes_split_line_doc_inline_syntax_as_physically_bounded() {
        let source = "-- [link\n-- here](add)\nmy value = 1\n";
        let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green(source));
        let declarations = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::DocCommentDecl)
            .collect::<Vec<_>>();

        // Recovery closes the incomplete inline node at the physical doc
        // boundary and currently duplicates its buffered text/trivia.
        assert_eq!(
            root.text().to_string(),
            "-- [linklink\n\n-- here](add)\nmy value = 1\n"
        );
        assert_eq!(declarations.len(), 2);
        assert_eq!(
            declarations[0]
                .descendants()
                .find(|node| node.kind() == SyntaxKind::YmInlineExpr)
                .expect("first physical line has an incomplete inline node")
                .text()
                .to_string(),
            "[linklink\n"
        );
        assert!(
            declarations[1]
                .descendants()
                .all(|node| node.kind() != SyntaxKind::YmInlineExpr),
            "the second physical line cannot complete the first declaration's inline node"
        );
    }

    #[test]
    fn parse_module_preserves_block_doc_comment_text_ranges() {
        let source =
            "---\n# Title\nA *soft* doc.\n\n- item\n```text\nbody\n```\n---\nmy value = 1\n";
        let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green(source));
        let my = root
            .descendants_with_tokens()
            .filter_map(NodeOrToken::into_token)
            .find(|token| token.kind() == SyntaxKind::My)
            .expect("my token");

        assert_eq!(root.text().to_string(), source);
        assert_eq!(
            usize::from(my.text_range().start()),
            source.find("my").unwrap()
        );
    }
}
