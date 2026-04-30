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

pub trait EventInput: SeqInput<Item = char, Seq: AsRef<str>> + Front {}

impl<I> EventInput for I where I: SeqInput<Item = char, Seq: AsRef<str>> + Front {}

// ── 公開ユーティリティ ────────────────────────────────────────────────────────

/// ソース文字列をパースして Rowan の `GreenNode`（Root ノード）を返す。
/// `SyntaxNode::new_root(green)` で走査可能な CST が得られる。
pub fn parse_module_to_green(source: &str) -> rowan::GreenNode {
    parse_module_to_green_with_ops(source, crate::op::standard_op_table())
}

pub fn parse_module_to_green_with_ops(source: &str, ops: crate::op::OpTable) -> rowan::GreenNode {
    use chasa::error::LatestSink;
    use chasa::input::{Input as _, IsCut};
    use either::Either;
    use im::HashSet;
    use reborrow_generic::Reborrow as _;

    use crate::context::{Env, State};
    use crate::lex::{SyntaxKind, TriviaInfo};
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

        let leading = i
            .run(scan_trivia)
            .map(|t| t.info())
            .unwrap_or(TriviaInfo::None);
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
                Some(Either::Right(_)) => break,
            }
        }
    }

    state.sink.finish(); // Root
    state.sink.finish_green()
}
