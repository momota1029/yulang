use im::HashSet;
use reborrow_generic::Reborrow;

use crate::lex::SyntaxKind;
// use crate::old_mark::scan::YmPending;
use crate::op::OpTable;
use crate::sink::EventSink;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum YumarkCodeKind {
    Plain,
    Yulang,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct YumarkOption {
    pub code_kind: YumarkCodeKind,
}

#[derive(Debug)]
pub struct State<S: EventSink> {
    pub sink: S,
    pub line_indent: usize,
    pub ops: OpTable,
    // pub pending_ym: Option<YmPending>,
}

impl<S: EventSink + Default> Default for State<S> {
    fn default() -> Self {
        Self {
            sink: S::default(),
            line_indent: 0,
            ops: OpTable::default(),
            // pending_ym: None,
        }
    }
}

#[derive(Debug, Reborrow)]
pub struct Env<'a, S: EventSink> {
    pub state: &'a mut State<S>,
    pub indent: usize,
    pub mark_quote_depth: usize,
    #[reborrow(clone)]
    pub yumark_option: YumarkOption,
    pub inline: bool,
    pub ml_arg: bool,
    #[reborrow(clone)]
    pub stop: HashSet<SyntaxKind>,
}
impl<'a, S: EventSink> Env<'a, S> {
    pub fn new(
        state: &'a mut State<S>,
        ops: OpTable,
        indent: usize,
        stop: HashSet<SyntaxKind>,
    ) -> Self {
        state.ops = ops;
        Self {
            state,
            indent,
            mark_quote_depth: 0,
            yumark_option: YumarkOption {
                code_kind: YumarkCodeKind::Plain,
            },
            ml_arg: false,
            inline: false,
            stop,
        }
    }
}

pub type In<'a, 'b, I, S> = chasa::prelude::In<'a, I, Env<'b, S>>;
