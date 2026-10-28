//! Source-free ownership of a sequence at the current lexical depth.

pub(crate) type SequenceContext = Option<SequenceOwner>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SequenceOwner {
    RootStatement,
    VirtualStatement,
    RecordPattern,
    RuleExpressionList,
    Parenthesized,
    Call,
    Index,
    ProjectionTuple,
    ProjectionRecord,
    Colon,
    IndentedStatement,
    BracedStatement,
    CaseInline,
    CaseIndented,
    CatchInline,
    CatchIndented,
    CatchBraced,
    If,
}
