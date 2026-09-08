//! Source-free ownership of a sequence at the current lexical depth.

pub(in crate::parser) type SequenceContext = Option<SequenceOwner>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::parser) enum SequenceOwner {
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
