//! Source-free ownership of a sequence at the current lexical depth.

pub(crate) type SequenceContext = Option<SequenceOwner>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SequenceOwner {
    RootStatement,
    VirtualStatement,
    RecordPattern,
    RuleExpressionList,
    Parenthesized,
    List,
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
    IndentedOwnerField,
    BracedOwnerField,
    OwnerField,
}

impl SequenceOwner {
    pub(crate) fn admits_doc_comment(self) -> bool {
        matches!(
            self,
            Self::RootStatement
                | Self::VirtualStatement
                | Self::IndentedStatement
                | Self::BracedStatement
                | Self::CaseInline
                | Self::CatchInline
                | Self::If
        )
    }
}

pub(crate) fn admits_doc_comment(context: SequenceContext) -> bool {
    context.is_some_and(SequenceOwner::admits_doc_comment)
}
