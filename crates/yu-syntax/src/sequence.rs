//! Sequence ownership and optional declaration-doc boundary at the current lexical depth.

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
    IndentedActOperation,
    BracedActOperation,
    ActOperation,
    WithDeclarationDoc {
        owner: &'static SequenceOwner,
        doc: DeclarationDocContext,
    },
}

/// Created by the declaration owner only when `--` is not an operator.
/// A fresh nested sequence has no permission to terminate at its outer doc.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DeclarationDocContext {
    pub(crate) start_line_end: usize,
}

impl DeclarationDocContext {
    pub(crate) fn new(source: &str, origin: usize) -> Self {
        Self {
            start_line_end: origin + source.find(['\r', '\n']).unwrap_or(source.len()),
        }
    }
}

impl SequenceOwner {
    pub(crate) fn with_declaration_doc(self, doc: Option<DeclarationDocContext>) -> Self {
        let Some(doc) = doc else {
            return self.without_declaration_doc();
        };
        // References point only to these static, undecorated owner values.
        let owner = match self.without_declaration_doc() {
            Self::RootStatement => &Self::RootStatement,
            Self::VirtualStatement => &Self::VirtualStatement,
            Self::RecordPattern => &Self::RecordPattern,
            Self::RuleExpressionList => &Self::RuleExpressionList,
            Self::Parenthesized => &Self::Parenthesized,
            Self::List => &Self::List,
            Self::Call => &Self::Call,
            Self::Index => &Self::Index,
            Self::ProjectionTuple => &Self::ProjectionTuple,
            Self::ProjectionRecord => &Self::ProjectionRecord,
            Self::Colon => &Self::Colon,
            Self::IndentedStatement => &Self::IndentedStatement,
            Self::BracedStatement => &Self::BracedStatement,
            Self::CaseInline => &Self::CaseInline,
            Self::CaseIndented => &Self::CaseIndented,
            Self::CatchInline => &Self::CatchInline,
            Self::CatchIndented => &Self::CatchIndented,
            Self::CatchBraced => &Self::CatchBraced,
            Self::If => &Self::If,
            Self::IndentedOwnerField => &Self::IndentedOwnerField,
            Self::BracedOwnerField => &Self::BracedOwnerField,
            Self::OwnerField => &Self::OwnerField,
            Self::IndentedActOperation => &Self::IndentedActOperation,
            Self::BracedActOperation => &Self::BracedActOperation,
            Self::ActOperation => &Self::ActOperation,
            Self::WithDeclarationDoc { .. } => unreachable!(),
        };
        Self::WithDeclarationDoc { owner, doc }
    }

    pub(crate) fn declaration_doc(self) -> Option<DeclarationDocContext> {
        match self {
            Self::WithDeclarationDoc { doc, .. } => Some(doc),
            _ => None,
        }
    }

    pub(crate) fn without_declaration_doc(self) -> Self {
        match self {
            Self::WithDeclarationDoc { owner, .. } => *owner,
            owner => owner,
        }
    }

    pub(crate) fn admits_doc_comment(self) -> bool {
        matches!(
            self.without_declaration_doc(),
            Self::RootStatement
                | Self::VirtualStatement
                | Self::IndentedStatement
                | Self::BracedStatement
                | Self::CaseInline
                | Self::CatchInline
                | Self::If
        )
    }

    pub(crate) fn admits_operation_where(self) -> bool {
        matches!(
            self.without_declaration_doc(),
            Self::IndentedActOperation | Self::BracedActOperation | Self::ActOperation
        )
    }
}

pub(crate) fn admits_doc_comment(context: SequenceContext) -> bool {
    context.is_some_and(SequenceOwner::admits_doc_comment)
}
