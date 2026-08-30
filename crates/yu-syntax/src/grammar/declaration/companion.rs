use std::ops::Range;

use crate::grammar::expression::Statement;

use super::{DerivesClause, Recovered};

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeclarationCompanion<'source> {
    pub(super) keyword: Range<usize>,
    pub(super) form: DeclarationCompanionForm<'source>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationCompanionForm<'source> {
    Colon {
        colon: Recovered<Range<usize>>,
        body: Recovered<DeclarationCompanionColonBody<'source>>,
    },
    Braced {
        open: Range<usize>,
        items: Vec<Recovered<DeclarationCompanionItem<'source>>>,
        close: Recovered<Range<usize>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationCompanionColonBody<'source> {
    Inline {
        item: Box<DeclarationCompanionItem<'source>>,
        semicolon: Option<Range<usize>>,
    },
    Indented(DeclarationCompanionIndentedBody<'source>),
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeclarationCompanionIndentedBody<'source> {
    pub(super) base_indent: usize,
    pub(super) block_indent: usize,
    pub(super) items: Vec<Recovered<DeclarationCompanionItem<'source>>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationCompanionItem<'source> {
    Statement(Box<Statement<'source>>),
    Derives(Vec<DerivesClause<'source>>),
}
