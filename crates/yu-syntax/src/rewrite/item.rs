#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct LeadingTrivia(pub(super) Box<[Trivia]>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Trivia {
    pub(super) kind: TriviaKind,
    pub(super) text: Box<str>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TriviaKind {
    Whitespace,
    Newline,
    LineComment,
    BlockComment,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TokenKind {
    Identifier,
    SigilIdentifier,
    Integer,
    Operator,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semicolon,
    Dot,
    DotDot,
    Arrow,
    Colon,
    Equals,
    Forall,
    EffectRowApostrophe,
    PolymorphicVariantColon,
    PatternSymbolColon,
    PathSeparator,
    Pipe,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Token {
    pub(super) kind: TokenKind,
    pub(super) text: Box<str>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct OperatorToken {
    pub(super) text: Box<str>,
    pub(super) use_: OperatorUse,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum OperatorUse {
    Prefix(BindingPower),
    Infix {
        left: BindingPower,
        right: BindingPower,
    },
    Suffix(BindingPower),
    Nullfix,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Payload {
    Token(Token),
    Operator(OperatorToken),
    Boundary(PendingBoundary),
    Eof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PendingBoundary {
    inspected: std::ops::Range<usize>,
    kind: Boundary,
}

impl PendingBoundary {
    pub(super) fn new(inspected: std::ops::Range<usize>, kind: Boundary) -> Self {
        assert!(inspected.start <= inspected.end);
        Self { inspected, kind }
    }

    pub(super) fn coordinate(&self) -> usize {
        self.inspected.start
    }

    pub(super) fn inspected(&self) -> &std::ops::Range<usize> {
        &self.inspected
    }

    pub(super) fn kind(&self) -> &Boundary {
        &self.kind
    }

    pub(super) fn into_kind(self) -> Boundary {
        self.kind
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Delimiter {
    Parenthesis,
    Bracket,
    Brace,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct LayoutEvidence {
    pub(super) baseline: usize,
    pub(super) indentation: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Boundary {
    Close(Delimiter),
    BorrowedClose(BorrowedTarget),
    Dedent(LayoutEvidence),
    Stop(StopKind),
    EofAfterTrivia,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum BorrowedTarget {
    Delimiter(Delimiter),
    YumarkFence(Box<super::yumark::FenceCloseFacts>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StopKind {
    Newline,
    Comma,
    Semicolon,
    Colon,
    LeftBrace,
    Elsif,
    Else,
    RightParenthesis,
    RightBracket,
    RightBrace,
    Equal,
    Arrow,
    ArmGuardIf,
    ArmGuardWhere,
    With,
    Derives,
    Via,
    In,
    Impl,
    LeftParenthesis,
    Pipe,
    YumarkFence(Box<super::yumark::YumarkFenceTransition>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ForeignKind {
    YmQuotePrefix,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ForeignSplit {
    pub(super) offset: usize,
    pub(super) length: usize,
    pub(super) kind: ForeignKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FragmentError {
    Empty,
    Overflow,
    OutOfOrder,
    Overlap,
    OutsidePhysicalText,
    InvalidTextBoundary,
    CrossesPartBoundary,
    PhysicalLengthMismatch,
    AlreadyAttached,
}

impl ForeignSplit {
    pub(super) fn quote_prefix(offset: usize, length: usize) -> Self {
        Self {
            offset,
            length,
            kind: ForeignKind::YmQuotePrefix,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub(super) struct PendingFragments {
    physical: std::ops::Range<usize>,
    foreign: Box<[ForeignSplit]>,
}

impl PendingFragments {
    /// Lazily creates the scanner-local vector at the first accepted split.
    pub(super) fn record(
        pending: &mut Option<Vec<ForeignSplit>>,
        split: ForeignSplit,
    ) -> Result<(), FragmentError> {
        if split.length == 0 {
            return Err(FragmentError::Empty);
        }
        let split_end = split
            .offset
            .checked_add(split.length)
            .ok_or(FragmentError::Overflow)?;
        if let Some(previous) = pending.as_ref().and_then(|splits| splits.last()) {
            if split.offset < previous.offset {
                return Err(FragmentError::OutOfOrder);
            }
            let previous_end = previous
                .offset
                .checked_add(previous.length)
                .ok_or(FragmentError::Overflow)?;
            if previous_end > split.offset {
                return Err(FragmentError::Overlap);
            }
        }
        debug_assert!(split_end > split.offset);
        pending.get_or_insert_with(Vec::new).push(split);
        Ok(())
    }

    /// Completes one item with one move and one boxed-slice conversion.
    pub(super) fn finish(
        pending: Option<Vec<ForeignSplit>>,
        physical_origin: usize,
        physical_length: usize,
    ) -> Result<Option<Self>, FragmentError> {
        let Some(foreign) = pending.filter(|foreign| !foreign.is_empty()) else {
            return Ok(None);
        };
        let physical_end = physical_origin
            .checked_add(physical_length)
            .ok_or(FragmentError::Overflow)?;
        let mut previous_offset = None;
        let mut previous_end = physical_origin;
        for split in &foreign {
            if split.length == 0 {
                return Err(FragmentError::Empty);
            }
            let split_end = split
                .offset
                .checked_add(split.length)
                .ok_or(FragmentError::Overflow)?;
            if previous_offset.is_some_and(|offset| split.offset < offset) {
                return Err(FragmentError::OutOfOrder);
            }
            if split.offset < previous_end {
                return Err(if split.offset < physical_origin {
                    FragmentError::OutsidePhysicalText
                } else {
                    FragmentError::Overlap
                });
            }
            if split_end > physical_end {
                return Err(FragmentError::OutsidePhysicalText);
            }
            previous_offset = Some(split.offset);
            previous_end = split_end;
        }
        Ok(Some(Self {
            physical: physical_origin..physical_end,
            foreign: foreign.into_boxed_slice(),
        }))
    }

    pub(super) fn physical(&self) -> &std::ops::Range<usize> {
        &self.physical
    }

    pub(super) fn foreign(&self) -> &[ForeignSplit] {
        &self.foreign
    }
}

/// A scanned logical item owns every byte it retains.
#[derive(Debug, Eq, PartialEq)]
pub(super) struct Item {
    pub(super) leading: LeadingTrivia,
    pub(super) payload: Payload,
    fragments: Option<PendingFragments>,
}

impl Item {
    pub(super) fn plain(leading: LeadingTrivia, payload: Payload) -> Self {
        Self {
            leading,
            payload,
            fragments: None,
        }
    }

    pub(super) fn with_fragments(
        &mut self,
        fragments: PendingFragments,
    ) -> Result<(), FragmentError> {
        if self.fragments.is_some() {
            return Err(FragmentError::AlreadyAttached);
        }
        self.validate_fragments(&fragments)?;
        self.fragments = Some(fragments);
        Ok(())
    }

    pub(super) fn fragments(&self) -> Option<&PendingFragments> {
        self.fragments.as_ref()
    }

    pub(super) fn fragmented_parts(&self) -> Option<FragmentedParts<'_>> {
        let fragments = self.fragments.as_ref()?;
        Some(FragmentedParts {
            item: self,
            fragments,
            part: 0,
            offset: fragments.physical.start,
            split: 0,
        })
    }

    fn validate_fragments(&self, fragments: &PendingFragments) -> Result<(), FragmentError> {
        let total = self
            .constituent_texts()
            .try_fold(0usize, |length, text| length.checked_add(text.len()))
            .ok_or(FragmentError::Overflow)?;
        if fragments.physical.end - fragments.physical.start != total {
            return Err(FragmentError::PhysicalLengthMismatch);
        }

        let mut part_start = fragments.physical.start;
        let mut split_index = 0;
        for text in self.constituent_texts() {
            let part_end = part_start
                .checked_add(text.len())
                .ok_or(FragmentError::Overflow)?;
            while let Some(split) = fragments.foreign.get(split_index)
                && split.offset < part_end
            {
                let split_end = split
                    .offset
                    .checked_add(split.length)
                    .ok_or(FragmentError::Overflow)?;
                if split.offset < part_start || split_end > part_end {
                    return Err(FragmentError::CrossesPartBoundary);
                }
                let start = split.offset - part_start;
                let end = split_end - part_start;
                if !text.is_char_boundary(start) || !text.is_char_boundary(end) {
                    return Err(FragmentError::InvalidTextBoundary);
                }
                split_index += 1;
            }
            part_start = part_end;
        }
        if split_index != fragments.foreign.len() {
            return Err(FragmentError::OutsidePhysicalText);
        }
        Ok(())
    }

    fn constituent_texts(&self) -> impl Iterator<Item = &str> {
        self.leading
            .0
            .iter()
            .map(|trivia| &*trivia.text)
            .chain(self.payload_text())
    }

    fn payload_text(&self) -> Option<&str> {
        match &self.payload {
            Payload::Token(token) => Some(&token.text),
            Payload::Operator(operator) => Some(&operator.text),
            Payload::Boundary(_) | Payload::Eof => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ItemTextPart {
    LeadingTrivia(usize),
    PayloadToken,
    PayloadOperator,
}

pub(super) struct FragmentedPart<'item> {
    pub(super) kind: ItemTextPart,
    pub(super) physical: std::ops::Range<usize>,
    pub(super) text: &'item str,
    pub(super) foreign: &'item [ForeignSplit],
}

pub(super) struct FragmentedParts<'item> {
    item: &'item Item,
    fragments: &'item PendingFragments,
    part: usize,
    offset: usize,
    split: usize,
}

impl<'item> Iterator for FragmentedParts<'item> {
    type Item = FragmentedPart<'item>;

    fn next(&mut self) -> Option<Self::Item> {
        let (kind, text) = if let Some(trivia) = self.item.leading.0.get(self.part) {
            (ItemTextPart::LeadingTrivia(self.part), &*trivia.text)
        } else if self.part == self.item.leading.0.len() {
            match &self.item.payload {
                Payload::Token(token) => (ItemTextPart::PayloadToken, &*token.text),
                Payload::Operator(operator) => (ItemTextPart::PayloadOperator, &*operator.text),
                Payload::Boundary(_) | Payload::Eof => return None,
            }
        } else {
            return None;
        };

        let start = self.offset;
        let end = start + text.len();
        let first_split = self.split;
        while self
            .fragments
            .foreign
            .get(self.split)
            .is_some_and(|split| split.offset < end)
        {
            self.split += 1;
        }
        self.part += 1;
        self.offset = end;
        Some(FragmentedPart {
            kind,
            physical: start..end,
            text,
            foreign: &self.fragments.foreign[first_split..self.split],
        })
    }
}
use crate::operator::BindingPower;
