use rowan::GreenNodeBuilder;

use crate::{operator::BindingPower, syntax_kind::SyntaxKind};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct LeadingTrivia(Box<[Trivia]>);

impl LeadingTrivia {
    pub(super) fn ordinary(parts: Box<[Trivia]>) -> Self {
        Self(parts)
    }

    pub(super) fn view(&self) -> LeadingView<'_> {
        LeadingView {
            physical: &self.0,
            first_unemitted: 0,
        }
    }

    pub(super) fn ordinary_parts(&self) -> impl Iterator<Item = &Trivia> {
        self.0.iter()
    }

    pub(super) fn has_ordinary_trivia(&self) -> bool {
        self.ordinary_parts().next().is_some()
    }

    pub(super) fn is_grammar_empty(&self) -> bool {
        !self.has_ordinary_trivia()
    }

    pub(super) fn is_adjacent(&self) -> bool {
        self.is_grammar_empty()
    }

    pub(super) fn has_ordinary_newline(&self) -> bool {
        self.ordinary_parts()
            .any(|part| part.kind == TriviaKind::Newline)
    }

    pub(super) fn indentation_after_newline(&self) -> Option<usize> {
        let mut saw_newline = false;
        let mut at_line_start = false;
        let mut indentation = 0usize;
        for part in self.ordinary_parts() {
            match part.kind {
                TriviaKind::Newline => {
                    saw_newline = true;
                    at_line_start = true;
                    indentation = 0;
                }
                TriviaKind::Whitespace if at_line_start => {
                    indentation += part.text.chars().count();
                }
                TriviaKind::YmQuotePrefix => {
                    unreachable!("ordinary parts exclude quote prefixes")
                }
                _ => at_line_start = false,
            }
        }
        saw_newline.then_some(indentation)
    }

    pub(super) fn emit(&self, builder: &mut GreenNodeBuilder<'static>) {
        for part in &self.0 {
            builder.token(trivia_syntax_kind(part.kind).into(), &part.text);
        }
    }

    fn into_physical(self) -> Box<[Trivia]> {
        self.0
    }
}

/// Fenced owners build physical leading parts locally and can only hand the
/// completed collection to `Item::finish`. It cannot enter `Item::plain` or a
/// detached ordinary-trivia emitter.
#[derive(Default)]
pub(super) struct PhysicalLeadingTrivia(Vec<Trivia>);

impl PhysicalLeadingTrivia {
    pub(super) fn from_ordinary(leading: LeadingTrivia) -> Self {
        Self(leading.0.into_vec())
    }

    pub(super) fn push_ordinary(&mut self, trivia: Trivia) {
        self.0.push(trivia);
    }

    pub(super) fn push_quote_prefix(&mut self, text: Box<str>) {
        self.0.push(Trivia {
            kind: TriviaKind::YmQuotePrefix,
            text,
        });
    }

    pub(super) fn into_ordinary(self) -> LeadingTrivia {
        LeadingTrivia::ordinary(self.0.into_boxed_slice())
    }

    fn into_boxed(self) -> Box<[Trivia]> {
        self.0.into_boxed_slice()
    }
}

#[derive(Clone, Copy)]
pub(super) struct LeadingView<'item> {
    physical: &'item [Trivia],
    first_unemitted: usize,
}

impl<'item> LeadingView<'item> {
    fn remaining_physical(self) -> impl Iterator<Item = &'item Trivia> {
        self.physical[self.first_unemitted..].iter()
    }

    pub(super) fn has_ordinary_trivia(self) -> bool {
        self.remaining_physical()
            .any(|part| part.kind != TriviaKind::YmQuotePrefix)
    }

    pub(super) fn is_grammar_empty(self) -> bool {
        !self.has_ordinary_trivia()
    }

    pub(super) fn is_adjacent(self) -> bool {
        self.is_grammar_empty()
    }

    pub(super) fn has_ordinary_newline(self) -> bool {
        self.remaining_physical()
            .any(|part| part.kind == TriviaKind::Newline)
    }

    pub(super) fn indentation_after_newline(self) -> Option<usize> {
        indentation_after_newline(
            self.remaining_physical()
                .filter(|part| part.kind != TriviaKind::YmQuotePrefix),
        )
    }

    pub(super) fn contains_line_break(self) -> bool {
        self.remaining_physical()
            .filter(|part| part.kind != TriviaKind::YmQuotePrefix)
            .any(|part| part.text.contains(['\r', '\n']))
    }

    pub(super) fn remaining_physical_parts(self) -> usize {
        self.physical.len() - self.first_unemitted
    }

    pub(super) fn cut_after_last_ordinary_newline(self) -> Option<usize> {
        self.remaining_physical()
            .enumerate()
            .filter(|(_, part)| part.kind == TriviaKind::Newline)
            .map(|(offset, _)| self.first_unemitted + offset + 1)
            .last()
    }
}

fn indentation_after_newline<'a>(parts: impl Iterator<Item = &'a Trivia>) -> Option<usize> {
    let mut saw_newline = false;
    let mut at_line_start = false;
    let mut indentation = 0usize;
    for part in parts {
        match part.kind {
            TriviaKind::Newline => {
                saw_newline = true;
                at_line_start = true;
                indentation = 0;
            }
            TriviaKind::Whitespace if at_line_start => {
                indentation += part.text.chars().count();
            }
            TriviaKind::YmQuotePrefix => {
                unreachable!("ordinary parts exclude quote prefixes")
            }
            _ => at_line_start = false,
        }
    }
    saw_newline.then_some(indentation)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Trivia {
    kind: TriviaKind,
    text: Box<str>,
}

impl Trivia {
    pub(super) fn whitespace(text: Box<str>) -> Self {
        Self {
            kind: TriviaKind::Whitespace,
            text,
        }
    }

    pub(super) fn newline(text: Box<str>) -> Self {
        Self {
            kind: TriviaKind::Newline,
            text,
        }
    }

    pub(super) fn line_comment(text: Box<str>) -> Self {
        Self {
            kind: TriviaKind::LineComment,
            text,
        }
    }

    pub(super) fn block_comment(text: Box<str>) -> Self {
        Self {
            kind: TriviaKind::BlockComment,
            text,
        }
    }

    pub(super) fn is_newline(&self) -> bool {
        self.kind == TriviaKind::Newline
    }

    pub(super) fn has_line_feed(&self) -> bool {
        self.kind == TriviaKind::Newline && self.text.ends_with('\n')
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TriviaKind {
    Whitespace,
    Newline,
    LineComment,
    BlockComment,
    YmQuotePrefix,
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

#[derive(Clone, Copy)]
pub(super) struct PayloadView<'item> {
    payload: &'item Payload,
}

impl<'item> PayloadView<'item> {
    pub(super) fn token_kind(self) -> Option<TokenKind> {
        match self.payload {
            Payload::Token(token) => Some(token.kind),
            Payload::Operator(_) | Payload::Boundary(_) | Payload::Eof => None,
        }
    }

    pub(super) fn operator_use(self) -> Option<&'item OperatorUse> {
        match self.payload {
            Payload::Operator(operator) => Some(&operator.use_),
            Payload::Token(_) | Payload::Boundary(_) | Payload::Eof => None,
        }
    }

    pub(super) fn spelling(self) -> Option<&'item str> {
        match self.payload {
            Payload::Token(token) => Some(&token.text),
            Payload::Operator(operator) => Some(&operator.text),
            Payload::Boundary(_) | Payload::Eof => None,
        }
    }

    pub(super) fn is_boundary(self) -> bool {
        matches!(self.payload, Payload::Boundary(_))
    }

    pub(super) fn is_eof(self) -> bool {
        matches!(self.payload, Payload::Eof)
    }
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
enum ForeignKind {
    YmQuotePrefix,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ForeignSplit {
    offset: usize,
    length: usize,
    kind: ForeignKind,
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
    ForeignPartMismatch,
    InvalidForeignPlacement,
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
    fn finish(
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
}

/// A scanned logical item owns every byte it retains.
#[derive(Debug, Eq, PartialEq)]
pub(super) struct Item {
    physical_leading: Box<[Trivia]>,
    payload: Payload,
    fragments: Option<PendingFragments>,
    first_unemitted_leading: usize,
}

impl Item {
    pub(super) fn plain(leading: LeadingTrivia, payload: Payload) -> Self {
        Self {
            physical_leading: leading.into_physical(),
            payload,
            fragments: None,
            first_unemitted_leading: 0,
        }
    }

    pub(super) fn finish(
        physical_leading: PhysicalLeadingTrivia,
        payload: Payload,
        pending_splits: Option<Vec<ForeignSplit>>,
        item_origin: usize,
    ) -> Result<Self, FragmentError> {
        let physical_leading = physical_leading.into_boxed();
        let physical_length = physical_leading
            .iter()
            .try_fold(0usize, |length, part| length.checked_add(part.text.len()))
            .and_then(|length| {
                length.checked_add(payload_text(&payload).map_or(0, |(_, text)| text.len()))
            })
            .ok_or(FragmentError::Overflow)?;
        let fragments = PendingFragments::finish(pending_splits, item_origin, physical_length)?;
        let item = Self {
            physical_leading,
            payload,
            fragments,
            first_unemitted_leading: 0,
        };
        item.validate_fragments()?;
        Ok(item)
    }

    pub(super) fn leading_view(&self) -> LeadingView<'_> {
        LeadingView {
            physical: &self.physical_leading,
            first_unemitted: self.first_unemitted_leading,
        }
    }

    pub(super) fn payload_view(&self) -> PayloadView<'_> {
        PayloadView {
            payload: &self.payload,
        }
    }

    pub(super) fn emit_all_remaining_leading(&mut self, builder: &mut GreenNodeBuilder<'static>) {
        assert!(!self.payload_view().is_boundary());
        self.emit_leading_range(builder, self.physical_leading.len(), |_, _| {});
    }

    pub(super) fn emit_leading_prefix_with(
        &mut self,
        builder: &mut GreenNodeBuilder<'static>,
        end_part: usize,
        before_part: impl FnMut(TriviaKind, &mut GreenNodeBuilder<'static>),
    ) {
        assert!(!self.payload_view().is_boundary());
        self.emit_leading_range(builder, end_part, before_part);
    }

    pub(super) fn emit_payload(self, builder: &mut GreenNodeBuilder<'static>, kind: SyntaxKind) {
        assert_eq!(self.first_unemitted_leading, self.physical_leading.len());
        let mut cursor = self.payload_fragment_cursor();
        self.emit_payload_with_cursor(builder, kind, &mut cursor);
    }

    pub(super) fn emit_remaining(
        mut self,
        builder: &mut GreenNodeBuilder<'static>,
        payload_kind: SyntaxKind,
    ) {
        assert!(payload_text(&self.payload).is_some());
        let mut cursor = self.fragment_cursor();
        self.emit_leading_range_with_cursor(
            builder,
            self.physical_leading.len(),
            |_, _| {},
            &mut cursor,
        );
        self.emit_payload_with_cursor(builder, payload_kind, &mut cursor);
    }

    pub(super) fn emit_eof_leading(&mut self, builder: &mut GreenNodeBuilder<'static>) {
        assert!(self.payload_view().is_eof());
        self.emit_leading_range(builder, self.physical_leading.len(), |_, _| {});
    }

    pub(super) fn emit_terminal_boundary(
        mut self,
        builder: &mut GreenNodeBuilder<'static>,
    ) -> PendingBoundary {
        assert_eq!(self.first_unemitted_leading, 0);
        assert!(self.payload_view().is_boundary());
        self.emit_leading_range_unchecked(builder, self.physical_leading.len(), |_, _| {});
        match self.payload {
            Payload::Boundary(boundary) => boundary,
            Payload::Token(_) | Payload::Operator(_) | Payload::Eof => unreachable!(),
        }
    }

    fn emit_leading_range(
        &mut self,
        builder: &mut GreenNodeBuilder<'static>,
        end_part: usize,
        before_part: impl FnMut(TriviaKind, &mut GreenNodeBuilder<'static>),
    ) {
        assert!(!self.payload_view().is_boundary());
        self.emit_leading_range_unchecked(builder, end_part, before_part);
    }

    fn emit_leading_range_unchecked(
        &mut self,
        builder: &mut GreenNodeBuilder<'static>,
        end_part: usize,
        before_part: impl FnMut(TriviaKind, &mut GreenNodeBuilder<'static>),
    ) {
        let mut cursor = self.fragment_cursor();
        self.emit_leading_range_with_cursor(builder, end_part, before_part, &mut cursor);
    }

    fn emit_leading_range_with_cursor(
        &mut self,
        builder: &mut GreenNodeBuilder<'static>,
        end_part: usize,
        mut before_part: impl FnMut(TriviaKind, &mut GreenNodeBuilder<'static>),
        cursor: &mut Option<FragmentCursor>,
    ) {
        assert!(end_part >= self.first_unemitted_leading);
        assert!(end_part <= self.physical_leading.len());
        for index in self.first_unemitted_leading..end_part {
            let part = &self.physical_leading[index];
            before_part(part.kind, builder);
            emit_physical_text(
                builder,
                self.fragments.as_ref(),
                cursor,
                trivia_syntax_kind(part.kind),
                &part.text,
            );
            self.first_unemitted_leading = index + 1;
        }
    }

    fn emit_payload_with_cursor(
        &self,
        builder: &mut GreenNodeBuilder<'static>,
        kind: SyntaxKind,
        cursor: &mut Option<FragmentCursor>,
    ) {
        let (_, text) = payload_text(&self.payload).expect("a lexical Item has payload text");
        emit_physical_text(builder, self.fragments.as_ref(), cursor, kind, text);
    }

    fn fragment_cursor(&self) -> Option<FragmentCursor> {
        let fragments = self.fragments.as_ref()?;
        let physical_start = fragments.physical.start
            + self.physical_leading[..self.first_unemitted_leading]
                .iter()
                .map(|part| part.text.len())
                .sum::<usize>();
        let mut split_index = 0;
        while fragments
            .foreign
            .get(split_index)
            .is_some_and(|split| split.offset < physical_start)
        {
            split_index += 1;
        }
        Some(FragmentCursor {
            physical_start,
            split_index,
        })
    }

    /// Locates the payload directly from the immutable carrier end. This is
    /// called once after leading is exhausted, so its one binary search is
    /// `O(log splits)` and never re-traverses leading metadata.
    fn payload_fragment_cursor(&self) -> Option<FragmentCursor> {
        let fragments = self.fragments.as_ref()?;
        let (_, text) = payload_text(&self.payload).expect("a lexical Item has payload text");
        let physical_start = fragments
            .physical
            .end
            .checked_sub(text.len())
            .expect("validated Item payload lies inside its physical carrier");
        let split_index = fragments
            .foreign
            .partition_point(|split| split.offset < physical_start);
        Some(FragmentCursor {
            physical_start,
            split_index,
        })
    }

    fn validate_fragments(&self) -> Result<(), FragmentError> {
        let total = self
            .constituent_texts()
            .try_fold(0usize, |length, (_, text)| length.checked_add(text.len()))
            .ok_or(FragmentError::Overflow)?;
        let Some(fragments) = &self.fragments else {
            return if self
                .physical_leading
                .iter()
                .any(|part| part.kind == TriviaKind::YmQuotePrefix)
            {
                Err(FragmentError::ForeignPartMismatch)
            } else {
                Ok(())
            };
        };
        if fragments.physical.end - fragments.physical.start != total {
            return Err(FragmentError::PhysicalLengthMismatch);
        }

        let mut part_start = fragments.physical.start;
        let mut split_index = 0;
        for (part_kind, text) in self.constituent_texts() {
            let part_end = part_start
                .checked_add(text.len())
                .ok_or(FragmentError::Overflow)?;
            let first_split = split_index;
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
            if let ItemTextPart::LeadingTrivia(index) = part_kind {
                let matching = &fragments.foreign[first_split..split_index];
                match self.physical_leading[index].kind {
                    TriviaKind::YmQuotePrefix => {
                        if matching.len() != 1
                            || matching[0].kind != ForeignKind::YmQuotePrefix
                            || matching[0].offset != part_start
                            || matching[0].length != text.len()
                        {
                            return Err(FragmentError::ForeignPartMismatch);
                        }
                    }
                    TriviaKind::BlockComment => {}
                    TriviaKind::Whitespace | TriviaKind::Newline | TriviaKind::LineComment => {
                        if !matching.is_empty() {
                            return Err(FragmentError::InvalidForeignPlacement);
                        }
                    }
                }
            }
            part_start = part_end;
        }
        if split_index != fragments.foreign.len() {
            return Err(FragmentError::OutsidePhysicalText);
        }
        Ok(())
    }

    fn constituent_texts(&self) -> impl Iterator<Item = (ItemTextPart, &str)> {
        self.physical_leading
            .iter()
            .enumerate()
            .map(|(index, trivia)| (ItemTextPart::LeadingTrivia(index), &*trivia.text))
            .chain(self.payload_text())
    }

    fn payload_text(&self) -> Option<(ItemTextPart, &str)> {
        payload_text(&self.payload)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ItemTextPart {
    LeadingTrivia(usize),
    PayloadToken,
    PayloadOperator,
}

fn payload_text(payload: &Payload) -> Option<(ItemTextPart, &str)> {
    match payload {
        Payload::Token(token) => Some((ItemTextPart::PayloadToken, &token.text)),
        Payload::Operator(operator) => Some((ItemTextPart::PayloadOperator, &operator.text)),
        Payload::Boundary(_) | Payload::Eof => None,
    }
}

fn trivia_syntax_kind(kind: TriviaKind) -> SyntaxKind {
    match kind {
        TriviaKind::Whitespace => SyntaxKind::Whitespace,
        TriviaKind::Newline => SyntaxKind::Newline,
        TriviaKind::LineComment => SyntaxKind::LineComment,
        TriviaKind::BlockComment => SyntaxKind::BlockComment,
        TriviaKind::YmQuotePrefix => SyntaxKind::YmQuotePrefix,
    }
}

struct FragmentCursor {
    physical_start: usize,
    split_index: usize,
}

fn emit_physical_text(
    builder: &mut GreenNodeBuilder<'static>,
    fragments: Option<&PendingFragments>,
    cursor: &mut Option<FragmentCursor>,
    ordinary: SyntaxKind,
    text: &str,
) {
    let Some(fragments) = fragments else {
        debug_assert!(cursor.is_none());
        builder.token(ordinary.into(), text);
        return;
    };
    let cursor = cursor
        .as_mut()
        .expect("fragmented Item emission has one operation-local cursor");
    let part_start = cursor.physical_start;
    let part_end = part_start + text.len();
    let first_split = cursor.split_index;
    while fragments
        .foreign
        .get(cursor.split_index)
        .is_some_and(|split| split.offset < part_end)
    {
        cursor.split_index += 1;
    }
    emit_fragmented_part(
        builder,
        ordinary,
        part_start,
        text,
        &fragments.foreign[first_split..cursor.split_index],
    );
    cursor.physical_start = part_end;
}

fn emit_fragmented_part(
    builder: &mut GreenNodeBuilder<'static>,
    ordinary: SyntaxKind,
    physical_start: usize,
    text: &str,
    foreign: &[ForeignSplit],
) {
    let mut cursor = 0;
    for split in foreign {
        let start = split.offset - physical_start;
        let end = start + split.length;
        if cursor < start {
            builder.token(ordinary.into(), &text[cursor..start]);
        }
        let kind = match split.kind {
            ForeignKind::YmQuotePrefix => SyntaxKind::YmQuotePrefix,
        };
        builder.token(kind.into(), &text[start..end]);
        cursor = end;
    }
    if cursor < text.len() {
        builder.token(ordinary.into(), &text[cursor..]);
    }
}
