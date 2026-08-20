//! UTF-8 byte-positioned source input for chasa parsers.

use chasa::{Back, Input, SeqInput};

/// A borrowing character input whose public position is a source byte offset.
pub(crate) struct SourceInput<'source> {
    source: &'source str,
    remainder: &'source str,
    byte_offset: usize,
}

impl<'source> SourceInput<'source> {
    pub(crate) fn new(source: &'source str) -> Self {
        Self {
            source,
            remainder: source,
            byte_offset: 0,
        }
    }

    pub(crate) fn source(&self) -> &'source str {
        self.source
    }

    pub(crate) fn remainder(&self) -> &'source str {
        self.remainder
    }
}

/// A cheap source cursor snapshot; both fields are restored together.
#[derive(Clone, Copy)]
pub(crate) struct SourceCheckpoint<'source> {
    remainder: &'source str,
    byte_offset: usize,
}

impl<'source> Back for SourceInput<'source> {
    type Checkpoint = SourceCheckpoint<'source>;

    fn checkpoint(&mut self) -> Self::Checkpoint {
        SourceCheckpoint {
            remainder: self.remainder,
            byte_offset: self.byte_offset,
        }
    }

    fn rollback(&mut self, checkpoint: Self::Checkpoint) {
        self.remainder = checkpoint.remainder;
        self.byte_offset = checkpoint.byte_offset;
    }
}

impl Input for SourceInput<'_> {
    type Item = char;
    type Pos = usize;

    fn index(&self) -> u64 {
        self.byte_offset as u64
    }

    fn pos(&self) -> Self::Pos {
        self.byte_offset
    }

    fn next(&mut self) -> Option<Self::Item> {
        let character = self.remainder.chars().next()?;
        let length = character.len_utf8();
        self.remainder = &self.remainder[length..];
        self.byte_offset += length;
        Some(character)
    }

    fn commit(&mut self) {}
}

impl<'source> SeqInput for SourceInput<'source> {
    type Seq = &'source str;

    fn seq(start: Self::Checkpoint, end: Self::Checkpoint) -> Self::Seq {
        debug_assert!(start.byte_offset <= end.byte_offset);
        let consumed_len = end.byte_offset - start.byte_offset;
        &start.remainder[..consumed_len]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checkpoint_and_rollback_restore_cursor_and_byte_position() {
        let mut input = SourceInput::new("ab");
        assert_eq!(input.next(), Some('a'));
        let checkpoint = input.checkpoint();

        assert_eq!(input.next(), Some('b'));
        assert_eq!(input.pos(), 2);
        assert_eq!(input.remainder(), "");

        input.rollback(checkpoint);
        assert_eq!(input.pos(), 1);
        assert_eq!(input.remainder(), "b");
        assert_eq!(input.next(), Some('b'));
    }

    #[test]
    fn seq_returns_the_exact_contiguous_source_slice() {
        let mut input = SourceInput::new("before +! after");
        for _ in 0..7 {
            input.next();
        }
        let start = input.checkpoint();
        input.next();
        input.next();
        let end = input.checkpoint();

        assert_eq!(SourceInput::seq(start, end), "+!");
        assert_eq!(input.source(), "before +! after");
    }

    #[test]
    fn multibyte_characters_advance_by_utf8_bytes() {
        let mut input = SourceInput::new("aあ⊕z");
        let start = input.checkpoint();

        assert_eq!(input.next(), Some('a'));
        assert_eq!(input.pos(), 1);
        assert_eq!(input.next(), Some('あ'));
        assert_eq!(input.pos(), 4);
        assert_eq!(input.next(), Some('⊕'));
        assert_eq!(input.pos(), 7);
        let end = input.checkpoint();

        assert_eq!(SourceInput::seq(start, end), "aあ⊕");
        assert_eq!(input.remainder(), "z");
    }
}
