use core::marker::PhantomData;

use crate::input::{Input, Offset, SeqInput};

impl<'a> Input for &'a str {
    type Item = char;
    type Pos = Offset<char>;

    fn index(&self) -> u64 {
        u64::MAX - (self.len() as u64)
    }

    fn pos(&self) -> Self::Pos {
        Offset(self.as_ptr() as usize, PhantomData)
    }

    fn next(&mut self) -> Option<Self::Item> {
        let mut chars = self.chars();
        let c = chars.next();
        *self = chars.as_str();
        c
    }

    fn commit(&mut self) {}
}

impl<'a> SeqInput for &'a str {
    type Seq = &'a str;
    fn seq(start: Self::Checkpoint, end: Self::Checkpoint) -> Self::Seq {
        &start[0..(start.len() - end.len())]
    }
}

impl<'a, T> Input for &'a [T]
where
    T: Clone,
{
    type Item = T;
    type Pos = Offset<T>;

    fn index(&self) -> u64 {
        u64::MAX - (self.len() as u64)
    }

    fn pos(&self) -> Self::Pos {
        Offset(self.as_ptr() as usize, PhantomData)
    }

    fn next(&mut self) -> Option<Self::Item> {
        let first = self.first()?.clone();
        *self = &self[1..];
        Some(first)
    }

    fn commit(&mut self) {}
}

impl<'a, T> SeqInput for &'a [T]
where
    T: Clone,
{
    type Seq = &'a [T];
    fn seq(start: Self::Checkpoint, end: Self::Checkpoint) -> Self::Seq {
        &start[0..(start.len() - end.len())]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::back::Back;

    #[test]
    fn str_seq_returns_consumed_prefix() {
        let mut input = "ab";
        let start = input.checkpoint();
        input.next();
        let end = input.checkpoint();
        let seq = <&str as SeqInput>::seq(start, end);
        assert_eq!(seq, "a");
    }

    #[test]
    fn slice_seq_returns_consumed_prefix() {
        let mut input: &[u8] = b"ab";
        let start = input.checkpoint();
        input.next();
        let end = input.checkpoint();
        let seq = <&[u8] as SeqInput>::seq(start, end);
        assert_eq!(seq, b"a");
    }
}
