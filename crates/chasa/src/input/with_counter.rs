use crate::back::{Back, Front};
use crate::input::{Counter, Input, SeqInput};

pub struct WithCounter<I, C> {
    pub input: I,
    pub counter: C,
}

impl<I, C> WithCounter<I, C> {
    pub fn inner(&self) -> &I {
        &self.input
    }

    pub fn inner_mut(&mut self) -> &mut I {
        &mut self.input
    }

    pub fn counter(&self) -> &C {
        &self.counter
    }
}

impl<I, C> Back for WithCounter<I, C>
where
    I: Input,
    C: Counter<I::Item>,
{
    type Checkpoint = (I::Checkpoint, C::Checkpoint);

    fn checkpoint(&mut self) -> Self::Checkpoint {
        (self.input.checkpoint(), self.counter.checkpoint())
    }

    fn rollback(&mut self, checkpoint: Self::Checkpoint) {
        self.input.rollback(checkpoint.0);
        self.counter.rollback(checkpoint.1);
    }
}

impl<I, C> Input for WithCounter<I, C>
where
    I: Input,
    C: Counter<I::Item>,
{
    type Item = I::Item;
    type Pos = C::Pos;

    fn index(&self) -> u64 {
        self.input.index()
    }

    fn pos(&self) -> Self::Pos {
        self.counter.pos()
    }

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.input.next()?;
        self.counter.feed(item.clone());
        Some(item)
    }

    fn commit(&mut self) {
        self.input.commit();
    }
}

impl<I, C> SeqInput for WithCounter<I, C>
where
    I: SeqInput,
    C: Counter<I::Item>,
{
    type Seq = I::Seq;

    fn seq(start: Self::Checkpoint, end: Self::Checkpoint) -> I::Seq {
        I::seq(start.0, end.0)
    }
}

impl<I, C> Front for WithCounter<I, C>
where
    I: Input + Front,
    C: Counter<I::Item> + Front,
{
}
