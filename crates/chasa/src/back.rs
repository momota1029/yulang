use reborrow_generic::Reborrow;

pub trait Back {
    type Checkpoint: Clone;
    fn checkpoint(&mut self) -> Self::Checkpoint;
    fn rollback(&mut self, checkpoint: Self::Checkpoint);
}

pub trait Front: Back {}

impl<T: Clone> Back for T {
    type Checkpoint = T;
    fn checkpoint(&mut self) -> Self::Checkpoint {
        self.clone()
    }
    fn rollback(&mut self, checkpoint: Self::Checkpoint) {
        *self = checkpoint;
    }
}

impl<T: Clone> Front for T {}

pub trait RbBack: Reborrow {
    type Checkpoint: Clone;
    fn checkpoint<'a>(this: Self::Target<'a>) -> Self::Checkpoint;
    fn rollback<'a>(this: Self::Target<'a>, checkpoint: Self::Checkpoint);
}

pub trait RbFront: RbBack {}

impl<'a, T: Back> RbBack for &'a mut T {
    type Checkpoint = T::Checkpoint;
    fn checkpoint<'b>(this: &'b mut T) -> Self::Checkpoint {
        this.checkpoint()
    }
    fn rollback<'b>(this: &'b mut T, checkpoint: Self::Checkpoint) {
        this.rollback(checkpoint);
    }
}

impl<'a, T: Front> RbFront for &'a mut T {}

impl RbBack for () {
    type Checkpoint = ();
    fn checkpoint<'a>(_: ()) -> Self::Checkpoint {}
    fn rollback<'a>(_: (), _: Self::Checkpoint) {}
}

impl RbFront for () {}
