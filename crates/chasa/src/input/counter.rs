use crate::back::Back;

pub trait Counter<Item>: Back {
    type Pos: Ord + Clone;
    fn feed(&mut self, item: Item);
    fn pos(&self) -> Self::Pos;
}

impl<T> Counter<T> for usize {
    type Pos = usize;

    fn feed(&mut self, _item: T) {
        *self += 1;
    }

    fn pos(&self) -> Self::Pos {
        *self
    }
}
