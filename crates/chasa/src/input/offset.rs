use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;

use crate::input::ToSpan;

pub struct Offset<T>(pub usize, pub PhantomData<fn() -> T>);

impl<T> Offset<T> {
    pub fn new(ptr: usize) -> Self {
        Self(ptr, PhantomData)
    }
}

impl<T> Copy for Offset<T> {}

impl<T> Clone for Offset<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> fmt::Debug for Offset<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Offset").field(&self.0).finish()
    }
}

impl<T> PartialEq for Offset<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for Offset<T> {}

impl<T> PartialOrd for Offset<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Offset<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T> Hash for Offset<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T> ToSpan for Offset<T> {
    type Span = usize;
    fn span_to(&self, end: &Self) -> Self::Span {
        end.0.saturating_sub(self.0)
    }
}
