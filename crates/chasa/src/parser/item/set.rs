use ::std::ops;

pub trait ItemSet<Item> {
    type Copyable: ItemSet<Item>;

    fn has(&self, item: &Item) -> bool;
    fn into_copyable(self) -> Self::Copyable;

    fn cap<A: ItemSet<Item>>(self, other: A) -> Intersection<Self, A>
    where
        Self: Sized,
    {
        Intersection(self, other)
    }

    fn and<A: ItemSet<Item>>(self, other: A) -> Union<Self, A>
    where
        Self: Sized,
    {
        Union(self, other)
    }

    fn sub<A: ItemSet<Item>>(self, other: A) -> Difference<Self, A>
    where
        Self: Sized,
    {
        Difference(self, other)
    }

    fn complement(self) -> Complement<Self>
    where
        Self: Sized,
    {
        Complement(self)
    }
}

impl<'a> ItemSet<char> for &'a str {
    type Copyable = &'a str;

    fn has(&self, item: &char) -> bool {
        self.contains(*item)
    }

    fn into_copyable(self) -> Self::Copyable {
        self
    }
}

impl ItemSet<char> for char {
    type Copyable = char;

    fn has(&self, item: &char) -> bool {
        self == item
    }

    fn into_copyable(self) -> Self::Copyable {
        self
    }
}

impl<Item: Clone, F: Fn(Item) -> bool> ItemSet<Item> for F {
    type Copyable = F;

    fn has(&self, item: &Item) -> bool {
        self(item.clone())
    }

    fn into_copyable(self) -> Self::Copyable {
        self
    }
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct Intersection<A, B>(pub A, pub B);
impl<Item, A: ItemSet<Item>, B: ItemSet<Item>> ItemSet<Item> for Intersection<A, B> {
    type Copyable = Intersection<A::Copyable, B::Copyable>;

    fn has(&self, item: &Item) -> bool {
        self.0.has(item) && self.1.has(item)
    }

    fn into_copyable(self) -> Self::Copyable {
        Intersection(self.0.into_copyable(), self.1.into_copyable())
    }
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct Union<A, B>(pub A, pub B);
impl<Item, A: ItemSet<Item>, B: ItemSet<Item>> ItemSet<Item> for Union<A, B> {
    type Copyable = Union<A::Copyable, B::Copyable>;

    fn has(&self, item: &Item) -> bool {
        self.0.has(item) || self.1.has(item)
    }

    fn into_copyable(self) -> Self::Copyable {
        Union(self.0.into_copyable(), self.1.into_copyable())
    }
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct Difference<A, B>(pub A, pub B);
impl<Item, A: ItemSet<Item>, B: ItemSet<Item>> ItemSet<Item> for Difference<A, B> {
    type Copyable = Difference<A::Copyable, B::Copyable>;

    fn has(&self, item: &Item) -> bool {
        self.0.has(item) && !self.1.has(item)
    }

    fn into_copyable(self) -> Self::Copyable {
        Difference(self.0.into_copyable(), self.1.into_copyable())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Complement<A>(pub A);
impl<Item, A: ItemSet<Item>> ItemSet<Item> for Complement<A> {
    type Copyable = Complement<A::Copyable>;

    fn has(&self, item: &Item) -> bool {
        !self.0.has(item)
    }

    fn into_copyable(self) -> Self::Copyable {
        Complement(self.0.into_copyable())
    }
}

impl<T> ItemSet<T> for ops::RangeFull {
    type Copyable = ops::RangeFull;

    fn has(&self, _: &T) -> bool {
        true
    }

    fn into_copyable(self) -> Self::Copyable {
        self
    }
}

macro_rules! impl_range_same {
    ($Range:ident) => {
        impl<T: PartialOrd> ItemSet<T> for ops::$Range<T> {
            type Copyable = ops::$Range<T>;

            fn has(&self, item: &T) -> bool {
                self.contains(item)
            }

            fn into_copyable(self) -> Self::Copyable {
                self
            }
        }
    };
}

impl_range_same!(RangeTo);
impl_range_same!(RangeToInclusive);

macro_rules! impl_copy_range {
    ($StdRange:ident, $CopyRange:ident) => {
        impl<T: PartialOrd> ItemSet<T> for ops::$StdRange<T> {
            type Copyable = copy_range::$CopyRange<T>;

            fn has(&self, item: &T) -> bool {
                self.contains(item)
            }

            fn into_copyable(self) -> Self::Copyable {
                copy_range::$CopyRange::from_std(self)
            }
        }

        impl<T: PartialOrd> ItemSet<T> for copy_range::$CopyRange<T> {
            type Copyable = copy_range::$CopyRange<T>;

            fn has(&self, item: &T) -> bool {
                self.contains(item)
            }

            fn into_copyable(self) -> Self::Copyable {
                self
            }
        }
    };
}

impl_copy_range!(Range, CopyRange);
impl_copy_range!(RangeFrom, CopyRangeFrom);
impl_copy_range!(RangeInclusive, CopyRangeInclusive);
