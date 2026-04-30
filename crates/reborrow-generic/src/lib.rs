#![doc = include_str!("../README.md")]

use std::marker::PhantomData;

use seq_macro::seq;

#[cfg(feature = "derive")]
pub use reborrow_generic_derive::*;

pub mod short {
    pub use super::Reborrow as Rb;
    pub use super::Reborrowed as Rbd;
}

pub trait Reborrow {
    type Target<'short>: Reborrowed<'short>
    where
        Self: 'short;
    fn rb<'short>(&'short mut self) -> Self::Target<'short>;
    fn shorten<'short, 'long: 'short>(this: Self::Target<'long>) -> Self::Target<'short>;
    fn shorten_mut<'short, 'long>(this: &'short mut Self::Target<'long>) -> Self::Target<'short>;
}

pub trait Reborrowed<'long>: Reborrow<Target<'long> = Self> + 'long {}
impl<'long, T: ?Sized + Reborrow<Target<'long> = T> + 'long> Reborrowed<'long> for T {}

impl<'a, T: ?Sized + 'a> Reborrow for &'a mut T {
    type Target<'short>
        = &'short mut T
    where
        Self: 'short;
    fn rb(&mut self) -> &mut T {
        self
    }
    fn shorten<'short, 'long: 'short>(this: &'long mut T) -> &'short mut T {
        this
    }
    fn shorten_mut<'short, 'long>(this: &'short mut &'long mut T) -> &'short mut T {
        this
    }
}
impl<'a, T: ?Sized + 'a> Reborrow for &'a T {
    type Target<'short>
        = &'short T
    where
        Self: 'short;

    fn rb(&mut self) -> &T {
        self
    }
    fn shorten<'short, 'long: 'short>(this: &'long T) -> &'short T {
        this
    }
    fn shorten_mut<'short, 'long>(this: &'short mut &'long T) -> &'short T {
        this
    }
}
impl<T: ?Sized> Reborrow for PhantomData<T> {
    type Target<'short>
        = PhantomData<T>
    where
        Self: 'short;

    fn rb(&mut self) -> PhantomData<T> {
        *self
    }
    fn shorten<'short, 'long: 'short>(this: PhantomData<T>) -> PhantomData<T> {
        this
    }
    fn shorten_mut<'short, 'long>(this: &'short mut PhantomData<T>) -> PhantomData<T> {
        *this
    }
}

macro_rules! reborrow_impl_tuple {
    ($Length:literal) => {
        seq!(N in 1..=$Length {
            reborrow_impl_tuple!(#((P~N, p~N),)*);
        });
    };
    ($(($P:ident, $p:ident),)*) => {
        impl<$($P,)*> Reborrow for ($($P,)*) where $($P: Reborrow,)* {
            type Target<'short> = ($($P::Target<'short>,)*) where Self: 'short;
            #[inline(always)]
            fn rb<'short>(&'short mut self) -> Self::Target<'short> {
                let ($($p,)*) = self;
                ($($p.rb(),)*)
            }
            #[inline(always)]
            fn shorten<'short, 'long: 'short>(this: Self::Target<'long>) -> Self::Target<'short> {
                let ($($p,)*) = this;
                ($(<$P>::shorten($p),)*)
            }
            #[inline(always)]
            fn shorten_mut<'short, 'long>(this: &'short mut Self::Target<'long>) -> Self::Target<'short> {
                let ($($p,)*) = this;
                ($(<$P>::shorten_mut($p),)*)
            }
        }
    }
}

seq!(Length in 0..=32 { reborrow_impl_tuple!(Length); });

macro_rules! reborrow_impl_copy {
    () => {};
    ($T:ident, $($L:ident,)*) => {
        impl Reborrow for $T {
            type Target<'short> = $T;
            #[inline(always)]
            fn rb(&mut self) -> $T {
                *self
            }
            #[inline(always)]
            fn shorten<'short, 'long: 'short>(this: $T) -> $T {
                this
            }
            #[inline(always)]
            fn shorten_mut(this: &mut $T) -> $T {
                *this
            }
        }
        reborrow_impl_copy!($($L,)*);
    };
}
reborrow_impl_copy!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, bool, char, f32, f64,
);
