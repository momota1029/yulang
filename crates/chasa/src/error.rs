pub mod std;

use ::std::cmp::Ordering;
use ::std::marker::PhantomData;
use ::std::ops::Range;

use reborrow_generic::Reborrow;

use crate::back::RbBack;

pub trait MergeErrors: Sized {
    type Output;
    fn merge(errors: &[Self]) -> Self::Output;
}

pub trait ErrorSink<Pos>: RbBack {
    type Error: MergeErrors;

    fn push(this: Self::Target<'_>, range: Range<Pos>, error: Self::Error);
    fn take_merged(this: Self::Target<'_>) -> Option<<Self::Error as MergeErrors>::Output>;
}

#[derive(Debug, Default)]
pub struct LatestSink<Pos, E> {
    range: Option<Range<Pos>>,
    errors: Vec<E>,
    group_start: usize,
    undo: Vec<Undo<Pos>>,
    base_index: usize,
}

#[derive(Debug)]
enum Undo<Pos> {
    SetNone {
        old_len: usize,
    },
    PopError,
    Replace {
        old_range: Option<Range<Pos>>,
        old_group_start: usize,
        old_len: usize,
    },
}

impl<Pos, E> LatestSink<Pos, E> {
    pub fn new() -> Self {
        Self {
            range: None,
            errors: Vec::new(),
            group_start: 0,
            undo: Vec::new(),
            base_index: 0,
        }
    }

    pub fn clear(&mut self) {
        self.range = None;
        self.errors.clear();
        self.group_start = 0;
        self.undo.clear();
        self.base_index = 0;
    }

    pub fn commit(&mut self) {
        self.base_index += self.undo.len();
        self.undo.clear();
        if self.range.is_none() {
            self.errors.clear();
            self.group_start = 0;
        } else if self.group_start > 0 {
            self.errors.drain(0..self.group_start);
            self.group_start = 0;
        }
    }
}

impl<Pos: Ord, E: MergeErrors> LatestSink<Pos, E> {
    #[inline]
    pub fn take_merged(&mut self) -> Option<<E as MergeErrors>::Output> {
        <Self as ErrorSink<Pos>>::take_merged(self)
    }
}

fn cmp_range<Pos: Ord>(a: &Range<Pos>, b: &Range<Pos>) -> Ordering {
    let a_key = (&a.start, &a.end);
    let b_key = (&b.start, &b.end);
    a_key.cmp(&b_key)
}

impl<Pos, E> LatestSink<Pos, E> {
    fn current_errors(&self) -> &[E] {
        match self.range {
            None => &[],
            Some(_) => &self.errors[self.group_start..],
        }
    }
}

impl<Pos, E> Reborrow for LatestSink<Pos, E> {
    type Target<'short>
        = &'short mut Self
    where
        Self: 'short;

    fn rb<'short>(&'short mut self) -> Self::Target<'short> {
        self
    }

    fn shorten<'short, 'long: 'short>(this: Self::Target<'long>) -> Self::Target<'short> {
        this
    }

    fn shorten_mut<'short, 'long>(this: &'short mut Self::Target<'long>) -> Self::Target<'short> {
        this
    }
}

impl<Pos: Ord, E: MergeErrors> ErrorSink<Pos> for LatestSink<Pos, E> {
    type Error = E;

    fn push(this: Self::Target<'_>, range: Range<Pos>, error: Self::Error) {
        match this.range.as_ref() {
            None => {
                this.range = Some(range);
                this.group_start = this.errors.len();
                this.errors.push(error);
                this.undo.push(Undo::SetNone {
                    old_len: this.errors.len() - 1,
                });
            }
            Some(current) => match cmp_range(&range, current) {
                Ordering::Less => {}
                Ordering::Equal => {
                    this.errors.push(error);
                    this.undo.push(Undo::PopError);
                }
                Ordering::Greater => {
                    let old_range = this.range.replace(range);
                    let old_group_start = this.group_start;
                    let old_len = this.errors.len();
                    this.group_start = this.errors.len();
                    this.errors.push(error);
                    this.undo.push(Undo::Replace {
                        old_range,
                        old_group_start,
                        old_len,
                    });
                }
            },
        }
    }

    fn take_merged(this: Self::Target<'_>) -> Option<<Self::Error as MergeErrors>::Output> {
        let errors = this.current_errors();
        if errors.is_empty() {
            return None;
        }
        let out = E::merge(errors);
        this.clear();
        Some(out)
    }
}

impl<Pos, E> RbBack for LatestSink<Pos, E> {
    type Checkpoint = usize;

    fn checkpoint<'a>(this: Self::Target<'a>) -> Self::Checkpoint {
        this.base_index + this.undo.len()
    }

    fn rollback<'a>(this: Self::Target<'a>, checkpoint: Self::Checkpoint) {
        let checkpoint = checkpoint.max(this.base_index);
        while this.base_index + this.undo.len() > checkpoint {
            match this.undo.pop().expect("checked by loop condition") {
                Undo::SetNone { old_len } => {
                    this.range = None;
                    this.errors.truncate(old_len);
                    this.group_start = this.errors.len();
                }
                Undo::PopError => {
                    this.errors.pop();
                }
                Undo::Replace {
                    old_range,
                    old_group_start,
                    old_len,
                } => {
                    this.range = old_range;
                    this.errors.truncate(old_len);
                    this.group_start = old_group_start;
                }
            }
        }
    }
}

#[derive(Debug, Default, Reborrow)]
pub struct NullSink<E> {
    _marker: PhantomData<fn() -> E>,
}

impl<E> NullSink<E> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

impl<Pos, E: MergeErrors> ErrorSink<Pos> for NullSink<E> {
    type Error = E;

    fn push(_: NullSink<E>, _: Range<Pos>, _: Self::Error) {}

    fn take_merged(_: NullSink<E>) -> Option<<Self::Error as MergeErrors>::Output> {
        None
    }
}

impl<E> RbBack for NullSink<E> {
    type Checkpoint = ();

    fn checkpoint<'a>(_: NullSink<E>) -> Self::Checkpoint {}

    fn rollback<'a>(_: NullSink<E>, _: Self::Checkpoint) {}
}
