//! Private physical source-draft allocation owners for the staged F5c ledger.
//!
//! The byte convention charges each vector's actual `capacity * size_of::<T>()`.
//! `current_bytes` tracks those vector buffers only. The meter state is inline
//! and contributes zero heap bytes. Each owner wrapper
//! (`size_of::<TrackedVec<T>>()` or `size_of::<TrackedOne<T>>()`) is inline in
//! its containing slot and must be classified there exactly once. Allocator
//! headers, padding outside these Rust values, and fragmentation are excluded by
//! the F5 byte convention. A zero-sized element contributes zero vector bytes.

use std::{cell::Cell, ops::Deref};

struct MeterState {
    current: Cell<Option<usize>>,
}

impl Default for MeterState {
    fn default() -> Self {
        Self {
            current: Cell::new(Some(0)),
        }
    }
}

/// Shared aggregate of live vector capacities. `None` means arithmetic
/// exhaustion; no later release claims to reconstruct an exact total.
#[derive(Default)]
pub(super) struct DraftHeapMeter(MeterState);

impl DraftHeapMeter {
    pub(super) fn current_bytes(&self) -> Option<usize> {
        self.0.current.get()
    }

    pub(super) const fn fixed_payload_bytes() -> usize {
        0
    }

    fn replace(&self, old: usize, new: usize) -> Result<(), ()> {
        let Some(current) = self.current_bytes() else {
            return Err(());
        };
        let Some(next) = current.checked_sub(old).and_then(|n| n.checked_add(new)) else {
            self.0.current.set(None);
            return Err(());
        };
        self.0.current.set(Some(next));
        Ok(())
    }

    fn release(&self, bytes: usize) {
        if let Some(current) = self.current_bytes() {
            self.0.current.set(current.checked_sub(bytes));
        }
    }
}

struct AllocationToken<'meter> {
    meter: &'meter DraftHeapMeter,
    bytes: usize,
}

impl AllocationToken<'_> {
    fn reconcile<T>(&mut self, capacity: usize) -> Result<(), ()> {
        let Some(bytes) = capacity.checked_mul(size_of::<T>()) else {
            self.meter.0.current.set(None);
            return Err(());
        };
        // Retain the lane's actual capacity even when the aggregate overflows.
        let result = self.meter.replace(self.bytes, bytes);
        self.bytes = bytes;
        result
    }
}

impl Drop for AllocationToken<'_> {
    fn drop(&mut self) {
        self.meter.release(self.bytes);
    }
}

/// A vector whose allocation stays charged until its elements and buffer drop.
/// No raw `Vec` or mutable vector dereference escapes this owner.
pub(super) struct TrackedVec<'meter, T> {
    values: Option<Vec<T>>,
    token: AllocationToken<'meter>,
}

impl<'meter, T> TrackedVec<'meter, T> {
    pub(super) fn new(meter: &'meter DraftHeapMeter) -> Self {
        Self {
            values: Some(Vec::new()),
            token: AllocationToken { meter, bytes: 0 },
        }
    }

    pub(super) fn capacity(&self) -> usize {
        self.values.as_ref().unwrap().capacity()
    }

    pub(super) fn len(&self) -> usize {
        self.values.as_ref().unwrap().len()
    }

    pub(super) fn accounted_bytes(&self) -> usize {
        self.token.bytes
    }

    pub(super) fn meter(&self) -> &'meter DraftHeapMeter {
        self.token.meter
    }

    /// Transfer the charge with an unchanged raw buffer. The returned token
    /// must outlive the raw buffer and all of its elements.
    pub(super) fn into_raw_with_token(mut self) -> (Vec<T>, TrackedAllocation<'meter>) {
        let values = self.values.take().unwrap();
        let bytes = std::mem::replace(&mut self.token.bytes, 0);
        (
            values,
            TrackedAllocation(AllocationToken {
                meter: self.token.meter,
                bytes,
            }),
        )
    }

    pub(super) fn as_mut_slice(&mut self) -> &mut [T] {
        self.values.as_mut().unwrap().as_mut_slice()
    }

    /// Append after the caller has reserved the complete batch.
    pub(super) fn push_reserved(&mut self, value: T) {
        assert!(
            self.len() < self.capacity(),
            "tracked batch capacity exhausted"
        );
        self.values.as_mut().unwrap().push(value);
    }

    pub(super) fn pop(&mut self) -> Option<T> {
        self.values.as_mut().unwrap().pop()
    }

    pub(super) fn clear(&mut self) {
        self.values.as_mut().unwrap().clear();
    }

    pub(super) fn truncate(&mut self, len: usize) {
        self.values.as_mut().unwrap().truncate(len);
    }

    #[cfg(test)]
    fn reserve_with(
        &mut self,
        additional: usize,
        reserve: impl FnOnce(&mut Vec<T>, usize) -> Result<(), ()>,
    ) -> Result<(), ()> {
        if self.token.meter.current_bytes().is_none() {
            return Err(());
        }
        let values = self.values.as_mut().unwrap();
        let result = reserve(values, additional);
        let accounted = self.token.reconcile::<T>(values.capacity());
        result.and(accounted)
    }

    pub(super) fn try_reserve(&mut self, additional: usize) -> Result<(), ()> {
        if self.token.meter.current_bytes().is_none() {
            return Err(());
        }
        let values = self.values.as_mut().unwrap();
        let result = values.try_reserve(additional).map_err(|_| ());
        let accounted = self.token.reconcile::<T>(values.capacity());
        result.and(accounted)
    }

    pub(super) fn try_reserve_exact(&mut self, additional: usize) -> Result<(), ()> {
        if self.token.meter.current_bytes().is_none() {
            return Err(());
        }
        let values = self.values.as_mut().unwrap();
        let result = values.try_reserve_exact(additional).map_err(|_| ());
        let accounted = self.token.reconcile::<T>(values.capacity());
        result.and(accounted)
    }

    pub(super) fn try_push(&mut self, value: T) -> Result<(), ()> {
        self.try_reserve(1)?;
        self.values.as_mut().unwrap().push(value);
        Ok(())
    }

    pub(super) fn try_clone_with(
        &self,
        mut copy: impl FnMut(&T) -> Result<T, ()>,
    ) -> Result<Self, ()> {
        let mut cloned = Self::new(self.token.meter);
        cloned.try_reserve(self.len())?;
        for item in self.iter() {
            cloned.try_push(copy(item)?)?;
        }
        Ok(cloned)
    }
}

/// Capacity charge for a raw buffer whose owner controls the drop order.
pub(super) struct TrackedAllocation<'meter>(AllocationToken<'meter>);

impl<T> Deref for TrackedVec<'_, T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.values.as_ref().unwrap()
    }
}

impl<T> Drop for TrackedVec<'_, T> {
    fn drop(&mut self) {
        drop(self.values.take());
        // `token` releases capacity after the vector allocation is gone.
    }
}

pub(super) struct TrackedIntoIter<'meter, T> {
    iter: Option<std::vec::IntoIter<T>>,
    token: AllocationToken<'meter>,
}

impl<T> Iterator for TrackedIntoIter<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.iter.as_mut().unwrap().next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.as_ref().unwrap().size_hint()
    }
}

impl<T> ExactSizeIterator for TrackedIntoIter<'_, T> {}

impl<T> DoubleEndedIterator for TrackedIntoIter<'_, T> {
    fn next_back(&mut self) -> Option<T> {
        self.iter.as_mut().unwrap().next_back()
    }
}

impl<T> Drop for TrackedIntoIter<'_, T> {
    fn drop(&mut self) {
        drop(self.iter.take());
        // `token` releases capacity after the iterator's buffer is gone.
    }
}

impl<'meter, T> IntoIterator for TrackedVec<'meter, T> {
    type Item = T;
    type IntoIter = TrackedIntoIter<'meter, T>;
    fn into_iter(mut self) -> Self::IntoIter {
        let values = self.values.take().unwrap();
        let bytes = self.token.bytes;
        self.token.bytes = 0;
        TrackedIntoIter {
            iter: Some(values.into_iter()),
            token: AllocationToken {
                meter: self.token.meter,
                bytes,
            },
        }
    }
}

/// One item with the same fallible allocation and accounting path as a vector.
pub(super) struct TrackedOne<'meter, T>(TrackedVec<'meter, T>);

impl<'meter, T> TrackedOne<'meter, T> {
    pub(super) fn try_new(meter: &'meter DraftHeapMeter, value: T) -> Result<Self, ()> {
        let mut values = TrackedVec::new(meter);
        values.try_push(value)?;
        Ok(Self(values))
    }

    pub(super) fn accounted_bytes(&self) -> usize {
        self.0.accounted_bytes()
    }

    pub(super) fn into_inner(self) -> T {
        self.0.into_iter().next().unwrap()
    }
}

impl<T> Deref for TrackedOne<'_, T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn growth_and_checked_clone() {
        let meter = DraftHeapMeter::default();
        assert_eq!(DraftHeapMeter::fixed_payload_bytes(), 0);
        let mut lane = TrackedVec::new(&meter);
        lane.try_push(3_u64).unwrap();
        lane.try_push(5).unwrap();
        assert_eq!(
            meter.current_bytes(),
            Some(lane.capacity() * size_of::<u64>())
        );
        let copy = lane.try_clone_with(|x| Ok(*x)).unwrap();
        assert_eq!(&*copy, &[3, 5]);
        assert_eq!(
            meter.current_bytes(),
            Some((lane.capacity() + copy.capacity()) * 8)
        );
        drop(copy);
        assert_eq!(meter.current_bytes(), Some(lane.accounted_bytes()));
    }

    #[test]
    fn failure_reconciles_retained_capacity_without_append() {
        let meter = DraftHeapMeter::default();
        let mut lane = TrackedVec::<u64>::new(&meter);
        let result = lane.reserve_with(4, |values, n| {
            values.try_reserve(n).unwrap();
            Err(())
        });
        assert_eq!(result, Err(()));
        assert_eq!(lane.len(), 0);
        assert_eq!(meter.current_bytes(), Some(lane.capacity() * 8));
    }

    #[test]
    fn aggregate_overflow_keeps_lane_capacity_and_poison() {
        let meter = DraftHeapMeter::default();
        meter.0.current.set(Some(usize::MAX));
        let mut lane = TrackedVec::<u64>::new(&meter);
        assert_eq!(lane.try_push(1), Err(()));
        assert_eq!(lane.len(), 0);
        assert!(lane.capacity() > 0);
        assert_eq!(lane.accounted_bytes(), lane.capacity() * 8);
        assert_eq!(meter.current_bytes(), None);
        let capacity = lane.capacity();
        let bytes = lane.accounted_bytes();
        for _ in 0..3 {
            assert_eq!(lane.try_reserve(usize::MAX), Err(()));
            assert_eq!(lane.try_reserve_exact(usize::MAX), Err(()));
            assert_eq!(lane.try_push(2), Err(()));
            assert_eq!(lane.len(), 0);
            assert_eq!(lane.capacity(), capacity);
            assert_eq!(lane.accounted_bytes(), bytes);
        }
    }

    #[test]
    fn removal_retains_capacity_charge_and_consumers() {
        let meter = DraftHeapMeter::default();
        let mut lane = TrackedVec::new(&meter);
        lane.try_reserve_exact(4).unwrap();
        lane.try_push(1_u64).unwrap();
        lane.try_push(2).unwrap();
        let bytes = lane.accounted_bytes();
        assert_eq!(lane.pop(), Some(2));
        lane.truncate(0);
        lane.try_push(3).unwrap();
        lane.clear();
        assert_eq!(meter.current_bytes(), Some(bytes));
        assert_eq!(lane.accounted_bytes(), bytes);
        drop(lane);
        assert_eq!(meter.current_bytes(), Some(0));

        let mut lane = TrackedVec::new(&meter);
        lane.try_push(4).unwrap();
        lane.try_push(5).unwrap();
        let mut iter = lane.into_iter();
        assert_eq!(iter.next_back(), Some(5));
        assert_eq!(iter.next(), Some(4));
        drop(iter);
        assert_eq!(meter.current_bytes(), Some(0));
        assert_eq!(TrackedOne::try_new(&meter, 6).unwrap().into_inner(), 6);
        assert_eq!(meter.current_bytes(), Some(0));
    }

    #[test]
    fn iterator_keeps_capacity_through_move_and_drop() {
        let meter = DraftHeapMeter::default();
        let mut lane = TrackedVec::new(&meter);
        lane.try_push(1_u64).unwrap();
        let bytes = lane.accounted_bytes();
        let mut iter = lane.into_iter();
        assert_eq!(iter.next(), Some(1));
        assert_eq!(meter.current_bytes(), Some(bytes));
        drop(iter);
        assert_eq!(meter.current_bytes(), Some(0));
    }

    #[test]
    fn elements_drop_before_capacity_release() {
        struct Witness<'a>(&'a DraftHeapMeter, std::rc::Rc<Cell<bool>>);
        impl Drop for Witness<'_> {
            fn drop(&mut self) {
                assert!(self.0.current_bytes().unwrap() > 0);
                self.1.set(true);
            }
        }
        let meter = DraftHeapMeter::default();
        let dropped = std::rc::Rc::new(Cell::new(false));
        let one = TrackedOne::try_new(&meter, Witness(&meter, dropped.clone())).unwrap();
        assert!(one.accounted_bytes() > 0);
        drop(one);
        assert!(dropped.get());
        assert_eq!(meter.current_bytes(), Some(0));
    }
}
