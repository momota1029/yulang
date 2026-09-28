//! Private physical source-draft allocation owners for the staged F5c ledger.
//!
//! The byte convention charges each vector's actual `capacity * size_of::<T>()`.
//! `current_bytes` tracks those vector buffers only. The meter state is inline
//! and contributes zero heap bytes. Each owner wrapper
//! (`size_of::<TrackedVec<T>>()` or `size_of::<TrackedOne<T>>()`) is inline in
//! its containing slot and must be classified there exactly once. Allocator
//! headers, padding outside these Rust values, and fragmentation are excluded by
//! the F5 byte convention. A zero-sized element contributes zero vector bytes.

use std::{cell::Cell, fmt, ops::Deref};

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PhysicalOwnerKind {
    Unclassified,
    SourceOuter,
    SourceSidecar,
    SourceHeldBounds,
    SourceActiveBounds,
    PositiveFunctionArgument,
    PositiveFunctionResult,
    NegativeFunctionArgument,
    NegativeFunctionResult,
    UnionChildren,
    IntersectionChildren,
    StagedOuter,
    StagedBuffer(usize),
    IndexedBuffer(usize),
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    WalkerLane(usize),
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    LiveVariableLane(usize),
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    StructuredPairLane(usize),
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    ComponentMemoLane(usize),
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    TermLane(usize),
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    InstantiationLane(usize),
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    NormalizationLane(usize),
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
mod event_sink {
    use super::PhysicalOwnerKind;
    use std::{cell::{Cell, RefCell}, fs::File, io::{BufWriter, Write}, path::Path};

    const MAGIC: &[u8; 8] = b"F5CRES01";
    pub(super) const CREATE: u64 = 1;
    pub(super) const SHAPE: u64 = 2;
    pub(super) const GROW: u64 = 3;
    pub(super) const TRANSFER: u64 = 4;
    pub(super) const RELEASE: u64 = 5;
    pub(super) const CHECKPOINT: u64 = 6;

    struct Sink { writer: BufWriter<File>, next_id: u64, count: u64, checksum: u64, failed: bool }
    thread_local! {
        static SINK: RefCell<Option<Sink>> = const { RefCell::new(None) };
        static STRUCTURED_PAIR_TOTALS: Cell<(usize, usize, usize)> = const { Cell::new((0, 0, 0)) };
        static COMPONENT_MEMO_TOTALS: Cell<(usize, usize, usize)> = const { Cell::new((0, 0, 0)) };
        static TERM_TOTALS: Cell<(usize, usize, usize)> = const { Cell::new((0, 0, 0)) };
        static INSTANTIATION_TOTALS: Cell<(usize, usize, usize)> = const { Cell::new((0, 0, 0)) };
        static NORMALIZATION_TOTALS: Cell<(usize, usize, usize)> = const { Cell::new((0, 0, 0)) };
    }

    pub(crate) fn open(path: &Path) -> std::io::Result<()> {
        let mut writer = BufWriter::new(File::create(path)?);
        writer.write_all(MAGIC)?;
        SINK.with(|slot| *slot.borrow_mut() = Some(Sink {
            writer, next_id: 1, count: 0, checksum: 0, failed: false,
        }));
        STRUCTURED_PAIR_TOTALS.with(|totals| totals.set((0, 0, 0)));
        COMPONENT_MEMO_TOTALS.with(|totals| totals.set((0, 0, 0)));
        TERM_TOTALS.with(|totals| totals.set((0, 0, 0)));
        INSTANTIATION_TOTALS.with(|totals| totals.set((0, 0, 0)));
        NORMALIZATION_TOTALS.with(|totals| totals.set((0, 0, 0)));
        Ok(())
    }

    pub(crate) fn close() -> std::io::Result<(u64, u64)> {
        SINK.with(|slot| {
            let Some(mut sink) = slot.borrow_mut().take() else {
                return Err(std::io::Error::other("F5c resource sidecar was not opened"));
            };
            sink.writer.flush()?;
            if sink.failed { return Err(std::io::Error::other("F5c resource sidecar write failed")); }
            Ok((sink.count, sink.checksum))
        })
    }

    pub(super) fn next_id() -> usize {
        SINK.with(|slot| {
            let mut slot = slot.borrow_mut();
            let Some(sink) = slot.as_mut() else { return 0; };
            let id = sink.next_id;
            sink.next_id = id.checked_add(1).expect("F5c owner ID overflow");
            usize::try_from(id).expect("F5c owner ID fits usize")
        })
    }

    pub(super) fn record(component: usize, id: usize, op: u64, kind: PhysicalOwnerKind,
        requested: usize, capacity: usize, slot_size: usize, target: u64) {
        SINK.with(|slot| {
            let mut slot = slot.borrow_mut();
            let Some(sink) = slot.as_mut() else { return; };
            let words = [component as u64, id as u64, op, kind.code(), requested as u64,
                capacity as u64, slot_size as u64, target];
            for word in words {
                if sink.writer.write_all(&word.to_le_bytes()).is_err() { sink.failed = true; }
                sink.checksum = sink.checksum.wrapping_add(word);
            }
            sink.count = sink.count.checked_add(1).expect("F5c event count overflow");
        });
    }

    pub(super) fn checkpoint(component: usize, capacity: usize, retained: usize) {
        record(component, 0, CHECKPOINT, PhysicalOwnerKind::Unclassified,
            0, capacity, retained, 0);
    }

    pub(super) fn adjust_structured_pair(capacity_delta: isize, retained_delta: isize) {
        STRUCTURED_PAIR_TOTALS.with(|cell| {
            let (capacity, retained, peak) = cell.get();
            let capacity = capacity.checked_add_signed(capacity_delta)
                .expect("family-3 event capacity");
            let retained = retained.checked_add_signed(retained_delta)
                .expect("family-3 event retained bytes");
            cell.set((capacity, retained, peak.max(retained)));
        });
    }

    pub(super) fn structured_pair_totals() -> (usize, usize, usize) {
        STRUCTURED_PAIR_TOTALS.with(Cell::get)
    }

    pub(super) fn checkpoint_structured_pair(capacity: usize, retained: usize) {
        record(0, 0, CHECKPOINT, PhysicalOwnerKind::StructuredPairLane(0),
            0, capacity, retained, 0);
    }

    pub(super) fn adjust_component_memo(capacity_delta: isize, retained_delta: isize) {
        COMPONENT_MEMO_TOTALS.with(|cell| {
            let (capacity, retained, peak) = cell.get();
            let capacity = capacity.checked_add_signed(capacity_delta).expect("family-4 capacity");
            let retained = retained.checked_add_signed(retained_delta).expect("family-4 bytes");
            cell.set((capacity, retained, peak.max(retained)));
        });
    }

    pub(super) fn component_memo_totals() -> (usize, usize, usize) {
        COMPONENT_MEMO_TOTALS.with(Cell::get)
    }

    pub(super) fn checkpoint_component_memo(capacity: usize, retained: usize) {
        record(0, 0, CHECKPOINT, PhysicalOwnerKind::ComponentMemoLane(0),
            0, capacity, retained, 0);
    }
    pub(super) fn term_totals() -> (usize, usize, usize) { TERM_TOTALS.with(Cell::get) }
    pub(super) fn normalization_totals() -> (usize, usize, usize) {
        NORMALIZATION_TOTALS.with(Cell::get)
    }
    pub(super) fn adjust_normalization(capacity_delta: isize, bytes_delta: isize) {
        NORMALIZATION_TOTALS.with(|cell| {
            let (capacity, bytes, peak) = cell.get();
            let capacity = capacity.checked_add_signed(capacity_delta)
                .expect("normalization event capacity");
            let bytes = bytes.checked_add_signed(bytes_delta)
                .expect("normalization event bytes");
            cell.set((capacity, bytes, peak.max(bytes)));
        });
    }
    pub(super) fn checkpoint_normalization(capacity: usize, bytes: usize) {
        record(0, 0, CHECKPOINT, PhysicalOwnerKind::NormalizationLane(0),
            0, capacity, bytes, 0);
    }
    pub(super) fn term_event(id: usize, op: u64, lane: usize, requested: usize,
        capacity: usize, size: usize) {
        if id == 0 { return; }
        record(0, id, op, PhysicalOwnerKind::TermLane(lane), requested, capacity, size, 0);
    }
    pub(super) fn adjust_term(capacity_delta: isize, bytes_delta: isize) {
        TERM_TOTALS.with(|cell| {
            let (capacity, bytes, peak) = cell.get();
            let capacity = capacity.checked_add_signed(capacity_delta).expect("family-2 capacity");
            let bytes = bytes.checked_add_signed(bytes_delta).expect("family-2 bytes");
            cell.set((capacity, bytes, peak.max(bytes)));
        });
    }
    pub(super) fn checkpoint_term(capacity: usize, bytes: usize) {
        record(0, 0, CHECKPOINT, PhysicalOwnerKind::TermLane(0), 0, capacity, bytes, 0);
    }
    pub(super) fn instantiation_totals() -> (usize, usize, usize) { INSTANTIATION_TOTALS.with(Cell::get) }
    pub(super) fn adjust_instantiation(capacity_delta: isize, bytes_delta: isize) {
        INSTANTIATION_TOTALS.with(|cell| {
            let (capacity, bytes, peak) = cell.get();
            let capacity = capacity.checked_add_signed(capacity_delta).expect("family-8 capacity");
            let bytes = bytes.checked_add_signed(bytes_delta).expect("family-8 bytes");
            cell.set((capacity, bytes, peak.max(bytes)));
        });
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn new_term_owner(lane: usize, requested: usize, capacity: usize, size: usize) -> usize {
    let id = event_sink::next_id();
    event_sink::term_event(id, event_sink::CREATE, lane, requested, capacity, size);
    if id != 0 { event_sink::adjust_term(capacity as isize, (capacity * size) as isize); }
    id
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn update_term_owner(id: usize, lane: usize, requested: usize, old_requested: usize,
    capacity: usize, old_capacity: usize, size: usize) {
    if capacity == old_capacity && requested == old_requested { return; }
    let op = if capacity > old_capacity { event_sink::GROW } else { event_sink::SHAPE };
    assert!(capacity >= old_capacity);
    event_sink::term_event(id, op, lane, requested, capacity, size);
    if id != 0 && capacity > old_capacity {
        let delta = capacity - old_capacity;
        event_sink::adjust_term(delta as isize, (delta * size) as isize);
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn release_term_owner(id: usize, lane: usize, capacity: usize, size: usize) {
    event_sink::term_event(id, event_sink::RELEASE, lane, 0, 0, size);
    if id != 0 { event_sink::adjust_term(-(capacity as isize), -((capacity * size) as isize)); }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn transfer_term_owner(id: usize, lane: usize, requested: usize,
    capacity: usize, size: usize) {
    if id == 0 { return; }
    event_sink::record(0, id, event_sink::TRANSFER, PhysicalOwnerKind::TermLane(lane),
        requested, capacity, size, 571 + lane as u64);
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn term_event_totals() -> (usize, usize, usize) { event_sink::term_totals() }

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn checkpoint_term_events(capacity: usize, bytes: usize) {
    event_sink::checkpoint_term(capacity, bytes);
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn instantiation_event_totals() -> (usize, usize, usize) {
    event_sink::instantiation_totals()
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn checkpoint_instantiation_events(capacity: usize, bytes: usize) {
    event_sink::record(0, 0, event_sink::CHECKPOINT,
        PhysicalOwnerKind::InstantiationLane(0), 0, capacity, bytes, 0);
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Default)]
pub(super) struct InstantiationEvents {
    owners: [Option<(usize, usize, usize, usize)>; 7],
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl InstantiationEvents {
    pub(super) fn observe(&mut self, lane: usize, requested: usize, capacity: usize, size: usize) {
        assert!(requested <= capacity && size > 0);
        let kind = PhysicalOwnerKind::InstantiationLane(lane);
        match &mut self.owners[lane] {
            None => {
                let id = event_sink::next_id();
                event_sink::record(0, id, event_sink::CREATE, kind, requested, capacity, size, 0);
                if id != 0 {
                    event_sink::adjust_instantiation(capacity as isize, (capacity * size) as isize);
                }
                self.owners[lane] = Some((id, requested, capacity, size));
            }
            Some((id, old_requested, old_capacity, old_size)) => {
                assert_eq!(*old_size, size);
                assert!(capacity >= *old_capacity, "instantiation backing shrank before release");
                let op = if capacity > *old_capacity { Some(event_sink::GROW) }
                    else if requested != *old_requested { Some(event_sink::SHAPE) } else { None };
                if let Some(op) = op {
                    event_sink::record(0, *id, op, kind, requested, capacity, size, 0);
                    if *id != 0 {
                        let delta = capacity - *old_capacity;
                        event_sink::adjust_instantiation(delta as isize, (delta * size) as isize);
                    }
                }
                *old_requested = requested;
                *old_capacity = capacity;
            }
        }
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl Drop for InstantiationEvents {
    fn drop(&mut self) {
        for (lane, owner) in self.owners.iter_mut().enumerate() {
            if let Some((id, _, capacity, size)) = owner.take() {
                event_sink::record(0, id, event_sink::RELEASE,
                    PhysicalOwnerKind::InstantiationLane(lane), 0, 0, size, 0);
                if id != 0 {
                    event_sink::adjust_instantiation(-(capacity as isize), -((capacity * size) as isize));
                }
            }
        }
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl PhysicalOwnerKind {
    fn code(self) -> u64 {
        match self {
            Self::Unclassified => 0, Self::SourceOuter => 1, Self::SourceSidecar => 2,
            Self::SourceHeldBounds => 3, Self::SourceActiveBounds => 4,
            Self::PositiveFunctionArgument => 5, Self::PositiveFunctionResult => 6,
            Self::NegativeFunctionArgument => 7, Self::NegativeFunctionResult => 8,
            Self::UnionChildren => 9, Self::IntersectionChildren => 10,
            Self::StagedOuter => 11, Self::StagedBuffer(index) => 12 + index as u64,
            Self::IndexedBuffer(index) => 18 + index as u64,
            Self::WalkerLane(index) => 32 + index as u64,
            Self::LiveVariableLane(index) => 512 + index as u64,
            Self::StructuredPairLane(index) => 530 + index as u64,
            Self::ComponentMemoLane(index) => 551 + index as u64,
            Self::TermLane(index) => 571 + index as u64,
            Self::InstantiationLane(index) => 577 + index as u64,
            Self::NormalizationLane(index) => 584 + index as u64,
        }
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) use event_sink::{close as close_f5c_resource_events, open as open_f5c_resource_events};

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn normalization_event_totals() -> (usize, usize, usize) {
    event_sink::normalization_totals()
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn checkpoint_normalization_events(capacity: usize, bytes: usize) {
    event_sink::checkpoint_normalization(capacity, bytes);
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct NormalizationOwner {
    id: usize,
    component: usize,
    lane: usize,
    requested: usize,
    capacity: usize,
    slot_size: usize,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl NormalizationOwner {
    pub(super) fn observe(&mut self, component: usize, lane: usize,
        requested: usize, capacity: usize, slot_size: usize) {
        if self.id == 0 {
            self.id = event_sink::next_id();
            self.component = component;
            self.lane = lane;
            self.slot_size = slot_size;
            event_sink::record(component, self.id, event_sink::CREATE,
                PhysicalOwnerKind::NormalizationLane(lane), 0, 0, slot_size, 0);
        }
        assert_eq!((self.component, self.lane, self.slot_size),
            (component, lane, slot_size));
        let operation = if capacity != self.capacity {
            Some(event_sink::GROW)
        } else if requested != self.requested {
            Some(event_sink::SHAPE)
        } else { None };
        if let Some(operation) = operation {
            event_sink::record(component, self.id, operation,
                PhysicalOwnerKind::NormalizationLane(lane), requested, capacity, slot_size, 0);
        }
        if self.id != 0 && capacity != self.capacity {
            let delta = capacity.checked_sub(self.capacity).expect("normalization capacity grows");
            event_sink::adjust_normalization(delta as isize, (delta * slot_size) as isize);
        }
        self.requested = requested;
        self.capacity = capacity;
    }

    pub(super) fn release(&mut self) {
        if self.id == 0 { return; }
        event_sink::record(self.component, self.id, event_sink::RELEASE,
            PhysicalOwnerKind::NormalizationLane(self.lane), 0, 0, self.slot_size, 0);
        event_sink::adjust_normalization(-(self.capacity as isize),
            -((self.capacity * self.slot_size) as isize));
        self.id = 0;
        self.capacity = 0;
        self.requested = 0;
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn checkpoint_live_variable_events(capacity: usize, retained: usize) {
    event_sink::record(0, 0, event_sink::CHECKPOINT,
        PhysicalOwnerKind::LiveVariableLane(0), 0, capacity, retained, 0);
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn structured_pair_event_totals() -> (usize, usize, usize) {
    event_sink::structured_pair_totals()
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn checkpoint_structured_pair_events(capacity: usize, retained: usize) {
    event_sink::checkpoint_structured_pair(capacity, retained);
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn component_memo_event_totals() -> (usize, usize, usize) {
    event_sink::component_memo_totals()
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn checkpoint_component_memo_events(capacity: usize, retained: usize) {
    event_sink::checkpoint_component_memo(capacity, retained);
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Default)]
pub(super) struct ComponentMemoEvents {
    owners: [Option<(usize, usize, usize, usize)>; 20],
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl ComponentMemoEvents {
    pub(super) fn observe(&mut self, lane: usize, requested: usize, capacity: usize, size: usize) {
        assert!(requested <= capacity && size > 0);
        let kind = PhysicalOwnerKind::ComponentMemoLane(lane);
        match &mut self.owners[lane] {
            None => {
                let id = event_sink::next_id();
                event_sink::record(0, id, event_sink::CREATE, kind, requested, capacity, size, 0);
                event_sink::adjust_component_memo(capacity as isize, (capacity * size) as isize);
                self.owners[lane] = Some((id, requested, capacity, size));
            }
            Some((id, old_requested, old_capacity, old_size)) => {
                assert_eq!(*old_size, size);
                let op = if capacity > *old_capacity { Some(event_sink::GROW) }
                    else if capacity == *old_capacity && requested != *old_requested {
                        Some(event_sink::SHAPE)
                    } else { None };
                assert!(capacity >= *old_capacity, "memo buffers release before capacity shrinks");
                if let Some(op) = op {
                    event_sink::record(0, *id, op, kind, requested, capacity, size, 0);
                    let delta = capacity - *old_capacity;
                    event_sink::adjust_component_memo(delta as isize, (delta * size) as isize);
                }
                *old_requested = requested;
                *old_capacity = capacity;
            }
        }
    }

    pub(super) fn release_all(&mut self) {
        for lane in 0..20 { self.release(lane); }
    }

    pub(super) fn release(&mut self, lane: usize) {
        if let Some((id, _, capacity, size)) = self.owners[lane].take() {
            event_sink::record(0, id, event_sink::RELEASE,
                PhysicalOwnerKind::ComponentMemoLane(lane), 0, 0, size, 0);
            event_sink::adjust_component_memo(-(capacity as isize), -((capacity * size) as isize));
        }
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl Drop for ComponentMemoEvents {
    fn drop(&mut self) { self.release_all(); }
}

/// One of the fixed family-3 owner buffers. The observer owns these records
/// outliving the corresponding session fields so error exits release only
/// after their actual allocations have been dropped.
#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Debug)]
pub(super) struct StructuredPairOwner {
    id: usize,
    lane: usize,
    requested: usize,
    capacity: usize,
    slot_size: usize,
    released: bool,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl StructuredPairOwner {
    pub(super) fn new(lane: usize, slot_size: usize) -> Self {
        let id = event_sink::next_id();
        event_sink::record(0, id, event_sink::CREATE,
            PhysicalOwnerKind::StructuredPairLane(lane), 0, 0, slot_size, 0);
        Self { id, lane, requested: 0, capacity: 0, slot_size, released: false }
    }

    pub(super) fn observe(&mut self, requested: usize, capacity: usize) {
        assert!(!self.released && requested <= capacity);
        let operation = if self.capacity != capacity { Some(event_sink::GROW) }
            else if self.requested != requested { Some(event_sink::SHAPE) } else { None };
        if let Some(operation) = operation {
            event_sink::record(0, self.id, operation,
                PhysicalOwnerKind::StructuredPairLane(self.lane), requested, capacity,
                self.slot_size, 0);
            if self.id != 0 {
                let capacity_delta = capacity as isize - self.capacity as isize;
                let retained_delta = capacity_delta * self.slot_size as isize;
                event_sink::adjust_structured_pair(capacity_delta, retained_delta);
            }
        }
        self.requested = requested;
        self.capacity = capacity;
    }

    pub(super) fn release(&mut self) {
        if self.released { return; }
        event_sink::record(0, self.id, event_sink::RELEASE,
            PhysicalOwnerKind::StructuredPairLane(self.lane), 0, 0, self.slot_size, 0);
        if self.id != 0 {
            event_sink::adjust_structured_pair(
                -(self.capacity as isize),
                -((self.capacity * self.slot_size) as isize),
            );
        }
        self.requested = 0;
        self.capacity = 0;
        self.released = true;
    }

    pub(super) fn transfer_same_id(&self) {
        assert!(!self.released);
        event_sink::record(0, self.id, event_sink::TRANSFER,
            PhysicalOwnerKind::StructuredPairLane(self.lane), self.requested,
            self.capacity, self.slot_size,
            PhysicalOwnerKind::StructuredPairLane(self.lane).code());
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl Drop for StructuredPairOwner {
    fn drop(&mut self) { self.release(); }
}

/// Compact per-`TypedPairMemo::Value.children` identity. Requested length is
/// supplied at each mutation; only capacity must survive until owner drop.
#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Debug)]
pub(super) struct StructuredPairChildOwner {
    id: usize,
    capacity: usize,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl StructuredPairChildOwner {
    pub(super) fn new(slot_size: usize) -> Self {
        Self::new_with_shape(slot_size, 0, 0)
    }

    pub(super) fn new_with_shape(slot_size: usize, requested: usize, capacity: usize) -> Self {
        assert!(requested <= capacity);
        let id = event_sink::next_id();
        event_sink::record(0, id, event_sink::CREATE,
            PhysicalOwnerKind::StructuredPairLane(1), requested, capacity, slot_size, 0);
        if id != 0 {
            event_sink::adjust_structured_pair(
                capacity as isize,
                (capacity * slot_size) as isize,
            );
        }
        Self { id, capacity }
    }

    pub(super) fn observe_growth(&mut self, requested: usize, capacity: usize, slot_size: usize) {
        assert!(requested <= capacity && capacity >= self.capacity);
        if self.id == 0 {
            self.capacity = capacity;
            return;
        }
        if capacity == self.capacity { return; }
        event_sink::record(0, self.id, event_sink::GROW,
            PhysicalOwnerKind::StructuredPairLane(1), requested, capacity, slot_size, 0);
        let delta = (capacity - self.capacity) as isize;
        event_sink::adjust_structured_pair(delta, delta * slot_size as isize);
        self.capacity = capacity;
    }

    pub(super) fn observe_shape(&mut self, requested: usize, capacity: usize, slot_size: usize) {
        assert!(requested <= capacity && capacity == self.capacity);
        if self.id == 0 { return; }
        event_sink::record(0, self.id, event_sink::SHAPE,
            PhysicalOwnerKind::StructuredPairLane(1), requested, capacity, slot_size, 0);
    }

    pub(super) fn activate(&mut self, requested: usize, capacity: usize, slot_size: usize) {
        assert!(requested <= capacity);
        if self.id == 0 {
            *self = Self::new_with_shape(slot_size, requested, capacity);
        } else {
            assert_eq!(self.capacity, capacity);
        }
    }

    pub(super) fn clone_for_shape(&self, requested: usize, capacity: usize, slot_size: usize) -> Self {
        Self::new_with_shape(slot_size, requested, capacity)
    }

    pub(super) fn release(&mut self, slot_size: usize) {
        if self.id == 0 { self.capacity = 0; return; }
        event_sink::record(0, self.id, event_sink::RELEASE,
            PhysicalOwnerKind::StructuredPairLane(1), 0, 0, slot_size, 0);
        event_sink::adjust_structured_pair(
            -(self.capacity as isize),
            -((self.capacity * slot_size) as isize),
        );
        self.capacity = 0;
        self.id = 0;
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Clone, Debug)]
pub(super) struct LiveVariableOwner {
    id: usize,
    lane: usize,
    requested: usize,
    capacity: usize,
    slot_size: usize,
    released: bool,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl LiveVariableOwner {
    pub(super) fn new(lane: usize, slot_size: usize) -> Self {
        let id = event_sink::next_id();
        event_sink::record(0, id, event_sink::CREATE,
            PhysicalOwnerKind::LiveVariableLane(lane), 0, 0, slot_size, 0);
        Self { id, lane, requested: 0, capacity: 0, slot_size, released: false }
    }

    pub(super) fn observe(&mut self, requested: usize, capacity: usize) -> (isize, isize) {
        assert!(!self.released && requested <= capacity);
        let operation = if self.capacity != capacity { Some(event_sink::GROW) }
            else if self.requested != requested { Some(event_sink::SHAPE) } else { None };
        if let Some(operation) = operation {
            event_sink::record(0, self.id, operation,
                PhysicalOwnerKind::LiveVariableLane(self.lane), requested, capacity,
                self.slot_size, 0);
        }
        let capacity_delta = capacity as isize - self.capacity as isize;
        let bytes_delta = capacity_delta * self.slot_size as isize;
        self.requested = requested;
        self.capacity = capacity;
        (capacity_delta, bytes_delta)
    }

    pub(super) fn release(&mut self) -> (isize, isize) {
        assert!(!self.released);
        event_sink::record(0, self.id, event_sink::RELEASE,
            PhysicalOwnerKind::LiveVariableLane(self.lane), 0, 0, self.slot_size, 0);
        self.released = true;
        let delta = (-(self.capacity as isize),
            -((self.capacity * self.slot_size) as isize));
        self.requested = 0;
        self.capacity = 0;
        delta
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) struct FlatDraftOwner {
    component: usize,
    id: usize,
    lane: usize,
    capacity: usize,
    slot_size: usize,
    requested: usize,
    peak_requested: usize,
    transferred: bool,
    kind: PhysicalOwnerKind,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl FlatDraftOwner {
    pub(super) fn new(meter: &DraftHeapMeter, lane: usize, slot_size: usize) -> Self {
        Self::new_with_component(meter.0.event_component.get(), lane, slot_size)
    }

    pub(super) fn new_with_component(component: usize, lane: usize, slot_size: usize) -> Self {
        Self::new_with_kind(component, lane, slot_size, PhysicalOwnerKind::WalkerLane(lane))
    }

    pub(super) fn new_normalization(component: usize, lane: usize, slot_size: usize) -> Self {
        Self::new_with_kind(component, lane, slot_size,
            PhysicalOwnerKind::NormalizationLane(lane))
    }

    fn new_with_kind(component: usize, lane: usize, slot_size: usize,
        kind: PhysicalOwnerKind) -> Self {
        let id = event_sink::next_id();
        event_sink::record(component, id, event_sink::CREATE,
            kind, 0, 0, slot_size, 0);
        Self { component, id, lane, capacity: 0, slot_size,
            requested: 0, peak_requested: 0, transferred: false, kind }
    }

    pub(super) fn observe(&mut self, requested: usize, capacity: usize) {
        let operation = if capacity != self.capacity {
            Some(event_sink::GROW)
        } else if requested != self.requested {
            Some(event_sink::SHAPE)
        } else {
            None
        };
        if let Some(operation) = operation {
            event_sink::record(self.component, self.id, operation,
                self.kind, requested, capacity,
                self.slot_size, 0);
        }
        if self.id != 0 && matches!(self.kind, PhysicalOwnerKind::NormalizationLane(_))
            && capacity != self.capacity {
            let delta = capacity.checked_sub(self.capacity).expect("normalization output grows");
            event_sink::adjust_normalization(delta as isize, (delta * self.slot_size) as isize);
        }
        self.capacity = capacity;
        self.requested = requested;
        self.peak_requested = self.peak_requested.max(requested);
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl Drop for FlatDraftOwner {
    fn drop(&mut self) {
        if !self.transferred {
            event_sink::record(self.component, self.id, event_sink::RELEASE,
                self.kind, 0, 0, self.slot_size, 0);
            if self.id != 0 && matches!(self.kind, PhysicalOwnerKind::NormalizationLane(_)) {
                event_sink::adjust_normalization(-(self.capacity as isize),
                    -((self.capacity * self.slot_size) as isize));
            }
        }
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) struct RawWalkerOwner<'meter> {
    meter: &'meter DraftHeapMeter,
    id: usize,
    lane: usize,
    capacity: usize,
    slot_size: usize,
    requested: usize,
    transferred: bool,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<'meter> RawWalkerOwner<'meter> {
    pub(super) fn new(meter: &'meter DraftHeapMeter, lane: usize, slot_size: usize) -> Self {
        let id = event_sink::next_id();
        event_sink::record(meter.0.event_component.get(), id, event_sink::CREATE,
            PhysicalOwnerKind::WalkerLane(lane), 0, 0, slot_size, 0);
        Self { meter, id, lane, capacity: 0, slot_size,
            requested: 0, transferred: false }
    }

    pub(super) fn observe(&mut self, requested: usize, capacity: usize) {
        let operation = if capacity != self.capacity {
            Some(event_sink::GROW)
        } else if requested != self.requested {
            Some(event_sink::SHAPE)
        } else {
            None
        };
        if let Some(operation) = operation {
            event_sink::record(self.meter.0.event_component.get(), self.id, operation,
                PhysicalOwnerKind::WalkerLane(self.lane), requested, capacity, self.slot_size, 0);
        }
        self.capacity = capacity;
        self.requested = requested;
    }

    fn transfer(&mut self, kind: PhysicalOwnerKind, requested: usize) -> usize {
        assert!(!self.transferred);
        self.transferred = true;
        event_sink::record(self.meter.0.event_component.get(), self.id, event_sink::TRANSFER,
            kind, requested, self.capacity, self.slot_size, kind.code());
        self.id
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl Drop for RawWalkerOwner<'_> {
    fn drop(&mut self) {
        if !self.transferred {
            event_sink::record(self.meter.0.event_component.get(), self.id, event_sink::RELEASE,
                PhysicalOwnerKind::WalkerLane(self.lane), 0, 0, self.slot_size, 0);
        }
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Clone, Copy, Debug)]
struct PhysicalOwnerHandle { slot: usize, id: usize }

#[cfg(all(test, not(feature = "f5c_resource_probe")))]
type PhysicalOwnerHandle = usize;

#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Clone, Copy)]
struct PhysicalOwnerEntry {
    capacity: usize, slot_size: usize, id: usize, kind: PhysicalOwnerKind,
    requested: usize, peak_requested: usize, adopting: bool,
}
#[cfg(all(test, not(feature = "f5c_resource_probe")))]
type PhysicalOwnerEntry = (usize, usize);

#[cfg(test)]
fn dead_physical_handle() -> PhysicalOwnerHandle {
    #[cfg(feature = "f5c_resource_probe")]
    { PhysicalOwnerHandle { slot: 0, id: 0 } }
    #[cfg(not(feature = "f5c_resource_probe"))]
    { 0 }
}

struct MeterState {
    current: Cell<Option<usize>>,
    normalization_scratch: Cell<Option<usize>>,
    normalization_joint_peak: Cell<Option<usize>>,
    component_external: Cell<Option<usize>>,
    component_joint_peak: Cell<Option<usize>>,
    #[cfg(test)]
    physical_current: Cell<Option<usize>>,
    #[cfg(test)]
    physical_owners: std::cell::RefCell<Vec<Option<PhysicalOwnerEntry>>>,
    #[cfg(test)]
    free_physical_owners: std::cell::RefCell<Vec<usize>>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    event_component: Cell<usize>,
    #[cfg(test)]
    physical_component_external: Cell<Option<usize>>,
    #[cfg(test)]
    physical_joint_peak: Cell<Option<usize>>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    family6_walker_current: Cell<usize>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    family6_source_capacity: Cell<Option<usize>>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    family6_walker_capacity: Cell<usize>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    family6_event_peak: Cell<Option<usize>>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    family6_event_count: Cell<usize>,
}

impl Default for MeterState {
    fn default() -> Self {
        Self {
            current: Cell::new(Some(0)),
            normalization_scratch: Cell::new(None),
            normalization_joint_peak: Cell::new(None),
            component_external: Cell::new(None),
            component_joint_peak: Cell::new(None),
            #[cfg(test)]
            physical_current: Cell::new(Some(0)),
            #[cfg(test)]
            physical_owners: std::cell::RefCell::new(vec![None]),
            #[cfg(test)]
            free_physical_owners: std::cell::RefCell::new(Vec::new()),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            event_component: Cell::new(0),
            #[cfg(test)]
            physical_component_external: Cell::new(None),
            #[cfg(test)]
            physical_joint_peak: Cell::new(None),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            family6_walker_current: Cell::new(0),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            family6_source_capacity: Cell::new(Some(0)),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            family6_walker_capacity: Cell::new(0),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            family6_event_peak: Cell::new(Some(0)),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            family6_event_count: Cell::new(0),
        }
    }
}

/// Shared aggregate of live vector capacities. `None` means arithmetic
/// exhaustion; no later release claims to reconstruct an exact total.
#[derive(Default)]
pub(super) struct DraftHeapMeter(MeterState);

impl DraftHeapMeter {
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn event_component(&self) -> usize {
        self.0.event_component.get()
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn claim_existing_batch_with_owners<'meter>(
        &'meter self,
        bytes: [usize; 6],
        future_external: usize,
        owners: &mut [FlatDraftOwner; 6],
        requested: [usize; 6],
        capacities: [usize; 6],
        sizes: [usize; 6],
    ) -> Result<[TrackedAllocation<'meter>; 6], ()> {
        let added = bytes.iter().try_fold(0usize, |sum, byte| sum.checked_add(*byte))
            .ok_or(())?;
        let next = self.current_bytes().ok_or(())?.checked_add(added).ok_or(())?;
        self.0.physical_current.get().ok_or(())?.checked_add(added).ok_or(())?;
        if self.0.component_external.get().is_some() {
            next.checked_add(future_external).ok_or(())?;
        }
        for (index, owner) in owners.iter().enumerate() {
            if owner.component != self.0.event_component.get()
                || owner.transferred
                || owner.capacity != capacities[index]
                || owner.slot_size != sizes[index]
                || owner.capacity.checked_mul(owner.slot_size) != Some(bytes[index])
            {
                return Err(());
            }
        }
        self.0.current.set(Some(next));
        let allocations = std::array::from_fn(|index| {
            let owner = &mut owners[index];
            let kind = PhysicalOwnerKind::StagedBuffer(index);
            let handle = self.register_physical_owner_id(bytes[index], kind, owner.id,
                false, false);
            {
                let mut registry = self.0.physical_owners.borrow_mut();
                let entry = registry[handle.slot].as_mut().expect("transferred draft owner");
                entry.capacity = owner.capacity;
                entry.slot_size = owner.slot_size;
                entry.requested = requested[index];
                entry.peak_requested = owner.peak_requested.max(requested[index]);
                entry.adopting = false;
            }
            self.0.family6_source_capacity.set(self.0.family6_source_capacity.get()
                .and_then(|current| current.checked_sub(bytes[index])?
                    .checked_add(owner.capacity)));
            owner.transferred = true;
            if owner.id != 0 && matches!(owner.kind, PhysicalOwnerKind::NormalizationLane(_)) {
                event_sink::adjust_normalization(-(owner.capacity as isize),
                    -((owner.capacity * owner.slot_size) as isize));
            }
            event_sink::record(owner.component, owner.id, event_sink::TRANSFER,
                kind, requested[index], owner.capacity, owner.slot_size, kind.code());
            TrackedAllocation(AllocationToken { meter: self, bytes: bytes[index],
                physical_owner: handle })
        });
        Ok(allocations)
    }
    /// Claim already allocated buffers as one checked transfer. The caller
    /// releases their former ledger lanes before the next observation.
    pub(super) fn claim_existing_batch<'meter>(
        &'meter self,
        bytes: [usize; 6],
        future_external: usize,
    ) -> Result<[TrackedAllocation<'meter>; 6], ()> {
        let added = bytes
            .iter()
            .try_fold(0usize, |sum, byte| sum.checked_add(*byte))
            .ok_or(())?;
        let next = self
            .current_bytes()
            .ok_or(())?
            .checked_add(added)
            .ok_or(())?;
        if self.0.component_external.get().is_some() {
            next.checked_add(future_external).ok_or(())?;
        }
        self.0.current.set(Some(next));
        Ok(std::array::from_fn(|index| TrackedAllocation(
            AllocationToken::new_with_kind(
                self, bytes[index], PhysicalOwnerKind::StagedBuffer(index),
            ))))
    }
    pub(super) fn begin_component(&self) -> Result<(), ()> {
        let current = self.current_bytes().ok_or(())?;
        self.0.component_external.set(Some(0));
        self.0.component_joint_peak.set(Some(current));
        #[cfg(test)]
        self.0.physical_component_external.set(Some(0));
        #[cfg(test)]
        self.0
            .physical_joint_peak
            .set(self.0.physical_current.get());
        Ok(())
    }

    pub(super) fn observe_component_external(&self, bytes: usize) -> Result<(), ()> {
        if self.0.component_external.get().is_none() {
            return Ok(());
        }
        self.0.component_external.set(Some(bytes));
        self.observe_component_joint()
    }

    #[cfg(test)]
    pub(super) fn observe_component_external_pair(
        &self,
        bytes: usize,
        physical_bytes: usize,
    ) -> Result<(), ()> {
        if self.0.component_external.get().is_none() {
            return Ok(());
        }
        self.0.component_external.set(Some(bytes));
        self.0.physical_component_external.set(Some(physical_bytes));
        self.observe_component_joint()
    }

    #[cfg(test)]
    pub(super) fn observe_physical_component_external(&self, bytes: usize) -> Result<(), ()> {
        if self.0.physical_component_external.get().is_none() {
            return Ok(());
        }
        self.0.physical_component_external.set(Some(bytes));
        self.observe_component_joint()
    }

    pub(super) fn end_component(&self) -> Option<usize> {
        self.0.component_external.set(None);
        #[cfg(test)]
        self.0.physical_component_external.set(None);
        self.0.component_joint_peak.replace(None)
    }

    pub(super) fn component_joint_peak(&self) -> Option<usize> {
        self.0.component_joint_peak.get()
    }

    #[cfg(test)]
    pub(super) fn physical_component_joint_peak(&self) -> Option<usize> {
        self.0.physical_joint_peak.get()
    }

    fn observe_component_joint(&self) -> Result<(), ()> {
        if let Some(external) = self.0.component_external.get() {
            let Some(joint) = self
                .current_bytes()
                .and_then(|bytes| bytes.checked_add(external))
            else {
                self.0.current.set(None);
                return Err(());
            };
            self.0.component_joint_peak.set(Some(
                self.0.component_joint_peak.get().unwrap_or(0).max(joint),
            ));
            #[cfg(test)]
            {
                let physical =
                    self.0.physical_current.get().and_then(|bytes| {
                        bytes.checked_add(self.0.physical_component_external.get()?)
                    });
                self.0.physical_joint_peak.set(
                    match (self.0.physical_joint_peak.get(), physical) {
                        (Some(old), Some(next)) => Some(old.max(next)),
                        _ => None,
                    },
                );
            }
        }
        Ok(())
    }
    pub(super) fn begin_normalization(&self) -> Result<(), ()> {
        let current = self.current_bytes().ok_or(())?;
        self.0.normalization_scratch.set(Some(0));
        self.0.normalization_joint_peak.set(Some(current));
        Ok(())
    }

    pub(super) fn observe_normalization_scratch(&self, bytes: usize) -> Result<(), ()> {
        self.0.normalization_scratch.set(Some(bytes));
        self.observe_normalization_joint()
    }

    pub(super) fn end_normalization(&self) -> Option<usize> {
        self.0.normalization_scratch.set(None);
        self.0.normalization_joint_peak.replace(None)
    }

    fn observe_normalization_joint(&self) -> Result<(), ()> {
        if let Some(scratch) = self.0.normalization_scratch.get() {
            let Some(joint) = self
                .current_bytes()
                .and_then(|bytes| bytes.checked_add(scratch))
            else {
                self.0.current.set(None);
                return Err(());
            };
            self.0.normalization_joint_peak.set(Some(
                self.0
                    .normalization_joint_peak
                    .get()
                    .unwrap_or(0)
                    .max(joint),
            ));
        }
        Ok(())
    }

    pub(super) fn current_bytes(&self) -> Option<usize> {
        self.0.current.get()
    }

    #[cfg(test)]
    pub(super) fn physical_current_bytes(&self) -> Option<usize> {
        self.0.physical_current.get()
    }

    #[cfg(test)]
    pub(super) fn physical_owner_bytes(&self) -> Option<usize> {
        self.0
            .physical_owners
            .borrow()
            .iter()
            .flatten()
            .try_fold(0usize, |sum, owner| {
                #[cfg(feature = "f5c_resource_probe")]
                let (capacity, slot_size) = (owner.capacity, owner.slot_size);
                #[cfg(not(feature = "f5c_resource_probe"))]
                let (capacity, slot_size) = (owner.0, owner.1);
                sum.checked_add(capacity.checked_mul(slot_size)?)
            })
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn set_event_component(&self, component: usize) {
        self.0.event_component.set(component);
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn record_event_checkpoint(&self, capacity: usize, retained: usize) {
        event_sink::checkpoint(self.0.event_component.get(), capacity, retained);
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn family6_event_peak(&self) -> Option<usize> {
        self.0.family6_event_peak.get()
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn family6_event_count(&self) -> usize {
        self.0.family6_event_count.get()
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn family6_event_current(&self) -> Option<(usize, usize)> {
        Some((self.0.family6_source_capacity.get()?
            .checked_add(self.0.family6_walker_capacity.get())?,
            self.0.physical_current.get()?
                .checked_add(self.0.family6_walker_current.get())?))
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn observe_family6_walker(&self, bytes: usize, capacity: usize) {
        self.0.family6_walker_current.set(bytes);
        self.0.family6_walker_capacity.set(capacity);
        self.sample_family6_event();
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn sample_family6_event(&self) {
        let current = self.0.physical_current.get().and_then(|source|
            source.checked_add(self.0.family6_walker_current.get()));
        self.0.family6_event_peak.set(match (self.0.family6_event_peak.get(), current) {
            (Some(old), Some(now)) => Some(old.max(now)),
            _ => None,
        });
        self.0.family6_event_count.set(self.0.family6_event_count.get() + 1);
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn register_physical_owner(&self, bytes: usize, kind: PhysicalOwnerKind) -> PhysicalOwnerHandle {
        self.register_physical_owner_id(bytes, kind, event_sink::next_id(), true, true)
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn register_physical_owner_id(&self, bytes: usize, kind: PhysicalOwnerKind,
        owner_id: usize, create: bool, sample: bool) -> PhysicalOwnerHandle {
        let mut owners = self.0.physical_owners.borrow_mut();
        let entry = PhysicalOwnerEntry { capacity: bytes, slot_size: 1, id: owner_id,
            kind, requested: 0, peak_requested: 0, adopting: !create };
        let id = if let Some(id) = self.0.free_physical_owners.borrow_mut().pop() {
            assert!(owners[id].replace(entry).is_none());
            id
        } else {
            let id = owners.len();
            owners.push(Some(entry));
            id
        };
        self.0.physical_current.set(
            self.0
                .physical_current
                .get()
                .and_then(|total| total.checked_add(bytes)),
        );
        self.0.family6_source_capacity.set(self.0.family6_source_capacity.get()
            .and_then(|current| current.checked_add(bytes)));
        if sample { self.sample_family6_event(); }
        if create {
            event_sink::record(self.0.event_component.get(), owner_id, event_sink::CREATE,
                kind, 0, bytes, 1, 0);
        }
        PhysicalOwnerHandle { slot: id, id: owner_id }
    }

    #[cfg(all(test, not(feature = "f5c_resource_probe")))]
    fn register_physical_owner(&self, bytes: usize, _kind: PhysicalOwnerKind) -> PhysicalOwnerHandle {
        let mut owners = self.0.physical_owners.borrow_mut();
        let slot = if let Some(slot) = self.0.free_physical_owners.borrow_mut().pop() {
            assert!(owners[slot].replace((bytes, 1)).is_none());
            slot
        } else {
            let slot = owners.len();
            owners.push(Some((bytes, 1)));
            slot
        };
        self.0.physical_current.set(self.0.physical_current.get()
            .and_then(|total| total.checked_add(bytes)));
        slot
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn replace_physical_owner(&self, handle: PhysicalOwnerHandle, capacity: usize, slot_size: usize, sample_event: bool) {
        let mut owners = self.0.physical_owners.borrow_mut();
        let owner = owners[handle.slot].as_mut().expect("live physical source owner");
        assert_eq!(owner.id, handle.id, "physical owner generation");
        let (old_capacity, old_size) = (owner.capacity, owner.slot_size);
        owner.capacity = capacity;
        owner.slot_size = slot_size;
        let (kind, requested, adopting) = (owner.kind, owner.requested, owner.adopting);
        self.0
            .physical_current
            .set(self.0.physical_current.get().and_then(|total| {
                total
                    .checked_sub(old_capacity.checked_mul(old_size)?)?
                    .checked_add(capacity.checked_mul(slot_size)?)
            }));
        #[cfg(feature = "f5c_resource_probe")]
        self.0.family6_source_capacity.set(self.0.family6_source_capacity.get()
            .and_then(|current| current.checked_sub(old_capacity)?
                .checked_add(capacity)));
        #[cfg(feature = "f5c_resource_probe")]
        if sample_event { self.sample_family6_event(); }
        if !adopting && (capacity != old_capacity || slot_size != old_size) {
            event_sink::record(self.0.event_component.get(), handle.id,
                if slot_size != old_size { event_sink::SHAPE } else { event_sink::GROW },
                kind, requested, capacity, slot_size, 0);
        }
    }

    #[cfg(all(test, not(feature = "f5c_resource_probe")))]
    fn replace_physical_owner(&self, slot: PhysicalOwnerHandle, capacity: usize, slot_size: usize, _sample_event: bool) {
        let (old_capacity, old_size) = self.0.physical_owners.borrow_mut()[slot]
            .replace((capacity, slot_size)).expect("live physical source owner");
        self.0.physical_current.set(self.0.physical_current.get().and_then(|total| {
            total.checked_sub(old_capacity.checked_mul(old_size)?)?
                .checked_add(capacity.checked_mul(slot_size)?)
        }));
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn release_physical_owner(&self, handle: PhysicalOwnerHandle) {
        if handle.slot == 0 {
            return;
        }
        let owner = self.0.physical_owners.borrow_mut()[handle.slot]
            .take()
            .expect("live physical source owner");
        let (capacity, slot_size) = (owner.capacity, owner.slot_size);
        assert_eq!(owner.id, handle.id, "physical owner generation");
        self.0.physical_current.set(
            self.0
                .physical_current
                .get()
                .and_then(|total| total.checked_sub(capacity.checked_mul(slot_size)?)),
        );
        #[cfg(feature = "f5c_resource_probe")]
        self.0.family6_source_capacity.set(self.0.family6_source_capacity.get()
            .and_then(|current| current.checked_sub(capacity)));
        #[cfg(feature = "f5c_resource_probe")]
        self.sample_family6_event();
        if !owner.adopting {
            event_sink::record(self.0.event_component.get(), handle.id, event_sink::RELEASE,
                owner.kind, 0, 0, slot_size, 0);
        }
        self.0.free_physical_owners.borrow_mut().push(handle.slot);
    }

    #[cfg(all(test, not(feature = "f5c_resource_probe")))]
    fn release_physical_owner(&self, slot: PhysicalOwnerHandle) {
        if slot == 0 { return; }
        let (capacity, slot_size) = self.0.physical_owners.borrow_mut()[slot]
            .take().expect("live physical source owner");
        self.0.physical_current.set(self.0.physical_current.get()
            .and_then(|total| total.checked_sub(capacity.checked_mul(slot_size)?)));
        self.0.free_physical_owners.borrow_mut().push(slot);
    }

    #[cfg(test)]
    fn physical_owner_requested(&self, handle: PhysicalOwnerHandle, requested: usize) {
        #[cfg(feature = "f5c_resource_probe")]
        {
            let mut owners = self.0.physical_owners.borrow_mut();
            let owner = owners[handle.slot].as_mut().expect("live physical owner");
            assert_eq!(owner.id, handle.id);
            owner.requested = requested;
            owner.peak_requested = owner.peak_requested.max(requested);
        }
        #[cfg(not(feature = "f5c_resource_probe"))]
        let _ = (handle, requested);
    }

    #[cfg(test)]
    fn physical_owner_transfer(&self, handle: PhysicalOwnerHandle) {
        #[cfg(feature = "f5c_resource_probe")]
        {
            let owners = self.0.physical_owners.borrow();
            let owner = owners[handle.slot].as_ref().expect("live physical owner");
            event_sink::record(self.0.event_component.get(), handle.id, event_sink::TRANSFER,
                owner.kind, owner.requested, owner.capacity, owner.slot_size, owner.kind.code());
        }
        #[cfg(not(feature = "f5c_resource_probe"))]
        let _ = handle;
    }

    pub(super) const fn fixed_payload_bytes() -> usize {
        0
    }

    fn replace(&self, old: usize, new: usize) -> Result<(), ()> {
        self.replace_with_component_sample(old, new, true)
    }

    fn replace_with_component_sample(
        &self,
        old: usize,
        new: usize,
        sample_component: bool,
    ) -> Result<(), ()> {
        let Some(current) = self.current_bytes() else {
            return Err(());
        };
        let Some(next) = current.checked_sub(old).and_then(|n| n.checked_add(new)) else {
            self.0.current.set(None);
            return Err(());
        };
        self.0.current.set(Some(next));
        if new > old {
            self.observe_normalization_joint()?;
        }
        if sample_component {
            self.observe_component_joint()?;
        }
        Ok(())
    }

    fn release(&self, bytes: usize) {
        if let Some(current) = self.current_bytes() {
            self.0.current.set(current.checked_sub(bytes));
        }
        let _ = self.observe_component_joint();
    }
}

struct AllocationToken<'meter> {
    meter: &'meter DraftHeapMeter,
    bytes: usize,
    #[cfg(test)]
    physical_owner: PhysicalOwnerHandle,
}

impl AllocationToken<'_> {
    fn new(meter: &DraftHeapMeter, bytes: usize) -> AllocationToken<'_> {
        Self::new_with_kind(meter, bytes, PhysicalOwnerKind::Unclassified)
    }

    fn new_with_kind(meter: &DraftHeapMeter, bytes: usize, kind: PhysicalOwnerKind) -> AllocationToken<'_> {
        #[cfg(not(test))]
        let _ = kind;
        AllocationToken {
            meter,
            bytes,
            #[cfg(test)]
            physical_owner: meter.register_physical_owner(bytes, kind),
        }
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn new_with_existing_owner(meter: &DraftHeapMeter, kind: PhysicalOwnerKind,
        id: usize) -> AllocationToken<'_> {
        AllocationToken { meter, bytes: 0,
            physical_owner: meter.register_physical_owner_id(0, kind, id, false, true) }
    }


    fn reconcile<T>(&mut self, capacity: usize) -> Result<(), ()> {
        self.reconcile_with_component_sample::<T>(capacity, true)
    }

    fn reconcile_with_component_sample<T>(
        &mut self,
        capacity: usize,
        sample_component: bool,
    ) -> Result<(), ()> {
        #[cfg(test)]
        self.meter
            .replace_physical_owner(self.physical_owner, capacity, size_of::<T>(), sample_component);
        let Some(bytes) = capacity.checked_mul(size_of::<T>()) else {
            self.meter.0.current.set(None);
            return Err(());
        };
        // Retain the lane's actual capacity even when the aggregate overflows.
        let result = if sample_component {
            self.meter.replace(self.bytes, bytes)
        } else {
            self.meter
                .replace_with_component_sample(self.bytes, bytes, false)
        };
        self.bytes = bytes;
        result
    }
}

impl Drop for AllocationToken<'_> {
    fn drop(&mut self) {
        self.meter.release(self.bytes);
        #[cfg(test)]
        self.meter.release_physical_owner(self.physical_owner);
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
        Self::new_with_kind(meter, PhysicalOwnerKind::Unclassified)
    }

    pub(super) fn new_with_kind(meter: &'meter DraftHeapMeter, kind: PhysicalOwnerKind) -> Self {
        Self {
            values: Some(Vec::new()),
            token: AllocationToken::new_with_kind(meter, 0, kind),
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

    /// Take over an existing vector buffer without allocating another one.
    /// The caller keeps the scratch-lane charge until adoption succeeds, then
    /// releases that charge before any fallible work or resource observation.
    /// On failure, the caller drops the returned buffer before releasing its
    /// scratch-lane charge.
    pub(super) fn try_adopt_raw(
        meter: &'meter DraftHeapMeter,
        values: Vec<T>,
    ) -> Result<Self, (Vec<T>, ())> {
        let mut owned = Self {
            values: Some(values),
            token: AllocationToken::new(meter, 0),
        };
        match owned.token.reconcile::<T>(owned.capacity()) {
            Ok(()) => Ok(owned),
            Err(()) => Err((owned.values.take().unwrap(), ())),
        }
    }

    /// The walker lane still owns this buffer's physical charge until its
    /// release. The caller must release that lane before the next component
    /// peak observation.
    pub(super) fn try_adopt_raw_from_walker(
        meter: &'meter DraftHeapMeter,
        values: Vec<T>,
    ) -> Result<Self, (Vec<T>, ())> {
        Self::try_adopt_raw_from_walker_with_kind(
            meter, values, PhysicalOwnerKind::Unclassified,
        )
    }

    pub(super) fn try_adopt_raw_from_walker_with_kind(
        meter: &'meter DraftHeapMeter,
        values: Vec<T>,
        kind: PhysicalOwnerKind,
    ) -> Result<Self, (Vec<T>, ())> {
        let mut owned = Self {
            values: Some(values),
            token: AllocationToken::new_with_kind(meter, 0, kind),
        };
        match owned
            .token
            .reconcile_with_component_sample::<T>(owned.capacity(), false)
        {
            Ok(()) => {
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                {
                    let handle = owned.token.physical_owner;
                    meter.physical_owner_requested(handle, owned.len());
                    meter.physical_owner_transfer(handle);
                }
                Ok(owned)
            },
            Err(()) => Err((owned.values.take().unwrap(), ())),
        }
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn try_adopt_raw_from_walker_with_owner(
        meter: &'meter DraftHeapMeter, values: Vec<T>, kind: PhysicalOwnerKind,
        mut raw_owner: RawWalkerOwner<'meter>,
    ) -> Result<Self, (Vec<T>, RawWalkerOwner<'meter>)> {
        assert_eq!(raw_owner.capacity, values.capacity());
        let mut owned = Self { values: Some(values),
            token: AllocationToken::new_with_existing_owner(meter, kind, raw_owner.id) };
        match owned.token.reconcile_with_component_sample::<T>(owned.capacity(), false) {
            Ok(()) => {
                raw_owner.transfer(kind, owned.len());
                meter.0.physical_owners.borrow_mut()
                    [owned.token.physical_owner.slot].as_mut()
                    .expect("adopted physical owner").adopting = false;
                meter.physical_owner_requested(owned.token.physical_owner, owned.len());
                Ok(owned)
            }
            Err(()) => Err((owned.values.take().unwrap(), raw_owner)),
        }
    }

    /// Transfer the charge with an unchanged raw buffer. The returned token
    /// must outlive the raw buffer and all of its elements.
    pub(super) fn into_raw_with_token(mut self) -> (Vec<T>, TrackedAllocation<'meter>) {
        let values = self.values.take().unwrap();
        let bytes = std::mem::replace(&mut self.token.bytes, 0);
        #[cfg(test)]
        let physical_owner = std::mem::replace(&mut self.token.physical_owner,
            dead_physical_handle());
        #[cfg(test)]
        self.token.meter.physical_owner_transfer(physical_owner);
        (
            values,
            TrackedAllocation(AllocationToken {
                meter: self.token.meter,
                bytes,
                #[cfg(test)]
                physical_owner,
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
        #[cfg(test)]
        self.token.meter.physical_owner_requested(self.token.physical_owner, self.len());
    }

    pub(super) fn pop(&mut self) -> Option<T> {
        let value = self.values.as_mut().unwrap().pop();
        #[cfg(test)]
        self.token.meter.physical_owner_requested(self.token.physical_owner, self.len());
        value
    }

    pub(super) fn clear(&mut self) {
        self.values.as_mut().unwrap().clear();
        #[cfg(test)]
        self.token.meter.physical_owner_requested(self.token.physical_owner, 0);
    }

    pub(super) fn truncate(&mut self, len: usize) {
        self.values.as_mut().unwrap().truncate(len);
        #[cfg(test)]
        self.token.meter.physical_owner_requested(self.token.physical_owner, self.len());
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
        #[cfg(test)]
        self.token.meter.physical_owner_requested(self.token.physical_owner, self.len());
        Ok(())
    }

    pub(super) fn try_clone_with(
        &self,
        mut copy: impl FnMut(&T) -> Result<T, ()>,
    ) -> Result<Self, ()> {
        let mut cloned = Self::new(self.token.meter);
        cloned.try_reserve(self.len())?;
        for item in self.iter() {
            cloned.push_reserved(copy(item)?);
        }
        Ok(cloned)
    }
}

/// Capacity charge for a raw buffer whose owner controls the drop order.
pub(super) struct TrackedAllocation<'meter>(AllocationToken<'meter>);

impl TrackedAllocation<'_> {
    pub(super) fn classify(&mut self, kind: PhysicalOwnerKind) {
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let _ = kind;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        {
            let handle = self.0.physical_owner;
            let mut owners = self.0.meter.0.physical_owners.borrow_mut();
            let owner = owners[handle.slot].as_mut().expect("live physical owner");
            assert_eq!(owner.id, handle.id);
            owner.kind = kind;
            event_sink::record(self.0.meter.0.event_component.get(), handle.id,
                event_sink::SHAPE, kind, owner.requested, owner.capacity, owner.slot_size, 0);
        }
    }

    pub(super) fn classify_shape(
        &mut self, kind: PhysicalOwnerKind, requested: usize, capacity: usize, slot_size: usize,
    ) {
        debug_assert_eq!(self.0.bytes, capacity.saturating_mul(slot_size));
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let _ = (kind, requested, capacity, slot_size);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        {
            let handle = self.0.physical_owner;
            let mut owners = self.0.meter.0.physical_owners.borrow_mut();
            let owner = owners[handle.slot].as_mut().expect("live physical owner");
            assert_eq!(owner.id, handle.id);
            let old_capacity = owner.capacity;
            owner.kind = kind;
            owner.requested = requested;
            owner.peak_requested = owner.peak_requested.max(requested);
            owner.capacity = capacity;
            owner.slot_size = slot_size;
            self.0.meter.0.family6_source_capacity.set(
                self.0.meter.0.family6_source_capacity.get()
                    .and_then(|current| current.checked_sub(old_capacity)?
                        .checked_add(capacity)));
            event_sink::record(self.0.meter.0.event_component.get(), handle.id,
                event_sink::TRANSFER, kind, requested, capacity, slot_size, kind.code());
        }
    }
}

impl<T> Deref for TrackedVec<'_, T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.values.as_ref().unwrap()
    }
}

impl<T: fmt::Debug> fmt::Debug for TrackedVec<'_, T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.values.as_ref().unwrap().fmt(formatter)
    }
}

impl<T: PartialEq> PartialEq for TrackedVec<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.values.as_ref().unwrap() == other.values.as_ref().unwrap()
    }
}

impl<T: Eq> Eq for TrackedVec<'_, T> {}

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
        #[cfg(test)]
        let physical_owner = std::mem::replace(&mut self.token.physical_owner,
            dead_physical_handle());
        #[cfg(test)]
        self.token.meter.physical_owner_transfer(physical_owner);
        TrackedIntoIter {
            iter: Some(values.into_iter()),
            token: AllocationToken {
                meter: self.token.meter,
                bytes,
                #[cfg(test)]
                physical_owner,
            },
        }
    }
}

/// One item with the same fallible allocation and accounting path as a vector.
pub(super) struct TrackedOne<'meter, T>(TrackedVec<'meter, T>);

#[cfg(test)]
thread_local! {
    static FAIL_TRACKED_ONE_AFTER: Cell<Option<usize>> = const { Cell::new(None) };
}

impl<'meter, T> TrackedOne<'meter, T> {
    #[cfg(test)]
    pub(super) fn capacity(&self) -> usize {
        self.0.capacity()
    }

    pub(super) fn try_new(meter: &'meter DraftHeapMeter, value: T) -> Result<Self, ()> {
        Self::try_new_with_kind(meter, value, PhysicalOwnerKind::Unclassified)
    }

    pub(super) fn try_new_with_kind(
        meter: &'meter DraftHeapMeter, value: T, kind: PhysicalOwnerKind,
    ) -> Result<Self, ()> {
        #[cfg(test)]
        if FAIL_TRACKED_ONE_AFTER.with(|remaining| match remaining.get() {
            Some(0) => {
                remaining.set(None);
                true
            }
            Some(n) => {
                remaining.set(Some(n - 1));
                false
            }
            None => false,
        }) {
            return Err(());
        }
        let mut values = TrackedVec::new_with_kind(meter, kind);
        values.try_reserve_exact(1)?;
        values.push_reserved(value);
        Ok(Self(values))
    }

    pub(super) fn accounted_bytes(&self) -> usize {
        self.0.accounted_bytes()
    }

    pub(super) fn into_inner(self) -> T {
        self.0.into_iter().next().unwrap()
    }

    pub(super) fn as_ref(&self) -> &T {
        &self.0[0]
    }
}

impl<T> Deref for TrackedOne<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<T: fmt::Debug> fmt::Debug for TrackedOne<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl<T: PartialEq> PartialEq for TrackedOne<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T: Eq> Eq for TrackedOne<'_, T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{F5cNegative, F5cNegativeEffect, F5cPositive, F5cPositiveEffect};
    use std::cell::Cell;

    #[test]
    fn physical_owner_registry_reuses_slots_after_drop() {
        let meter = DraftHeapMeter::default();
        let retained = TrackedVec::<u64>::new(&meter);
        for _ in 0..128 {
            let mut transient = TrackedVec::<u64>::new(&meter);
            transient.try_push(1).unwrap();
            assert_eq!(
                meter.physical_owner_bytes(),
                Some(transient.accounted_bytes())
            );
            assert_eq!(meter.0.physical_owners.borrow().len(), 3);
            drop(transient);
            assert_eq!(meter.physical_owner_bytes(), Some(0));
            assert_eq!(meter.0.physical_owners.borrow().len(), 3);
        }
        drop(retained);
        assert_eq!(meter.0.free_physical_owners.borrow().len(), 2);
    }

    #[test]
    fn function_child_owners_charge_nested_payloads_and_retry_after_second_failure() {
        let meter = DraftHeapMeter::default();
        let build_positive = || -> Result<F5cPositive<'_>, ()> {
            let mut members = TrackedVec::new(&meter);
            members.try_push(F5cNegative::Int)?;
            let argument = TrackedOne::try_new(&meter, F5cNegative::Intersection(members))?;
            let mut members = TrackedVec::new(&meter);
            members.try_push(F5cPositive::Int)?;
            let result = TrackedOne::try_new(&meter, F5cPositive::Union(members))?;
            Ok(F5cPositive::Function {
                argument,
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result,
            })
        };
        FAIL_TRACKED_ONE_AFTER.with(|remaining| remaining.set(Some(1)));
        assert_eq!(build_positive(), Err(()));
        assert_eq!(meter.current_bytes(), Some(0));
        assert_eq!(meter.physical_owner_bytes(), Some(0));
        let positive = build_positive().unwrap();
        let F5cPositive::Function {
            argument, result, ..
        } = &positive
        else {
            unreachable!()
        };
        let F5cNegative::Intersection(negative_members) = argument.as_ref() else {
            unreachable!()
        };
        let F5cPositive::Union(positive_members) = result.as_ref() else {
            unreachable!()
        };
        let expected = argument.accounted_bytes()
            + result.accounted_bytes()
            + negative_members.accounted_bytes()
            + positive_members.accounted_bytes();
        assert_eq!(meter.current_bytes(), Some(expected));
        assert_eq!(meter.physical_owner_bytes(), Some(expected));
        drop(positive);
        assert_eq!(meter.current_bytes(), Some(0));
        assert_eq!(meter.physical_owner_bytes(), Some(0));

        let build_negative = || -> Result<F5cNegative<'_>, ()> {
            let mut members = TrackedVec::new(&meter);
            members.try_push(F5cPositive::Int)?;
            let argument = TrackedOne::try_new(&meter, F5cPositive::Union(members))?;
            let mut members = TrackedVec::new(&meter);
            members.try_push(F5cNegative::Int)?;
            let result = TrackedOne::try_new(&meter, F5cNegative::Intersection(members))?;
            Ok(F5cNegative::Function {
                argument,
                argument_effect: F5cPositiveEffect::Bottom,
                result_effect: F5cNegativeEffect::Empty,
                result,
            })
        };
        FAIL_TRACKED_ONE_AFTER.with(|remaining| remaining.set(Some(1)));
        assert_eq!(build_negative(), Err(()));
        assert_eq!(meter.current_bytes(), Some(0));
        assert_eq!(meter.physical_owner_bytes(), Some(0));
        let negative = build_negative().unwrap();
        let F5cNegative::Function {
            argument, result, ..
        } = &negative
        else {
            unreachable!()
        };
        let F5cPositive::Union(positive_members) = argument.as_ref() else {
            unreachable!()
        };
        let F5cNegative::Intersection(negative_members) = result.as_ref() else {
            unreachable!()
        };
        let expected = argument.accounted_bytes()
            + result.accounted_bytes()
            + positive_members.accounted_bytes()
            + negative_members.accounted_bytes();
        assert_eq!(meter.current_bytes(), Some(expected));
        assert_eq!(meter.physical_owner_bytes(), Some(expected));
        drop(negative);
        assert_eq!(meter.current_bytes(), Some(0));
        assert_eq!(meter.physical_owner_bytes(), Some(0));
    }

    #[test]
    fn tracked_one_releases_each_capacity_after_its_child_drops() {
        struct Probe<'a> {
            meter: &'a DraftHeapMeter,
            expected: &'a Cell<usize>,
            drops: &'a Cell<usize>,
        }
        impl Drop for Probe<'_> {
            fn drop(&mut self) {
                assert_eq!(self.meter.current_bytes(), Some(self.expected.get()));
                self.drops.set(self.drops.get() + 1);
            }
        }
        let meter = DraftHeapMeter::default();
        let expected = Cell::new(0);
        let drops = Cell::new(0);
        let first = TrackedOne::try_new(
            &meter,
            Probe {
                meter: &meter,
                expected: &expected,
                drops: &drops,
            },
        )
        .unwrap();
        let second = TrackedOne::try_new(
            &meter,
            Probe {
                meter: &meter,
                expected: &expected,
                drops: &drops,
            },
        )
        .unwrap();
        let first_bytes = first.accounted_bytes();
        let second_bytes = second.accounted_bytes();
        expected.set(first_bytes + second_bytes);
        drop(first);
        expected.set(second_bytes);
        drop(second);
        assert_eq!(drops.get(), 2);
        assert_eq!(meter.current_bytes(), Some(0));
    }

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
    fn value_traits_compare_and_format_contents_only() {
        let first_meter = DraftHeapMeter::default();
        let second_meter = DraftHeapMeter::default();
        let mut first = TrackedVec::new(&first_meter);
        first.try_push(3_u64).unwrap();
        first.try_push(5).unwrap();
        let mut second = TrackedVec::new(&second_meter);
        second.try_push(3_u64).unwrap();
        second.try_push(5).unwrap();
        first.try_reserve_exact(second.capacity()).unwrap();

        assert_ne!(first.capacity(), second.capacity());
        assert_ne!(first_meter.current_bytes(), second_meter.current_bytes());
        assert_eq!(first, second);
        assert_eq!(format!("{first:?}"), "[3, 5]");
        assert_eq!(format!("{first:?}"), format!("{second:?}"));
        second.push_reserved(8);
        assert_ne!(first, second);
    }

    #[test]
    fn raw_adoption_preserves_buffer_and_releases_after_elements() {
        struct Witness<'a>(&'a DraftHeapMeter);
        impl Drop for Witness<'_> {
            fn drop(&mut self) {
                assert!(self.0.current_bytes().unwrap() > 0);
            }
        }

        let meter = DraftHeapMeter::default();
        for count in [0, 1, 3] {
            let mut raw = Vec::new();
            raw.try_reserve_exact(count.max(1)).unwrap();
            for _ in 0..count {
                raw.push(Witness(&meter));
            }
            let pointer = raw.as_ptr();
            let capacity = raw.capacity();
            let adopted = TrackedVec::try_adopt_raw(&meter, raw).unwrap_or_else(|_| panic!());
            assert_eq!(adopted.as_ptr(), pointer);
            assert_eq!(adopted.capacity(), capacity);
            assert_eq!(meter.current_bytes(), Some(capacity * size_of::<Witness>()));
            assert_eq!(
                meter.physical_owner_bytes(),
                Some(capacity * size_of::<Witness>())
            );
            drop(adopted);
            assert_eq!(meter.current_bytes(), Some(0));
            assert_eq!(meter.physical_owner_bytes(), Some(0));
        }
    }

    #[test]
    fn walker_transfer_samples_each_parts_buffer_once() {
        fn check<T>(value: T) {
            let meter = DraftHeapMeter::default();
            let mut raw = Vec::new();
            raw.push(value);
            let raw_bytes = raw.capacity() * size_of::<T>();
            meter.begin_component().unwrap();
            meter
                .observe_component_external_pair(raw_bytes + 23, raw_bytes + 23)
                .unwrap();
            let owner = TrackedVec::try_adopt_raw_from_walker(&meter, raw)
                .unwrap_or_else(|_| panic!("walker transfer failed"));
            assert_eq!(meter.physical_current_bytes(), Some(raw_bytes));
            assert_eq!(meter.physical_owner_bytes(), Some(raw_bytes));
            assert_eq!(meter.component_joint_peak(), Some(raw_bytes + 23));
            assert_eq!(meter.physical_component_joint_peak(), Some(raw_bytes + 23));
            meter.observe_component_external_pair(23, 23).unwrap();
            assert_eq!(meter.component_joint_peak(), Some(raw_bytes + 23));
            assert_eq!(meter.physical_component_joint_peak(), Some(raw_bytes + 23));
            drop(owner);
            assert_eq!(meter.current_bytes(), Some(0));
            assert_eq!(meter.end_component(), Some(raw_bytes + 23));
        }
        check(F5cPositive::Int);
        check(F5cNegative::Int);
    }

    #[test]
    fn failed_raw_adoption_returns_same_buffer() {
        struct ScratchWitness<'a>(&'a Cell<bool>);
        impl Drop for ScratchWitness<'_> {
            fn drop(&mut self) {
                assert!(self.0.get(), "scratch charge must outlive the raw buffer");
            }
        }

        let meter = DraftHeapMeter::default();
        meter.0.current.set(Some(usize::MAX));
        let scratch_live = Cell::new(true);
        let mut raw = Vec::new();
        raw.try_reserve_exact(2).unwrap();
        raw.extend([ScratchWitness(&scratch_live), ScratchWitness(&scratch_live)]);
        let pointer = raw.as_ptr();
        let capacity = raw.capacity();
        let (returned, ()) = match TrackedVec::try_adopt_raw(&meter, raw) {
            Ok(_) => panic!(),
            Err(failure) => failure,
        };
        assert_eq!(returned.as_ptr(), pointer);
        assert_eq!(returned.capacity(), capacity);
        assert_eq!(returned.len(), 2);
        assert_eq!(meter.current_bytes(), None);
        drop(returned);
        scratch_live.set(false);
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
        assert_eq!(meter.physical_owner_bytes(), Some(lane.capacity() * 8));
    }

    #[test]
    fn failed_source_growth_observes_joint_peak_and_allows_retry() {
        let meter = DraftHeapMeter::default();
        let mut lane = TrackedVec::<u64>::new(&meter);
        meter.begin_normalization().unwrap();
        meter.observe_normalization_scratch(128).unwrap();
        assert_eq!(
            lane.reserve_with(4, |values, n| {
                values.try_reserve(n).unwrap();
                Err(())
            }),
            Err(())
        );
        let first_bytes = lane.capacity() * size_of::<u64>();
        assert_eq!(meter.current_bytes(), Some(first_bytes));
        assert_eq!(meter.physical_owner_bytes(), Some(first_bytes));
        lane.try_push(1).unwrap();
        assert_eq!(lane.len(), 1);
        assert_eq!(meter.end_normalization(), Some(first_bytes + 128));
        drop(lane);
        assert_eq!(meter.current_bytes(), Some(0));
        assert_eq!(meter.physical_owner_bytes(), Some(0));
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
        assert_eq!(meter.physical_owner_bytes(), Some(bytes));
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
        assert_eq!(meter.physical_owner_bytes(), Some(bytes));
        drop(iter);
        assert_eq!(meter.current_bytes(), Some(0));
        assert_eq!(meter.physical_owner_bytes(), Some(0));
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

    #[cfg(feature = "f5c_resource_probe")]
    #[test]
    fn raw_walker_owner_keeps_identity_across_adoption_and_failure() {
        let path = std::env::temp_dir().join(format!(
            "f5c-raw-owner-{}-{:?}.bin", std::process::id(), std::thread::current().id()));
        super::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        let mut raw = Vec::<u64>::with_capacity(4);
        raw.push(7);
        let mut owner = super::RawWalkerOwner::new(&meter, 7, std::mem::size_of::<u64>());
        owner.observe(raw.len(), raw.capacity());
        let adopted = TrackedVec::try_adopt_raw_from_walker_with_owner(
            &meter, raw, PhysicalOwnerKind::UnionChildren, owner).ok().unwrap();
        drop(adopted);
        let mut raw = Vec::<u64>::with_capacity(2);
        raw.push(8);
        let mut owner = super::RawWalkerOwner::new(&meter, 7, std::mem::size_of::<u64>());
        owner.observe(raw.len(), raw.capacity());
        meter.0.current.set(None);
        let (raw, owner) = TrackedVec::try_adopt_raw_from_walker_with_owner(
            &meter, raw, PhysicalOwnerKind::UnionChildren, owner).err().unwrap();
        drop(raw);
        drop(owner);
        let (count, _) = super::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        assert_eq!(count, 7);
        let words: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).collect();
        assert_eq!(words.iter().map(|event| event[2]).collect::<Vec<_>>(),
            [1, 3, 4, 5, 1, 3, 5]);
        assert_eq!(words[0][1], words[3][1]);
        assert!(words[4][1] > words[0][1]);
    }

    #[cfg(feature = "f5c_resource_probe")]
    #[test]
    fn failed_raw_walker_adoption_drops_buffer_before_release() {
        struct DropProbe<'a>(&'a Cell<bool>);
        impl Drop for DropProbe<'_> {
            fn drop(&mut self) { self.0.set(true); }
        }
        for kind in [PhysicalOwnerKind::UnionChildren,
            PhysicalOwnerKind::IntersectionChildren] {
            let path = std::env::temp_dir().join(format!(
                "f5c-failed-transfer-{:?}-{}-{:?}.bin", kind,
                std::process::id(), std::thread::current().id()));
            super::open_f5c_resource_events(&path).unwrap();
            let meter = DraftHeapMeter::default();
            let dropped = Cell::new(false);
            let mut raw = Vec::with_capacity(2);
            raw.push(DropProbe(&dropped));
            let mut owner = super::RawWalkerOwner::new(&meter, 7,
                std::mem::size_of::<DropProbe<'_>>());
            owner.observe(raw.len(), raw.capacity());
            meter.0.current.set(None);
            let (raw, owner) = TrackedVec::try_adopt_raw_from_walker_with_owner(
                &meter, raw, kind, owner).err().unwrap();
            assert!(!dropped.get());
            drop(raw);
            assert!(dropped.get());
            drop(owner);
            super::close_f5c_resource_events().unwrap();
            let bytes = std::fs::read(&path).unwrap();
            std::fs::remove_file(path).unwrap();
            let events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
                std::array::from_fn(|index| u64::from_le_bytes(
                    event[index * 8..(index + 1) * 8].try_into().unwrap()))
            }).collect();
            assert_eq!(events.iter().map(|event| event[2]).collect::<Vec<_>>(),
                [1, 3, 5]);
            assert!(events.iter().all(|event| event[1] == events[0][1]));
        }
    }

    #[cfg(feature = "f5c_resource_probe")]
    #[test]
    fn raw_walker_transfer_has_one_same_time_buffer() {
        for kind in [PhysicalOwnerKind::UnionChildren,
            PhysicalOwnerKind::IntersectionChildren] {
            let path = std::env::temp_dir().join(format!(
                "f5c-transfer-{:?}-{}-{:?}.bin", kind, std::process::id(),
                std::thread::current().id()));
            super::open_f5c_resource_events(&path).unwrap();
            let meter = DraftHeapMeter::default();
            let mut raw = Vec::<u64>::with_capacity(4);
            raw.push(7);
            let mut owner = super::RawWalkerOwner::new(&meter, 7, 8);
            owner.observe(raw.len(), raw.capacity());
            let bytes = raw.capacity() * 8;
            meter.observe_family6_walker(bytes, raw.capacity());
            let adopted = TrackedVec::try_adopt_raw_from_walker_with_owner(
                &meter, raw, kind, owner).ok().unwrap();
            meter.observe_family6_walker(0, 0);
            assert_eq!(meter.family6_event_peak(), Some(bytes));
            drop(adopted);
            let (_, _) = super::close_f5c_resource_events().unwrap();
            let events = std::fs::read(&path).unwrap();
            std::fs::remove_file(path).unwrap();
            let words: Vec<[u64; 8]> = events[8..].chunks_exact(64).map(|event| {
                std::array::from_fn(|index| u64::from_le_bytes(
                    event[index * 8..(index + 1) * 8].try_into().unwrap()))
            }).collect();
            assert_eq!(words.iter().map(|event| event[1]).collect::<std::collections::HashSet<_>>().len(), 1);
            assert_eq!(words.iter().filter(|event| event[2] == 4).count(), 1);
            assert_eq!(words.iter().filter(|event| event[2] == 5).count(), 1);
        }
    }

    #[cfg(feature = "f5c_resource_probe")]
    #[test]
    fn raw_walker_owner_shapes_use_actual_lengths_after_failed_reserve() {
        let path = std::env::temp_dir().join(format!(
            "f5c-raw-shape-{}-{:?}.bin", std::process::id(), std::thread::current().id()));
        super::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        let mut raw = Vec::<u64>::with_capacity(2);
        let mut owner = super::RawWalkerOwner::new(&meter, 7, std::mem::size_of::<u64>());
        owner.observe(raw.len(), raw.capacity());
        raw.push(7);
        owner.observe(raw.len(), raw.capacity());
        assert!(raw.try_reserve(usize::MAX).is_err());
        owner.observe(raw.len(), raw.capacity());
        raw.pop();
        owner.observe(raw.len(), raw.capacity());
        drop(raw);
        drop(owner);
        let (count, _) = super::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        let words: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).collect();
        assert_eq!(count, 5);
        assert_eq!(words.iter().map(|event| (event[2], event[4])).collect::<Vec<_>>(),
            [(1, 0), (3, 0), (2, 1), (2, 0), (5, 0)]);
        assert!(words.iter().all(|event| event[1] == words[0][1]));
    }
}
