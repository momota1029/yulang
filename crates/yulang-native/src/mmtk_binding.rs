//! MMTk VM binding for the native GC runtime prototype.
//!
//! This module is compiled only with the `mmtk-runtime` feature.  It gives
//! MMTk a concrete VM binding surface before the runtime switches allocation
//! over to MMTk.  The first supported shape is a contiguous object:
//!
//! ```text
//! YulangMmtkObjectHeader
//! traced YValue slots...
//! raw payload bytes...
//! ```
//!
//! The existing `gc_runtime` module still owns the semantic object model.  This
//! file owns the MMTk callbacks that will later allocate and scan that object
//! model through MMTk.

use std::hash::{Hash, Hasher};
use std::ops::Range;
use std::sync::atomic::{AtomicUsize, Ordering};

use mmtk::ObjectQueue;
use mmtk::plan::Mutator;
use mmtk::scheduler::GCWorker;
use mmtk::util::alloc::AllocationError;
use mmtk::util::copy::{CopySemantics, GCWorkerCopyContext};
use mmtk::util::heap::GCTriggerPolicy;
use mmtk::util::opaque_pointer::{VMMutatorThread, VMThread};
use mmtk::util::{Address, ObjectReference, VMWorkerThread};
use mmtk::vm::slot::Slot;
use mmtk::vm::{
    ActivePlan, Collection, GCThreadContext, ObjectModel, ReferenceGlue, RootsWorkFactory,
    Scanning, SlotVisitor, VMBinding, VMGlobalLogBitSpec, VMLocalForwardingBitsSpec,
    VMLocalForwardingPointerSpec, VMLocalLOSMarkNurserySpec, VMLocalMarkBitSpec,
};

use crate::gc_runtime::{YObjectKind, YValue};

const WORD_BITS: isize = usize::BITS as isize;
const YULANG_TYPE_DESCRIPTOR: &[i8] = &[
    b'y' as i8, b'u' as i8, b'l' as i8, b'a' as i8, b'n' as i8, b'g' as i8, b'-' as i8, b'n' as i8,
    b'a' as i8, b't' as i8, b'i' as i8, b'v' as i8, b'e' as i8, b'-' as i8, b'o' as i8, b'b' as i8,
    b'j' as i8, b'e' as i8, b'c' as i8, b't' as i8, 0,
];

#[derive(Default)]
pub struct YulangMmtkVM;

unsafe impl Send for YulangMmtkVM {}
unsafe impl Sync for YulangMmtkVM {}

impl VMBinding for YulangMmtkVM {
    type VMObjectModel = YulangMmtkObjectModel;
    type VMScanning = YulangMmtkScanning;
    type VMCollection = YulangMmtkCollection;
    type VMActivePlan = YulangMmtkActivePlan;
    type VMReferenceGlue = YulangMmtkReferenceGlue;
    type VMSlot = YulangMmtkSlot;
    type VMMemorySlice = YulangMmtkMemorySlice;

    const MAX_ALIGNMENT: usize = 1 << 6;
    const USE_ALLOCATION_OFFSET: bool = false;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct YulangMmtkObjectHeader {
    mmtk_forwarding: usize,
    mmtk_mark_bits: usize,
    mmtk_log_bits: usize,
    kind: YObjectKind,
    total_size: usize,
    trace_slot_count: usize,
}

impl YulangMmtkObjectHeader {
    pub const fn new(kind: YObjectKind, total_size: usize, trace_slot_count: usize) -> Self {
        Self {
            mmtk_forwarding: 0,
            mmtk_mark_bits: 0,
            mmtk_log_bits: 0,
            kind,
            total_size,
            trace_slot_count,
        }
    }

    pub fn kind(self) -> YObjectKind {
        self.kind
    }

    pub fn total_size(self) -> usize {
        self.total_size
    }

    pub fn trace_slot_count(self) -> usize {
        self.trace_slot_count
    }

    pub fn header_size() -> usize {
        std::mem::size_of::<Self>()
    }

    pub fn payload_offset() -> usize {
        Self::header_size()
    }

    pub fn trace_slots_byte_size(trace_slot_count: usize) -> usize {
        trace_slot_count * std::mem::size_of::<YValue>()
    }

    pub fn total_size_for(trace_slot_count: usize, raw_payload_size: usize) -> usize {
        Self::header_size() + Self::trace_slots_byte_size(trace_slot_count) + raw_payload_size
    }

    pub fn trace_slot_address(object: ObjectReference, index: usize) -> Address {
        Self::slot_address(object, index)
    }

    pub fn raw_payload_address(object: ObjectReference) -> Address {
        let header = Self::from_object(object);
        object.to_raw_address()
            + Self::payload_offset()
            + Self::trace_slots_byte_size(header.trace_slot_count())
    }

    fn from_object(object: ObjectReference) -> Self {
        unsafe { object.to_raw_address().load::<Self>() }
    }

    fn slot_address(object: ObjectReference, index: usize) -> Address {
        object.to_raw_address() + Self::payload_offset() + index * std::mem::size_of::<YValue>()
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct YulangMmtkSlot {
    slot_addr: *mut AtomicUsize,
}

impl YulangMmtkSlot {
    pub fn from_address(address: Address) -> Self {
        Self {
            slot_addr: address.to_mut_ptr(),
        }
    }

    pub fn as_address(self) -> Address {
        Address::from_mut_ptr(self.slot_addr)
    }
}

unsafe impl Send for YulangMmtkSlot {}

impl std::fmt::Debug for YulangMmtkSlot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("YulangMmtkSlot")
            .field(&self.as_address())
            .finish()
    }
}

impl PartialEq for YulangMmtkSlot {
    fn eq(&self, other: &Self) -> bool {
        self.slot_addr == other.slot_addr
    }
}

impl Eq for YulangMmtkSlot {}

impl Hash for YulangMmtkSlot {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.slot_addr.hash(state);
    }
}

impl Slot for YulangMmtkSlot {
    fn load(&self) -> Option<ObjectReference> {
        let raw = unsafe { (*self.slot_addr).load(Ordering::Relaxed) };
        YValue::heap_reference_raw_bits(raw)
            .map(|raw| unsafe { ObjectReference::from_raw_address_unchecked(raw_address(raw)) })
    }

    fn store(&self, object: ObjectReference) {
        let raw = object.to_raw_address().as_usize();
        unsafe {
            (*self.slot_addr).store(raw, Ordering::Relaxed);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct YulangMmtkMemorySlice {
    object: ObjectReference,
    range: Range<Address>,
}

impl YulangMmtkMemorySlice {
    pub fn new(object: ObjectReference, range: Range<Address>) -> Self {
        Self { object, range }
    }
}

impl mmtk::vm::slot::MemorySlice for YulangMmtkMemorySlice {
    type SlotType = YulangMmtkSlot;
    type SlotIterator = YulangMmtkSlotIterator;

    fn iter_slots(&self) -> Self::SlotIterator {
        YulangMmtkSlotIterator {
            cursor: self.range.start,
            limit: self.range.end,
        }
    }

    fn object(&self) -> Option<ObjectReference> {
        Some(self.object)
    }

    fn start(&self) -> Address {
        self.range.start
    }

    fn bytes(&self) -> usize {
        self.range.end - self.range.start
    }

    fn copy(src: &Self, tgt: &Self) {
        debug_assert_eq!(src.bytes(), tgt.bytes());
        unsafe {
            std::ptr::copy_nonoverlapping(
                src.start().to_ptr::<u8>(),
                tgt.start().to_mut_ptr::<u8>(),
                src.bytes(),
            );
        }
    }
}

pub struct YulangMmtkSlotIterator {
    cursor: Address,
    limit: Address,
}

impl Iterator for YulangMmtkSlotIterator {
    type Item = YulangMmtkSlot;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= self.limit {
            return None;
        }
        let slot = YulangMmtkSlot::from_address(self.cursor);
        self.cursor += std::mem::size_of::<YValue>();
        Some(slot)
    }
}

pub fn initialize_yulang_mmtk_object(
    start: Address,
    kind: YObjectKind,
    trace_slots: &[YValue],
    raw_payload_size: usize,
) -> ObjectReference {
    let total_size = YulangMmtkObjectHeader::total_size_for(trace_slots.len(), raw_payload_size);
    let object = ObjectReference::from_raw_address(start).expect("MMTk object start must be valid");
    unsafe {
        start.store(YulangMmtkObjectHeader::new(
            kind,
            total_size,
            trace_slots.len(),
        ));
        for (index, value) in trace_slots.iter().copied().enumerate() {
            YulangMmtkObjectHeader::trace_slot_address(object, index).store(value.raw());
        }
        let raw_start = start
            + YulangMmtkObjectHeader::payload_offset()
            + YulangMmtkObjectHeader::trace_slots_byte_size(trace_slots.len());
        std::ptr::write_bytes(raw_start.to_mut_ptr::<u8>(), 0, raw_payload_size);
    }
    object
}

pub struct YulangMmtkObjectModel;

impl ObjectModel<YulangMmtkVM> for YulangMmtkObjectModel {
    const GLOBAL_LOG_BIT_SPEC: VMGlobalLogBitSpec = VMGlobalLogBitSpec::in_header(2 * WORD_BITS);
    const LOCAL_FORWARDING_POINTER_SPEC: VMLocalForwardingPointerSpec =
        VMLocalForwardingPointerSpec::in_header(0);
    const LOCAL_FORWARDING_BITS_SPEC: VMLocalForwardingBitsSpec =
        VMLocalForwardingBitsSpec::in_header(0);
    const LOCAL_MARK_BIT_SPEC: VMLocalMarkBitSpec = VMLocalMarkBitSpec::in_header(WORD_BITS);
    const LOCAL_LOS_MARK_NURSERY_SPEC: VMLocalLOSMarkNurserySpec =
        VMLocalLOSMarkNurserySpec::in_header(WORD_BITS + 1);
    const OBJECT_REF_OFFSET_LOWER_BOUND: isize = 0;
    const UNIFIED_OBJECT_REFERENCE_ADDRESS: bool = true;

    fn copy(
        _from: ObjectReference,
        _semantics: CopySemantics,
        _copy_context: &mut GCWorkerCopyContext<YulangMmtkVM>,
    ) -> ObjectReference {
        unreachable!("Yulang's initial MMTk spike uses NoGC and does not copy objects")
    }

    fn copy_to(_from: ObjectReference, _to: ObjectReference, _region: Address) -> Address {
        unreachable!("Yulang's initial MMTk spike uses NoGC and does not copy objects")
    }

    fn get_reference_when_copied_to(_from: ObjectReference, _to: Address) -> ObjectReference {
        unreachable!("Yulang's initial MMTk spike uses NoGC and does not copy objects")
    }

    fn get_current_size(object: ObjectReference) -> usize {
        YulangMmtkObjectHeader::from_object(object).total_size()
    }

    fn get_size_when_copied(object: ObjectReference) -> usize {
        Self::get_current_size(object)
    }

    fn get_align_when_copied(_object: ObjectReference) -> usize {
        std::mem::align_of::<YulangMmtkObjectHeader>()
    }

    fn get_align_offset_when_copied(_object: ObjectReference) -> usize {
        0
    }

    fn get_type_descriptor(_reference: ObjectReference) -> &'static [i8] {
        YULANG_TYPE_DESCRIPTOR
    }

    fn ref_to_object_start(object: ObjectReference) -> Address {
        object.to_raw_address()
    }

    fn ref_to_header(object: ObjectReference) -> Address {
        object.to_raw_address()
    }

    fn dump_object(object: ObjectReference) {
        eprintln!("Yulang MMTk object {:?}", object);
    }
}

pub struct YulangMmtkScanning;

impl Scanning<YulangMmtkVM> for YulangMmtkScanning {
    const UNIQUE_OBJECT_ENQUEUING: bool = true;

    fn scan_object<SV: SlotVisitor<YulangMmtkSlot>>(
        _tls: VMWorkerThread,
        object: ObjectReference,
        slot_visitor: &mut SV,
    ) {
        let header = YulangMmtkObjectHeader::from_object(object);
        for index in 0..header.trace_slot_count() {
            slot_visitor.visit_slot(YulangMmtkSlot::from_address(
                YulangMmtkObjectHeader::slot_address(object, index),
            ));
        }
    }

    fn scan_roots_in_mutator_thread(
        _tls: VMWorkerThread,
        _mutator: &'static mut Mutator<YulangMmtkVM>,
        _factory: impl RootsWorkFactory<YulangMmtkSlot>,
    ) {
    }

    fn scan_vm_specific_roots(
        _tls: VMWorkerThread,
        _factory: impl RootsWorkFactory<YulangMmtkSlot>,
    ) {
    }

    fn notify_initial_thread_scan_complete(_partial_scan: bool, _tls: VMWorkerThread) {}

    fn supports_return_barrier() -> bool {
        false
    }

    fn prepare_for_roots_re_scanning() {}
}

pub struct YulangMmtkCollection;

impl Collection<YulangMmtkVM> for YulangMmtkCollection {
    fn stop_all_mutators<F>(_tls: VMWorkerThread, _mutator_visitor: F)
    where
        F: FnMut(&'static mut Mutator<YulangMmtkVM>),
    {
    }

    fn resume_mutators(_tls: VMWorkerThread) {}

    fn block_for_gc(_tls: VMMutatorThread) {}

    fn spawn_gc_thread(_tls: VMThread, _ctx: GCThreadContext<YulangMmtkVM>) {
        unreachable!("Yulang MMTk collection initialization is not wired yet")
    }

    fn out_of_memory(_tls: VMThread, err_kind: AllocationError) {
        panic!("Yulang MMTk heap exhausted: {:?}", err_kind);
    }

    fn is_collection_enabled() -> bool {
        true
    }

    fn create_gc_trigger() -> Box<dyn GCTriggerPolicy<YulangMmtkVM>> {
        unimplemented!("delegated GC trigger is not part of the initial Yulang MMTk spike")
    }
}

pub struct YulangMmtkActivePlan;

impl ActivePlan<YulangMmtkVM> for YulangMmtkActivePlan {
    fn is_mutator(_tls: VMThread) -> bool {
        false
    }

    fn mutator(_tls: VMMutatorThread) -> &'static mut Mutator<YulangMmtkVM> {
        unreachable!("Yulang MMTk mutator registry is not wired yet")
    }

    fn mutators<'a>() -> Box<dyn Iterator<Item = &'a mut Mutator<YulangMmtkVM>> + 'a> {
        Box::new(std::iter::empty())
    }

    fn number_of_mutators() -> usize {
        0
    }

    fn vm_trace_object<Q: ObjectQueue>(
        _queue: &mut Q,
        object: ObjectReference,
        _worker: &mut GCWorker<YulangMmtkVM>,
    ) -> ObjectReference {
        object
    }
}

pub struct YulangMmtkReferenceGlue;

impl ReferenceGlue<YulangMmtkVM> for YulangMmtkReferenceGlue {
    type FinalizableType = ObjectReference;

    fn clear_referent(_new_reference: ObjectReference) {}

    fn get_referent(_object: ObjectReference) -> Option<ObjectReference> {
        None
    }

    fn set_referent(_reff: ObjectReference, _referent: ObjectReference) {}

    fn enqueue_references(_references: &[ObjectReference], _tls: VMWorkerThread) {}
}

fn raw_address(raw: usize) -> Address {
    unsafe { Address::from_usize(raw) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mmtk::vm::slot::MemorySlice;

    #[test]
    fn slot_ignores_immediate_yvalues_and_loads_heap_references() {
        let header = YulangMmtkObjectHeader::new(YObjectKind::Tuple, 16, 0);
        let object = ObjectReference::from_raw_address(Address::from_ref(&header)).unwrap();
        let mut slot_word = YValue::UNIT.raw();
        let slot = YulangMmtkSlot::from_address(Address::from_mut_ptr(&mut slot_word));

        assert_eq!(slot.load(), None);

        slot.store(object);

        assert_eq!(slot.load(), Some(object));
        assert_eq!(slot_word, object.to_raw_address().as_usize());
    }

    #[test]
    fn object_scanning_reports_only_declared_trace_slots() {
        #[repr(C)]
        struct TestObject {
            header: YulangMmtkObjectHeader,
            slots: [usize; 2],
            raw: usize,
        }

        let child_header = YulangMmtkObjectHeader::new(
            YObjectKind::String,
            YulangMmtkObjectHeader::header_size(),
            0,
        );
        let child = ObjectReference::from_raw_address(Address::from_ref(&child_header)).unwrap();
        let mut object = TestObject {
            header: YulangMmtkObjectHeader::new(
                YObjectKind::Tuple,
                YulangMmtkObjectHeader::total_size_for(2, 8),
                2,
            ),
            slots: [
                child.to_raw_address().as_usize(),
                YValue::from_i63(42).unwrap().raw(),
            ],
            raw: 0xabad_1dea,
        };
        let object_ref = ObjectReference::from_raw_address(Address::from_mut_ptr(&mut object))
            .expect("test object is word-aligned");
        let mut visited = Vec::new();

        YulangMmtkScanning::scan_object(
            VMWorkerThread(VMThread::UNINITIALIZED),
            object_ref,
            &mut |slot| {
                visited.push(slot);
            },
        );

        assert_eq!(visited.len(), 2);
        assert_eq!(visited[0].load(), Some(child));
        assert_eq!(visited[1].load(), None);
    }

    #[test]
    fn memory_slice_iterates_yvalue_sized_slots() {
        let object_header = YulangMmtkObjectHeader::new(YObjectKind::Tuple, 16, 0);
        let object = ObjectReference::from_raw_address(Address::from_ref(&object_header)).unwrap();
        let mut words = [0usize; 3];
        let start = Address::from_mut_ptr(&mut words[0]);
        let slice =
            YulangMmtkMemorySlice::new(object, start..start + std::mem::size_of_val(&words));

        let slots = slice.iter_slots().collect::<Vec<_>>();

        assert_eq!(slots.len(), 3);
        assert_eq!(slots[0].as_address(), start);
        assert_eq!(
            slots[2].as_address(),
            start + 2 * std::mem::size_of::<YValue>()
        );
    }
}
