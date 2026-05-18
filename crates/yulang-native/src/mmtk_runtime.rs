//! MMTk runtime integration boundary.
//!
//! This module is intentionally thin. The GC runtime object model is still in
//! `gc_runtime`; this file records the MMTk plan/options surface that will back
//! that heap once the VM binding and object model callbacks are implemented.

#[cfg(feature = "mmtk-runtime")]
use std::cell::RefCell;
#[cfg(feature = "mmtk-runtime")]
use std::collections::{BTreeMap, HashMap};

#[cfg(feature = "mmtk-runtime")]
use mmtk::plan::AllocationSemantics;
#[cfg(feature = "mmtk-runtime")]
use mmtk::util::ObjectReference;
#[cfg(feature = "mmtk-runtime")]
use mmtk::util::opaque_pointer::{VMMutatorThread, VMThread};

#[cfg(feature = "mmtk-runtime")]
use crate::gc_runtime::{
    GcRuntimeContext, NativeFieldLane, NativeFieldLayout, NativeFieldValue, NativeHeapBlock,
    NativeLayout, NativeLayoutHandle, NativeLayoutKind, NativePayloadBuffer, YHeap, YHeapStats,
    YList, YObject, YObjectKind, YObjectPayload, YString, YValue,
};
#[cfg(feature = "mmtk-runtime")]
use crate::mmtk_binding::{YulangMmtkObjectHeader, YulangMmtkVM, initialize_yulang_mmtk_object};

#[cfg(feature = "mmtk-runtime")]
const MAX_STRING_LEAF_CHARS: usize = yulang_runtime::runtime::string_tree::MAX_LEAF_CHARS;

#[cfg(feature = "mmtk-runtime")]
const MAX_LIST_LEAF_ITEMS: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MmtkRuntimeConfig {
    pub plan: MmtkRuntimePlan,
    pub heap_min: Option<String>,
    pub heap_max: Option<String>,
    pub threads: Option<usize>,
}

impl Default for MmtkRuntimeConfig {
    fn default() -> Self {
        Self {
            plan: MmtkRuntimePlan::NoGc,
            heap_min: None,
            heap_max: None,
            threads: Some(1),
        }
    }
}

impl MmtkRuntimeConfig {
    pub fn prototype_no_gc() -> Self {
        Self::default()
    }

    pub fn option_pairs(&self) -> Vec<(&'static str, String)> {
        let mut options = vec![("plan", self.plan.option_value().to_string())];
        if let Some(heap_min) = &self.heap_min {
            options.push(("min_heap", heap_min.clone()));
        }
        if let Some(heap_max) = &self.heap_max {
            options.push(("max_heap", heap_max.clone()));
        }
        if let Some(threads) = self.threads {
            options.push(("threads", threads.to_string()));
        }
        options
    }

    pub fn options_string(&self) -> String {
        self.option_pairs()
            .into_iter()
            .map(|(name, value)| format!("{name}={value}"))
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[cfg(feature = "mmtk-runtime")]
    pub fn configure_builder(
        &self,
        builder: &mut mmtk::MMTKBuilder,
    ) -> Result<(), MmtkConfigError> {
        for (name, value) in self.option_pairs() {
            if !builder.set_option(name, &value) {
                return Err(MmtkConfigError::RejectedOption {
                    name,
                    value: value.into_boxed_str(),
                });
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MmtkRuntimePlan {
    NoGc,
    Immix,
    MarkSweep,
    SemiSpace,
    GenImmix,
}

impl MmtkRuntimePlan {
    pub fn option_value(self) -> &'static str {
        match self {
            Self::NoGc => "NoGC",
            Self::Immix => "Immix",
            Self::MarkSweep => "MarkSweep",
            Self::SemiSpace => "SemiSpace",
            Self::GenImmix => "GenImmix",
        }
    }

    #[cfg(feature = "mmtk-runtime")]
    pub fn selector(self) -> mmtk::util::options::PlanSelector {
        match self {
            Self::NoGc => mmtk::util::options::PlanSelector::NoGC,
            Self::Immix => mmtk::util::options::PlanSelector::Immix,
            Self::MarkSweep => mmtk::util::options::PlanSelector::MarkSweep,
            Self::SemiSpace => mmtk::util::options::PlanSelector::SemiSpace,
            Self::GenImmix => mmtk::util::options::PlanSelector::GenImmix,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MmtkConfigError {
    RejectedOption { name: &'static str, value: Box<str> },
}

#[derive(Debug, Default)]
pub struct MmtkRuntimeBoundary {
    config: MmtkRuntimeConfig,
}

impl MmtkRuntimeBoundary {
    pub fn new(config: MmtkRuntimeConfig) -> Self {
        Self { config }
    }

    pub fn config(&self) -> &MmtkRuntimeConfig {
        &self.config
    }

    pub fn options_string(&self) -> String {
        self.config.options_string()
    }

    #[cfg(feature = "mmtk-runtime")]
    pub fn builder(&self) -> Result<mmtk::MMTKBuilder, MmtkConfigError> {
        let mut builder = mmtk::MMTKBuilder::new_no_env_vars();
        self.config.configure_builder(&mut builder)?;
        Ok(builder)
    }

    #[cfg(feature = "mmtk-runtime")]
    pub fn build_yulang_mmtk(
        &self,
    ) -> Result<mmtk::MMTK<crate::mmtk_binding::YulangMmtkVM>, MmtkConfigError> {
        Ok(self.builder()?.build::<crate::mmtk_binding::YulangMmtkVM>())
    }
}

#[cfg(feature = "mmtk-runtime")]
pub struct MmtkHeap {
    _mmtk: &'static mmtk::MMTK<YulangMmtkVM>,
    mutator: Box<mmtk::Mutator<YulangMmtkVM>>,
    objects: BTreeMap<usize, MmtkPayloadStorage>,
}

#[cfg(feature = "mmtk-runtime")]
impl MmtkHeap {
    pub fn new_no_gc() -> Result<Self, MmtkConfigError> {
        Self::new(MmtkRuntimeConfig::prototype_no_gc())
    }

    pub fn new(config: MmtkRuntimeConfig) -> Result<Self, MmtkConfigError> {
        let boundary = MmtkRuntimeBoundary::new(config);
        let mmtk = Box::leak(Box::new(boundary.build_yulang_mmtk()?));
        let tls = VMMutatorThread(VMThread::UNINITIALIZED);
        let mutator = mmtk::memory_manager::bind_mutator(mmtk, tls);
        Ok(Self {
            _mmtk: mmtk,
            mutator,
            objects: BTreeMap::new(),
        })
    }

    pub fn object_reference(&self, value: YValue) -> Option<ObjectReference> {
        value.heap_reference_raw().and_then(|raw| {
            self.objects
                .contains_key(&raw)
                .then(|| ObjectReference::from_raw_address(raw_address(raw)))
                .flatten()
        })
    }

    pub fn object_count(&self) -> usize {
        self.objects.len()
    }

    pub fn allocate_raw_payload(
        &mut self,
        kind: YObjectKind,
        trace_slots: &[YValue],
        raw_payload: &[u8],
    ) -> YValue {
        self.allocate_raw_payload_with_storage(
            kind,
            trace_slots,
            raw_payload,
            MmtkPayloadStorage::RawBytes,
        )
    }

    fn allocate_string_leaf(&mut self, bytes: &[u8]) -> Option<YValue> {
        let text = std::str::from_utf8(bytes).ok()?;
        Some(self.allocate_raw_payload_with_storage(
            YObjectKind::String,
            &[],
            bytes,
            MmtkPayloadStorage::StringLeaf {
                len_chars: text.chars().count(),
                len_bytes: bytes.len(),
            },
        ))
    }

    fn allocate_string_node(
        &mut self,
        color: TreeColor,
        left: YValue,
        right: YValue,
        len_chars: usize,
        len_bytes: usize,
    ) -> YValue {
        self.allocate_raw_payload_with_storage(
            YObjectKind::String,
            &[left, right],
            &[],
            MmtkPayloadStorage::StringNode {
                color,
                len_chars,
                len_bytes,
            },
        )
    }

    fn allocate_list_leaf(&mut self, items: &[YValue]) -> YValue {
        self.allocate_raw_payload_with_storage(
            YObjectKind::List,
            items,
            &[],
            MmtkPayloadStorage::ListLeaf { len: items.len() },
        )
    }

    fn allocate_list_node(
        &mut self,
        color: TreeColor,
        left: YValue,
        right: YValue,
        len: usize,
    ) -> YValue {
        self.allocate_raw_payload_with_storage(
            YObjectKind::List,
            &[left, right],
            &[],
            MmtkPayloadStorage::ListNode { color, len },
        )
    }

    pub fn allocate_native_heap_block(&mut self, block: &NativeHeapBlock) -> YValue {
        self.allocate_raw_payload_with_storage(
            block.object_kind(),
            &block.trace_children(),
            block.payload().bytes(),
            MmtkPayloadStorage::NativeBlock {
                layout: block.layout().clone(),
            },
        )
    }

    pub fn native_field_value(&self, value: YValue, index: usize) -> Option<NativeFieldValue> {
        let raw = value.heap_reference_raw()?;
        let layout = match self.objects.get(&raw)? {
            MmtkPayloadStorage::NativeBlock { layout } => layout.clone(),
            _ => return None,
        };
        let payload = NativePayloadBuffer::from_bytes(self.raw_payload_bytes(value)?.to_vec());
        payload.read_field(layout.layout(), index)
    }

    pub fn native_field_count(&self, value: YValue) -> Option<usize> {
        let raw = value.heap_reference_raw()?;
        match self.objects.get(&raw)? {
            MmtkPayloadStorage::NativeBlock { layout } => Some(layout.layout().fields.len()),
            _ => None,
        }
    }

    pub fn native_field_name(&self, value: YValue, index: usize) -> Option<&str> {
        let raw = value.heap_reference_raw()?;
        let layout = match self.objects.get(&raw)? {
            MmtkPayloadStorage::NativeBlock { layout } => layout,
            _ => return None,
        };
        layout.layout().fields.get(index)?.name.as_deref()
    }

    pub fn allocate_compact_closure(&mut self, code: usize, env: &[YValue]) -> YValue {
        self.allocate_compact_control_block(
            YObjectKind::Closure,
            Some(("code", NativeFieldValue::U64(code as u64))),
            env,
        )
    }

    pub fn allocate_compact_thunk(&mut self, code: usize, env: &[YValue]) -> YValue {
        self.allocate_compact_control_block(
            YObjectKind::Thunk,
            Some(("code", NativeFieldValue::U64(code as u64))),
            env,
        )
    }

    pub fn allocate_compact_resumption(&mut self, code: usize, env: &[YValue]) -> YValue {
        self.allocate_compact_control_block(
            YObjectKind::Resumption,
            Some(("code", NativeFieldValue::U64(code as u64))),
            env,
        )
    }

    pub fn allocate_compact_continuation_env(&mut self, slots: &[YValue]) -> YValue {
        self.allocate_compact_control_block(YObjectKind::ContinuationEnv, None, slots)
    }

    pub fn allocate_compact_handler_frame(&mut self, prompt: u64, env: &[YValue]) -> YValue {
        self.allocate_compact_control_block(
            YObjectKind::HandlerFrame,
            Some(("prompt", NativeFieldValue::U64(prompt))),
            env,
        )
    }

    pub fn allocate_compact_return_frame(&mut self, continuation: usize, env: &[YValue]) -> YValue {
        self.allocate_compact_control_block(
            YObjectKind::ReturnFrame,
            Some(("continuation", NativeFieldValue::U64(continuation as u64))),
            env,
        )
    }

    pub fn compact_control_word(&self, value: YValue) -> Option<u64> {
        if self.compact_env_start(value)? == 0 {
            return None;
        }
        let NativeFieldValue::U64(word) = self.native_field_value(value, 0)? else {
            return None;
        };
        Some(word)
    }

    pub fn compact_env_slots(&self, value: YValue) -> Option<Vec<YValue>> {
        let start = self.compact_env_start(value)?;
        let field_count = self.native_field_count(value)?;
        let mut slots = Vec::with_capacity(field_count.saturating_sub(start));
        for index in start..field_count {
            let NativeFieldValue::YValue(slot) = self.native_field_value(value, index)? else {
                return None;
            };
            slots.push(slot);
        }
        Some(slots)
    }

    fn allocate_raw_payload_with_storage(
        &mut self,
        kind: YObjectKind,
        trace_slots: &[YValue],
        raw_payload: &[u8],
        storage: MmtkPayloadStorage,
    ) -> YValue {
        let object_ref = self.allocate_mmtk_object(kind, trace_slots, raw_payload.len());
        unsafe {
            std::ptr::copy_nonoverlapping(
                raw_payload.as_ptr(),
                YulangMmtkObjectHeader::raw_payload_address(object_ref).to_mut_ptr(),
                raw_payload.len(),
            );
        }
        let raw = object_ref.to_raw_address().as_usize();
        self.objects.insert(raw, storage);
        YValue::from_heap_reference_raw(raw).expect("MMTk object reference must fit YValue")
    }

    fn allocate_compact_control_block(
        &mut self,
        kind: YObjectKind,
        head: Option<(&'static str, NativeFieldValue)>,
        env: &[YValue],
    ) -> YValue {
        let mut layouts = Vec::with_capacity(env.len() + usize::from(head.is_some()));
        let mut fields = Vec::with_capacity(env.len() + usize::from(head.is_some()));
        if let Some((name, value)) = head {
            layouts.push(NativeFieldLayout::named(name, value.lane()));
            fields.push(value);
        }
        layouts.extend(env.iter().enumerate().map(|(index, _)| {
            NativeFieldLayout::named(format!("env{index}"), NativeFieldLane::YValue)
        }));
        fields.extend(env.iter().copied().map(NativeFieldValue::YValue));
        let layout = NativeLayout::new(NativeLayoutKind::Object(kind), layouts);
        let layout = NativeLayoutHandle::ephemeral(self.next_ephemeral_layout_id(), layout);
        let block = NativeHeapBlock::new(layout, fields)
            .expect("compact control layout should match fields");
        self.allocate_native_heap_block(&block)
    }

    fn compact_env_start(&self, value: YValue) -> Option<usize> {
        let kind = self.object_header(value)?.kind;
        match kind {
            YObjectKind::Closure
            | YObjectKind::Thunk
            | YObjectKind::Resumption
            | YObjectKind::HandlerFrame
            | YObjectKind::ReturnFrame => Some(1),
            YObjectKind::ContinuationEnv => Some(0),
            _ => None,
        }
    }

    fn next_ephemeral_layout_id(&self) -> crate::gc_runtime::NativeLayoutId {
        crate::gc_runtime::NativeLayoutId(usize::MAX - self.objects.len())
    }

    pub fn raw_payload_bytes(&self, value: YValue) -> Option<&[u8]> {
        let object = self.object_reference(value)?;
        let header = Self::mmtk_header(object);
        let raw_size = header
            .total_size()
            .checked_sub(YulangMmtkObjectHeader::header_size())?
            .checked_sub(YulangMmtkObjectHeader::trace_slots_byte_size(
                header.trace_slot_count(),
            ))?;
        Some(unsafe {
            std::slice::from_raw_parts(
                YulangMmtkObjectHeader::raw_payload_address(object).to_ptr(),
                raw_size,
            )
        })
    }
}

#[cfg(feature = "mmtk-runtime")]
impl std::fmt::Debug for MmtkHeap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MmtkHeap")
            .field("object_count", &self.objects.len())
            .finish_non_exhaustive()
    }
}

#[cfg(feature = "mmtk-runtime")]
impl Drop for MmtkHeap {
    fn drop(&mut self) {
        for (raw, storage) in &self.objects {
            if storage != &MmtkPayloadStorage::SemanticObject {
                continue;
            }
            let object = ObjectReference::from_raw_address(raw_address(*raw))
                .expect("tracked MMTk object reference should remain valid");
            unsafe {
                std::ptr::drop_in_place(Self::payload_ptr(object));
            }
        }
        mmtk::memory_manager::destroy_mutator(&mut self.mutator);
    }
}

#[cfg(feature = "mmtk-runtime")]
impl YHeap for MmtkHeap {
    fn allocate_boxed(&mut self, object: Box<YObject>) -> YValue {
        let header = object.header();
        let trace_slots = object.trace_children();
        let raw_payload_size = std::mem::size_of::<YObject>();
        let object_ref = self.allocate_mmtk_object(header.kind, &trace_slots, raw_payload_size);
        unsafe {
            std::ptr::write(Self::payload_ptr(object_ref), *object);
        }

        let raw = object_ref.to_raw_address().as_usize();
        self.objects.insert(raw, MmtkPayloadStorage::SemanticObject);
        YValue::from_heap_reference_raw(raw).expect("MMTk object reference must fit YValue")
    }

    fn object(&self, value: YValue) -> Option<&YObject> {
        let raw = value.heap_reference_raw()?;
        (self.objects.get(&raw) == Some(&MmtkPayloadStorage::SemanticObject)).then(|| {
            let object = ObjectReference::from_raw_address(raw_address(raw))
                .expect("tracked MMTk object reference should remain valid");
            unsafe { &*Self::payload_ptr(object) }
        })
    }

    fn stats(&self) -> YHeapStats {
        YHeapStats::from_headers(self.objects.keys().map(|raw| {
            let object = ObjectReference::from_raw_address(raw_address(*raw))
                .expect("tracked MMTk object reference should remain valid");
            Self::object_header_from_ref(object)
        }))
    }

    fn object_header(&self, value: YValue) -> Option<crate::gc_runtime::YObjectHeader> {
        let object = self.object_reference(value)?;
        Some(Self::object_header_from_ref(object))
    }

    fn trace_children(&self, value: YValue) -> Option<Vec<YValue>> {
        let object = self.object_reference(value)?;
        let header = Self::mmtk_header(object);
        let mut children = Vec::with_capacity(header.trace_slot_count());
        for index in 0..header.trace_slot_count() {
            let raw = unsafe {
                YulangMmtkObjectHeader::trace_slot_address(object, index).load::<usize>()
            };
            children.push(YValue::from_raw(raw));
        }
        Some(children)
    }
}

#[cfg(feature = "mmtk-runtime")]
impl MmtkHeap {
    fn allocate_mmtk_object(
        &mut self,
        kind: YObjectKind,
        trace_slots: &[YValue],
        raw_payload_size: usize,
    ) -> ObjectReference {
        let bytes = YulangMmtkObjectHeader::total_size_for(trace_slots.len(), raw_payload_size);
        let align = std::mem::align_of::<YulangMmtkObjectHeader>()
            .max(std::mem::align_of::<YObject>())
            .max(ObjectReference::ALIGNMENT);
        let start = mmtk::memory_manager::alloc(
            &mut self.mutator,
            bytes,
            align,
            0,
            AllocationSemantics::Default,
        );
        assert!(
            !start.is_zero(),
            "MMTk returned a zero address for Yulang object allocation"
        );
        let object_ref = initialize_yulang_mmtk_object(start, kind, trace_slots, raw_payload_size);
        mmtk::memory_manager::post_alloc(
            &mut self.mutator,
            object_ref,
            bytes,
            AllocationSemantics::Default,
        );
        object_ref
    }

    fn payload_ptr(object: ObjectReference) -> *mut YObject {
        YulangMmtkObjectHeader::raw_payload_address(object).to_mut_ptr()
    }

    fn mmtk_header(object: ObjectReference) -> YulangMmtkObjectHeader {
        unsafe { object.to_raw_address().load::<YulangMmtkObjectHeader>() }
    }

    fn object_header_from_ref(object: ObjectReference) -> crate::gc_runtime::YObjectHeader {
        let header = Self::mmtk_header(object);
        crate::gc_runtime::YObjectHeader {
            kind: header.kind(),
            trace_slots: header.trace_slot_count(),
        }
    }
}

#[cfg(feature = "mmtk-runtime")]
#[derive(Debug, Clone, PartialEq, Eq)]
enum MmtkPayloadStorage {
    SemanticObject,
    RawBytes,
    NativeBlock {
        layout: NativeLayoutHandle,
    },
    StringLeaf {
        len_chars: usize,
        len_bytes: usize,
    },
    StringNode {
        color: TreeColor,
        len_chars: usize,
        len_bytes: usize,
    },
    ListLeaf {
        len: usize,
    },
    ListNode {
        color: TreeColor,
        len: usize,
    },
}

#[cfg(feature = "mmtk-runtime")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TreeColor {
    Red,
    Black,
}

#[cfg(feature = "mmtk-runtime")]
fn raw_address(raw: usize) -> mmtk::util::Address {
    unsafe { mmtk::util::Address::from_usize(raw) }
}

#[cfg(feature = "mmtk-runtime")]
pub fn register_mmtk_cps_jit_symbols(builder: &mut cranelift_jit::JITBuilder) {
    macro_rules! symbols {
        ($($symbol:ident),+ $(,)?) => {
            $(builder.symbol(stringify!($symbol), $symbol as *const u8);)+
        };
    }

    symbols!(
        yulang_mmtk_cps_reset_i64,
        yulang_mmtk_cps_unit_i64,
        yulang_mmtk_cps_box_bool_i64,
        yulang_mmtk_cps_make_int_i64,
        yulang_mmtk_cps_string_literal_i64,
        yulang_mmtk_cps_string_concat_i64,
        yulang_mmtk_cps_string_eq_i64,
        yulang_mmtk_cps_string_len_i64,
        yulang_mmtk_cps_string_index_i64,
        yulang_mmtk_cps_string_slice_i64,
        yulang_mmtk_cps_string_slice_range_i64,
        yulang_mmtk_cps_string_splice_i64,
        yulang_mmtk_cps_string_splice_range_i64,
        yulang_mmtk_cps_string_to_bytes_i64,
        yulang_mmtk_cps_bytes_len_i64,
        yulang_mmtk_cps_bytes_eq_i64,
        yulang_mmtk_cps_bytes_concat_i64,
        yulang_mmtk_cps_bytes_index_i64,
        yulang_mmtk_cps_bytes_slice_i64,
        yulang_mmtk_cps_bytes_slice_range_i64,
        yulang_mmtk_cps_bytes_to_utf8_raw_i64,
        yulang_mmtk_cps_bytes_to_path_i64,
        yulang_mmtk_cps_path_to_bytes_i64,
        yulang_mmtk_cps_tuple_i64_0,
        yulang_mmtk_cps_tuple_i64_1,
        yulang_mmtk_cps_tuple_i64_2,
        yulang_mmtk_cps_tuple_i64_3,
        yulang_mmtk_cps_tuple_i64_4,
        yulang_mmtk_cps_tuple_push_i64,
        yulang_mmtk_cps_tuple_get_i64,
        yulang_mmtk_cps_record_empty_i64,
        yulang_mmtk_cps_record_insert_i64,
        yulang_mmtk_cps_record_select_i64,
        yulang_mmtk_cps_record_select_or_default_i64,
        yulang_mmtk_cps_record_has_field_i64,
        yulang_mmtk_cps_record_without_field_i64,
        yulang_mmtk_cps_register_tag_i64,
        yulang_mmtk_cps_variant_i64_0,
        yulang_mmtk_cps_variant_i64_1,
        yulang_mmtk_cps_variant_tag_eq_i64,
        yulang_mmtk_cps_variant_payload_i64,
        yulang_mmtk_cps_list_empty_i64,
        yulang_mmtk_cps_list_singleton_i64,
        yulang_mmtk_cps_list_merge_i64,
        yulang_mmtk_cps_list_len_i64,
        yulang_mmtk_cps_list_index_i64,
        yulang_mmtk_cps_list_slice_i64,
        yulang_mmtk_cps_list_slice_range_i64,
        yulang_mmtk_cps_list_splice_i64,
        yulang_mmtk_cps_list_splice_range_i64,
        yulang_mmtk_cps_list_view_raw_i64,
        yulang_mmtk_cps_int_to_string_i64,
        yulang_mmtk_cps_int_to_hex_i64,
        yulang_mmtk_cps_int_to_upper_hex_i64,
        yulang_mmtk_cps_bool_to_string_i64,
        yulang_mmtk_cps_float_to_string_f64,
        yulang_mmtk_cps_bool_not_i64,
        yulang_mmtk_cps_bool_eq_i64,
        yulang_mmtk_cps_bool_truthy_i64,
        yulang_mmtk_cps_int_add_i64,
        yulang_mmtk_cps_int_sub_i64,
        yulang_mmtk_cps_int_mul_i64,
        yulang_mmtk_cps_int_div_i64,
        yulang_mmtk_cps_int_eq_i64,
        yulang_mmtk_cps_int_lt_i64,
        yulang_mmtk_cps_int_le_i64,
        yulang_mmtk_cps_int_gt_i64,
        yulang_mmtk_cps_int_ge_i64,
    );
}

#[cfg(feature = "mmtk-runtime")]
pub struct MmtkNativeRuntimeContext {
    context: GcRuntimeContext<MmtkHeap>,
}

#[cfg(feature = "mmtk-runtime")]
impl MmtkNativeRuntimeContext {
    pub fn new_no_gc() -> Result<Self, MmtkConfigError> {
        Ok(Self {
            context: GcRuntimeContext::with_heap(MmtkHeap::new_no_gc()?),
        })
    }

    pub fn context(&self) -> &GcRuntimeContext<MmtkHeap> {
        &self.context
    }

    pub fn context_mut(&mut self) -> &mut GcRuntimeContext<MmtkHeap> {
        &mut self.context
    }

    pub fn make_unit(&self) -> YValue {
        YValue::UNIT
    }

    pub fn make_bool(&self, value: bool) -> YValue {
        YValue::from_bool(value)
    }

    pub fn make_int_text(&mut self, bytes: &[u8]) -> Option<YValue> {
        let text = std::str::from_utf8(bytes).ok()?;
        self.context.alloc_int_text(text)
    }

    pub fn make_string(&mut self, bytes: &[u8]) -> Option<YValue> {
        let text = std::str::from_utf8(bytes).ok()?;
        let leaves = chunk_str_bytes(text)
            .into_iter()
            .map(|leaf| self.context.heap_mut().allocate_string_leaf(leaf))
            .collect::<Option<Vec<_>>>()?;
        self.build_balanced_string(leaves)
    }

    pub fn make_bytes(&mut self, bytes: &[u8]) -> YValue {
        self.context
            .heap_mut()
            .allocate_raw_payload(YObjectKind::Bytes, &[], bytes)
    }

    pub fn make_path_bytes(&mut self, bytes: &[u8]) -> YValue {
        self.context
            .heap_mut()
            .allocate_raw_payload(YObjectKind::Path, &[], bytes)
    }

    pub fn string_concat(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        self.string_concat_tree(left, right)
    }

    pub fn string_byte_len(&self, value: YValue) -> Option<usize> {
        self.string_tree_len_bytes(value)
    }

    pub fn string_len(&self, value: YValue) -> Option<usize> {
        self.string_tree_len_chars(value)
    }

    pub fn string_eq(&self, left: YValue, right: YValue) -> Option<bool> {
        Some(self.render_string(left)? == self.render_string(right)?)
    }

    pub fn string_index(&mut self, value: YValue, index: usize) -> Option<YValue> {
        self.string_index_range_tree(value, index, index.checked_add(1)?)
    }

    pub fn string_slice(&mut self, value: YValue, start: usize, end: usize) -> Option<YValue> {
        self.string_index_range_tree(value, start, end)
    }

    pub fn string_slice_range(&mut self, value: YValue, range: YValue) -> Option<YValue> {
        let (start, end) = self.normalized_int_range_value(range, self.string_len(value)?)?;
        self.string_slice(value, start, end)
    }

    pub fn string_splice(
        &mut self,
        value: YValue,
        start: usize,
        end: usize,
        insert: YValue,
    ) -> Option<YValue> {
        let text = self.render_string(value)?;
        let len = text.chars().count();
        if start > end || end > len {
            return None;
        }
        let prefix = self.string_index_range_tree(value, 0, start)?;
        let suffix = self.string_index_range_tree(value, end, len)?;
        let inserted = self.string_concat_tree(prefix, insert)?;
        self.string_concat_tree(inserted, suffix)
    }

    pub fn string_splice_range(
        &mut self,
        value: YValue,
        range: YValue,
        insert: YValue,
    ) -> Option<YValue> {
        let (start, end) = self.normalized_int_range_value(range, self.string_len(value)?)?;
        self.string_splice(value, start, end, insert)
    }

    pub fn string_to_bytes(&mut self, value: YValue) -> Option<YValue> {
        let text = self.render_string(value)?;
        Some(self.make_bytes(text.as_bytes()))
    }

    pub fn bytes_len(&self, value: YValue) -> Option<usize> {
        Some(self.render_bytes(value)?.len())
    }

    pub fn bytes_eq(&self, left: YValue, right: YValue) -> Option<bool> {
        Some(self.render_bytes(left)? == self.render_bytes(right)?)
    }

    pub fn bytes_concat(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        let mut bytes = self.render_bytes(left)?;
        bytes.extend(self.render_bytes(right)?);
        Some(self.make_bytes(&bytes))
    }

    pub fn bytes_get(&self, value: YValue, index: usize) -> Option<u8> {
        self.render_bytes(value)?.get(index).copied()
    }

    pub fn bytes_slice(&mut self, value: YValue, start: usize, end: usize) -> Option<YValue> {
        let bytes = self.render_bytes(value)?;
        Some(self.make_bytes(bytes.get(start..end)?))
    }

    pub fn bytes_slice_range(&mut self, value: YValue, range: YValue) -> Option<YValue> {
        let (start, end) = self.normalized_int_range_value(range, self.bytes_len(value)?)?;
        self.bytes_slice(value, start, end)
    }

    pub fn bytes_to_utf8_raw(&mut self, value: YValue) -> Option<YValue> {
        let bytes = self.render_bytes(value)?;
        let (text, valid_len) = match std::str::from_utf8(&bytes) {
            Ok(text) => (text, bytes.len()),
            Err(error) => {
                let valid = error.valid_up_to();
                (std::str::from_utf8(&bytes[..valid]).ok()?, valid)
            }
        };
        let text = self.make_string(text.as_bytes())?;
        let valid_len = YValue::from_i63(i64::try_from(valid_len).ok()?)?;
        Some(self.alloc_compact_tuple(&[text, valid_len]))
    }

    pub fn bytes_to_path(&mut self, value: YValue) -> Option<YValue> {
        let bytes = self.render_bytes(value)?;
        Some(self.make_path_bytes(&bytes))
    }

    pub fn path_to_bytes(&mut self, value: YValue) -> Option<YValue> {
        let bytes = self.render_path_bytes(value)?;
        Some(self.make_bytes(&bytes))
    }

    pub fn tuple_empty(&mut self) -> YValue {
        self.alloc_compact_tuple(&[])
    }

    pub fn tuple_push(&mut self, tuple: YValue, value: YValue) -> Option<YValue> {
        let mut items = self.tuple_items(tuple)?;
        items.push(value);
        Some(self.alloc_compact_tuple(&items))
    }

    pub fn tuple_get(&self, tuple: YValue, index: usize) -> Option<YValue> {
        self.tuple_items(tuple)?.get(index).copied()
    }

    pub fn record_empty(&mut self) -> YValue {
        self.alloc_compact_record(&[])
    }

    pub fn record_insert(&mut self, record: YValue, field: &[u8], value: YValue) -> Option<YValue> {
        let field = std::str::from_utf8(field).ok()?;
        let mut fields = self.record_fields(record)?;
        if let Some((_, existing)) = fields.iter_mut().find(|(name, _)| name.as_ref() == field) {
            *existing = value;
        } else {
            fields.push((Box::<str>::from(field), value));
        }
        Some(self.alloc_compact_record(&fields))
    }

    pub fn record_get(&self, record: YValue, field: &[u8]) -> Option<YValue> {
        let field = std::str::from_utf8(field).ok()?;
        self.record_fields(record)?
            .iter()
            .find(|(name, _)| name.as_ref() == field)
            .map(|(_, value)| *value)
    }

    pub fn record_get_or_default(
        &self,
        record: YValue,
        field: &[u8],
        default: YValue,
    ) -> Option<YValue> {
        let field = std::str::from_utf8(field).ok()?;
        let fields = self.record_fields(record)?;
        Some(
            fields
                .iter()
                .find(|(name, _)| name.as_ref() == field)
                .map(|(_, value)| *value)
                .unwrap_or(default),
        )
    }

    pub fn record_has_field(&self, record: YValue, field: &[u8]) -> Option<bool> {
        let field = std::str::from_utf8(field).ok()?;
        Some(
            self.record_fields(record)?
                .iter()
                .any(|(name, _)| name.as_ref() == field),
        )
    }

    pub fn record_without_field(&mut self, record: YValue, field: &[u8]) -> Option<YValue> {
        let field = std::str::from_utf8(field).ok()?;
        let fields = self
            .record_fields(record)?
            .into_iter()
            .filter(|(name, _)| name.as_ref() != field)
            .collect::<Vec<_>>();
        Some(self.alloc_compact_record(&fields))
    }

    pub fn variant(&mut self, tag: &[u8], value: Option<YValue>) -> Option<YValue> {
        let tag = std::str::from_utf8(tag).ok()?;
        let tag = self.context.intern_symbol_path(tag);
        let payload_layout = value
            .iter()
            .map(|_| NativeFieldLayout::named("value", NativeFieldLane::YValue))
            .collect::<Vec<_>>();
        let layout = self
            .context
            .intern_native_layout(NativeLayout::variant(payload_layout));
        let mut fields = vec![NativeFieldValue::Symbol(tag)];
        fields.extend(value.into_iter().map(NativeFieldValue::YValue));
        let block = NativeHeapBlock::new(layout, fields)
            .expect("compact variant layout should match fields");
        Some(self.context.heap_mut().allocate_native_heap_block(&block))
    }

    pub fn variant_tag_eq(&self, variant: YValue, tag: &[u8]) -> Option<bool> {
        let expected = std::str::from_utf8(tag).ok()?;
        if self.is_compact_kind(variant, YObjectKind::Variant) {
            let NativeFieldValue::Symbol(tag) =
                self.context.heap().native_field_value(variant, 0)?
            else {
                return None;
            };
            return Some(
                self.context
                    .symbol(tag)
                    .is_some_and(|symbol| symbol.path.display_name() == expected),
            );
        }

        let object = self.context.object(variant)?;
        match object.payload() {
            YObjectPayload::Variant { tag, .. } => Some(tag.as_ref() == expected),
            _ => None,
        }
    }

    pub fn variant_payload(&self, variant: YValue) -> Option<YValue> {
        if self.is_compact_kind(variant, YObjectKind::Variant) {
            let NativeFieldValue::YValue(value) =
                self.context.heap().native_field_value(variant, 1)?
            else {
                return None;
            };
            return Some(value);
        }

        let object = self.context.object(variant)?;
        let YObjectPayload::Variant { value, .. } = object.payload() else {
            return None;
        };
        *value
    }

    pub fn list_empty(&mut self) -> YValue {
        self.context.heap_mut().allocate_list_leaf(&[])
    }

    pub fn list_singleton(&mut self, value: YValue) -> YValue {
        self.context.heap_mut().allocate_list_leaf(&[value])
    }

    pub fn list_merge(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        self.list_concat_tree(left, right)
    }

    pub fn list_len(&self, list: YValue) -> Option<usize> {
        Some(self.list_items(list)?.len())
    }

    pub fn list_get(&self, list: YValue, index: usize) -> Option<YValue> {
        self.list_items(list)?.get(index).copied()
    }

    pub fn list_slice(&mut self, list: YValue, start: usize, end: usize) -> Option<YValue> {
        let len = self.list_len(list)?;
        if start > end || end > len {
            return None;
        }
        let (_, suffix) = self.list_split_at_unchecked(list, start)?;
        let (range, _) = self.list_split_at_unchecked(suffix, end - start)?;
        Some(range)
    }

    pub fn list_slice_range(&mut self, list: YValue, range: YValue) -> Option<YValue> {
        let (start, end) = self.normalized_int_range_value(range, self.list_len(list)?)?;
        self.list_slice(list, start, end)
    }

    pub fn list_splice(
        &mut self,
        list: YValue,
        start: usize,
        end: usize,
        insert: YValue,
    ) -> Option<YValue> {
        let len = self.list_len(list)?;
        if start > end || end > len {
            return None;
        }
        let (prefix, rest) = self.list_split_at_unchecked(list, start)?;
        let (_, suffix) = self.list_split_at_unchecked(rest, end - start)?;
        let inserted = self.list_concat_tree(prefix, insert)?;
        self.list_concat_tree(inserted, suffix)
    }

    pub fn list_splice_range(
        &mut self,
        list: YValue,
        range: YValue,
        insert: YValue,
    ) -> Option<YValue> {
        let (start, end) = self.normalized_int_range_value(range, self.list_len(list)?)?;
        self.list_splice(list, start, end, insert)
    }

    pub fn list_view_raw(&mut self, list: YValue) -> Option<YValue> {
        let len = self.list_len(list)?;
        match len {
            0 => self.variant(b"empty", None),
            1 => self.variant(b"leaf", self.list_get(list, 0)),
            _ => {
                let mid = len / 2;
                let (left, right) = self.list_split_at_unchecked(list, mid)?;
                let payload = self.alloc_compact_tuple(&[left, right]);
                self.variant(b"node", Some(payload))
            }
        }
    }

    pub fn int_to_string(&mut self, value: YValue) -> Option<YValue> {
        let text = self.int_text(value)?;
        self.make_string(text.as_bytes())
    }

    pub fn int_to_hex(&mut self, value: YValue, upper: bool) -> Option<YValue> {
        let text = self.int_text(value)?;
        let number = text.parse::<i128>().ok()?;
        let rendered = if upper {
            format!("{number:X}")
        } else {
            format!("{number:x}")
        };
        self.make_string(rendered.as_bytes())
    }

    pub fn bool_to_string(&mut self, value: YValue) -> Option<YValue> {
        let text = if value.as_bool()? { "true" } else { "false" };
        self.make_string(text.as_bytes())
    }

    pub fn float_to_string(&mut self, value: f64) -> Option<YValue> {
        let text = mmtk_format_float(value);
        self.make_string(text.as_bytes())
    }

    pub fn int_add(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        self.context.checked_add_int(left, right)
    }

    pub fn int_sub(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        self.context.checked_sub_int(left, right)
    }

    pub fn int_mul(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        self.context.checked_mul_int(left, right)
    }

    pub fn int_div(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        let left = self.int_text(left)?.parse::<i128>().ok()?;
        let right = self.int_text(right)?.parse::<i128>().ok()?;
        if right == 0 {
            return None;
        }
        self.context.alloc_int_text((left / right).to_string())
    }

    pub fn int_compare(&self, left: YValue, right: YValue) -> Option<std::cmp::Ordering> {
        self.context.compare_int(left, right)
    }

    pub fn debug_value(&self, value: YValue) -> String {
        if self.is_compact_string_tree(value) {
            return self
                .render_string(value)
                .map(|text| format!("{text:?}"))
                .unwrap_or_else(|| "<invalid compact string>".to_string());
        }
        if self.is_compact_raw_payload(value, YObjectKind::Bytes) {
            return self
                .bytes_len(value)
                .map(|len| format!("<bytes len={len}>"))
                .unwrap_or_else(|| "<invalid compact bytes>".to_string());
        }
        if self.is_compact_raw_payload(value, YObjectKind::Path) {
            return self
                .render_path_bytes(value)
                .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
                .unwrap_or_else(|| "<invalid compact path>".to_string());
        }
        if self.is_compact_tuple(value) {
            return self.debug_tuple(value);
        }
        if self.is_compact_list_tree(value) {
            return self.debug_list(value);
        }
        self.context.debug_value(value)
    }

    fn alloc_compact_tuple(&mut self, items: &[YValue]) -> YValue {
        let layout = NativeLayout::tuple(
            items
                .iter()
                .map(|_| NativeFieldLayout::unnamed(NativeFieldLane::YValue))
                .collect::<Vec<_>>(),
        );
        let layout = self.context.intern_native_layout(layout);
        let fields = items
            .iter()
            .copied()
            .map(NativeFieldValue::YValue)
            .collect::<Vec<_>>();
        let block =
            NativeHeapBlock::new(layout, fields).expect("compact tuple layout should match fields");
        self.context.heap_mut().allocate_native_heap_block(&block)
    }

    fn tuple_items(&self, value: YValue) -> Option<Vec<YValue>> {
        if self.is_compact_tuple(value) {
            let field_count = self.context.heap().native_field_count(value)?;
            let mut items = Vec::with_capacity(field_count);
            for index in 0..field_count {
                let NativeFieldValue::YValue(item) =
                    self.context.heap().native_field_value(value, index)?
                else {
                    return None;
                };
                items.push(item);
            }
            return Some(items);
        }

        let object = self.context.object(value)?;
        let YObjectPayload::Tuple(items) = object.payload() else {
            return None;
        };
        Some(items.to_vec())
    }

    fn alloc_compact_record(&mut self, fields: &[(Box<str>, YValue)]) -> YValue {
        let layout = NativeLayout::new(
            crate::gc_runtime::NativeLayoutKind::Object(YObjectKind::Record),
            fields
                .iter()
                .map(|(name, _)| NativeFieldLayout::named(name.clone(), NativeFieldLane::YValue))
                .collect::<Vec<_>>(),
        );
        let layout = self.context.intern_native_layout(layout);
        let values = fields
            .iter()
            .map(|(_, value)| NativeFieldValue::YValue(*value))
            .collect::<Vec<_>>();
        let block = NativeHeapBlock::new(layout, values)
            .expect("compact record layout should match fields");
        self.context.heap_mut().allocate_native_heap_block(&block)
    }

    fn build_balanced_string(&mut self, mut items: Vec<YValue>) -> Option<YValue> {
        if items.is_empty() {
            return self.context.heap_mut().allocate_string_leaf(&[]);
        }
        while items.len() > 1 {
            let count = items.len();
            let triple_count = if count % 2 == 1 && count >= 3 { 1 } else { 0 };
            let mut next = Vec::with_capacity(items.len().div_ceil(2));
            let mut pairs = items.into_iter();
            let mut remaining_triples = triple_count;
            while let Some(first) = pairs.next() {
                if remaining_triples > 0 {
                    let Some(second) = pairs.next() else {
                        next.push(first);
                        break;
                    };
                    let Some(third) = pairs.next() else {
                        next.push(self.string_black_node(first, second)?);
                        break;
                    };
                    let red = self.string_red_node(first, second)?;
                    next.push(self.string_black_node(red, third)?);
                    remaining_triples -= 1;
                    continue;
                }
                match pairs.next() {
                    Some(second) => next.push(self.string_black_node(first, second)?),
                    None => next.push(first),
                }
            }
            items = next;
        }
        items.pop()
    }

    fn string_concat_tree(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        if self.string_tree_len_chars(left)? == 0 {
            return Some(right);
        }
        if self.string_tree_len_chars(right)? == 0 {
            return Some(left);
        }
        if self.is_string_leaf(left)
            && self.is_string_leaf(right)
            && self.string_tree_len_chars(left)? + self.string_tree_len_chars(right)?
                <= MAX_STRING_LEAF_CHARS
        {
            let mut merged = self.render_string(left)?;
            merged.push_str(&self.render_string(right)?);
            return self
                .context
                .heap_mut()
                .allocate_string_leaf(merged.as_bytes());
        }
        let left_height = self.string_black_height(left)?;
        let right_height = self.string_black_height(right)?;
        if left_height == right_height {
            self.string_black_node(left, right)
        } else if left_height > right_height {
            let joined = self.string_join_right(left, right, right_height)?;
            self.string_blacken(joined)
        } else {
            let joined = self.string_join_left(left, right, left_height)?;
            self.string_blacken(joined)
        }
    }

    fn string_index_range_tree(
        &mut self,
        value: YValue,
        start: usize,
        end: usize,
    ) -> Option<YValue> {
        let len = self.string_tree_len_chars(value)?;
        if start > end || end > len {
            return None;
        }
        if start == 0 && end == len {
            return Some(value);
        }
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::StringLeaf { .. } => {
                let text = self.render_string(value)?;
                let (start, end) = char_range_to_byte_range(&text, start, end)?;
                self.context
                    .heap_mut()
                    .allocate_string_leaf(text.get(start..end)?.as_bytes())
            }
            MmtkPayloadStorage::StringNode { .. } => {
                let [left, right] = self.tree_binary_children(value)?;
                let left_len = self.string_tree_len_chars(left)?;
                if end <= left_len {
                    self.string_index_range_tree(left, start, end)
                } else if start >= left_len {
                    self.string_index_range_tree(right, start - left_len, end - left_len)
                } else {
                    let left_part = self.string_index_range_tree(left, start, left_len)?;
                    let right_part = self.string_index_range_tree(right, 0, end - left_len)?;
                    self.string_concat_tree(left_part, right_part)
                }
            }
            _ => None,
        }
    }

    fn string_black_node(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        self.string_node(TreeColor::Black, left, right)
    }

    fn string_red_node(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        self.string_node(TreeColor::Red, left, right)
    }

    fn string_node(&mut self, color: TreeColor, left: YValue, right: YValue) -> Option<YValue> {
        let len_chars = self.string_tree_len_chars(left)? + self.string_tree_len_chars(right)?;
        let len_bytes = self.string_tree_len_bytes(left)? + self.string_tree_len_bytes(right)?;
        Some(
            self.context
                .heap_mut()
                .allocate_string_node(color, left, right, len_chars, len_bytes),
        )
    }

    fn string_blacken(&mut self, value: YValue) -> Option<YValue> {
        if self.string_node_color(value) == Some(TreeColor::Red) {
            let [left, right] = self.tree_binary_children(value)?;
            self.string_black_node(left, right)
        } else {
            Some(value)
        }
    }

    fn string_join_right(
        &mut self,
        left: YValue,
        right: YValue,
        right_height: usize,
    ) -> Option<YValue> {
        if self.is_string_node(left) {
            let [left_left, left_right] = self.tree_binary_children(left)?;
            if self.string_black_height(left_right)? > right_height {
                let joined = self.string_join_right(left_right, right, right_height)?;
                return self.string_balance(self.string_node_color(left)?, left_left, joined);
            }
            let joined = self.string_red_node(left_right, right)?;
            return self.string_balance(self.string_node_color(left)?, left_left, joined);
        }
        self.string_red_node(left, right)
    }

    fn string_join_left(
        &mut self,
        left: YValue,
        right: YValue,
        left_height: usize,
    ) -> Option<YValue> {
        if self.is_string_node(right) {
            let [right_left, right_right] = self.tree_binary_children(right)?;
            if self.string_black_height(right_left)? > left_height {
                let joined = self.string_join_left(left, right_left, left_height)?;
                return self.string_balance(self.string_node_color(right)?, joined, right_right);
            }
            let joined = self.string_red_node(left, right_left)?;
            return self.string_balance(self.string_node_color(right)?, joined, right_right);
        }
        self.string_red_node(left, right)
    }

    fn string_balance(&mut self, color: TreeColor, left: YValue, right: YValue) -> Option<YValue> {
        if color != TreeColor::Black {
            return self.string_node(color, left, right);
        }

        if self.string_node_color(left) == Some(TreeColor::Red) {
            let [left_left, left_right] = self.tree_binary_children(left)?;
            if self.string_node_color(left_left) == Some(TreeColor::Red) {
                let [ll_left, ll_right] = self.tree_binary_children(left_left)?;
                let new_left = self.string_black_node(ll_left, ll_right)?;
                let new_right = self.string_black_node(left_right, right)?;
                return self.string_red_node(new_left, new_right);
            }
            if self.string_node_color(left_right) == Some(TreeColor::Red) {
                let [lr_left, lr_right] = self.tree_binary_children(left_right)?;
                let new_left = self.string_black_node(left_left, lr_left)?;
                let new_right = self.string_black_node(lr_right, right)?;
                return self.string_red_node(new_left, new_right);
            }
        }

        if self.string_node_color(right) == Some(TreeColor::Red) {
            let [right_left, right_right] = self.tree_binary_children(right)?;
            if self.string_node_color(right_left) == Some(TreeColor::Red) {
                let [rl_left, rl_right] = self.tree_binary_children(right_left)?;
                let new_left = self.string_black_node(left, rl_left)?;
                let new_right = self.string_black_node(rl_right, right_right)?;
                return self.string_red_node(new_left, new_right);
            }
            if self.string_node_color(right_right) == Some(TreeColor::Red) {
                let [rr_left, rr_right] = self.tree_binary_children(right_right)?;
                let new_left = self.string_black_node(left, right_left)?;
                let new_right = self.string_black_node(rr_left, rr_right)?;
                return self.string_red_node(new_left, new_right);
            }
        }

        self.string_black_node(left, right)
    }

    fn string_tree_len_chars(&self, value: YValue) -> Option<usize> {
        match self.mmtk_storage(value) {
            Some(MmtkPayloadStorage::StringLeaf { len_chars, .. })
            | Some(MmtkPayloadStorage::StringNode { len_chars, .. }) => Some(*len_chars),
            _ => {
                let object = self.context.object(value)?;
                let YObjectPayload::String(value) = object.payload() else {
                    return None;
                };
                Some(self.render_string_payload(value)?.chars().count())
            }
        }
    }

    fn string_tree_len_bytes(&self, value: YValue) -> Option<usize> {
        match self.mmtk_storage(value) {
            Some(MmtkPayloadStorage::StringLeaf { len_bytes, .. })
            | Some(MmtkPayloadStorage::StringNode { len_bytes, .. }) => Some(*len_bytes),
            _ => Some(self.render_string(value)?.len()),
        }
    }

    fn string_black_height(&self, value: YValue) -> Option<usize> {
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::StringLeaf { .. } => Some(0),
            MmtkPayloadStorage::StringNode { color, .. } => {
                let [left, _] = self.tree_binary_children(value)?;
                Some(self.string_black_height(left)? + usize::from(*color == TreeColor::Black))
            }
            _ => None,
        }
    }

    #[cfg(test)]
    fn string_red_black_status(&self, value: YValue) -> Option<usize> {
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::StringLeaf { .. } => Some(0),
            MmtkPayloadStorage::StringNode { color, .. } => {
                let [left, right] = self.tree_binary_children(value)?;
                let left_height = self.string_red_black_status(left)?;
                let right_height = self.string_red_black_status(right)?;
                if left_height != right_height {
                    return None;
                }
                if *color == TreeColor::Red
                    && (self.string_node_color(left) == Some(TreeColor::Red)
                        || self.string_node_color(right) == Some(TreeColor::Red))
                {
                    return None;
                }
                Some(left_height + usize::from(*color == TreeColor::Black))
            }
            _ => None,
        }
    }

    fn string_node_color(&self, value: YValue) -> Option<TreeColor> {
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::StringNode { color, .. } => Some(*color),
            _ => None,
        }
    }

    fn is_string_leaf(&self, value: YValue) -> bool {
        matches!(
            self.mmtk_storage(value),
            Some(MmtkPayloadStorage::StringLeaf { .. })
        )
    }

    fn is_string_node(&self, value: YValue) -> bool {
        matches!(
            self.mmtk_storage(value),
            Some(MmtkPayloadStorage::StringNode { .. })
        )
    }

    fn build_balanced_list(&mut self, mut items: Vec<YValue>) -> Option<YValue> {
        if items.is_empty() {
            return Some(self.context.heap_mut().allocate_list_leaf(&[]));
        }
        while items.len() > 1 {
            let count = items.len();
            let triple_count = if count % 2 == 1 && count >= 3 { 1 } else { 0 };
            let mut next = Vec::with_capacity(items.len().div_ceil(2));
            let mut pairs = items.into_iter();
            let mut remaining_triples = triple_count;
            while let Some(first) = pairs.next() {
                if remaining_triples > 0 {
                    let Some(second) = pairs.next() else {
                        next.push(first);
                        break;
                    };
                    let Some(third) = pairs.next() else {
                        next.push(self.list_black_node(first, second)?);
                        break;
                    };
                    let red = self.list_red_node(first, second)?;
                    next.push(self.list_black_node(red, third)?);
                    remaining_triples -= 1;
                    continue;
                }
                match pairs.next() {
                    Some(second) => next.push(self.list_black_node(first, second)?),
                    None => next.push(first),
                }
            }
            items = next;
        }
        items.pop()
    }

    fn list_from_items(&mut self, items: &[YValue]) -> Option<YValue> {
        let leaves = items
            .chunks(MAX_LIST_LEAF_ITEMS)
            .map(|chunk| self.context.heap_mut().allocate_list_leaf(chunk))
            .collect::<Vec<_>>();
        self.build_balanced_list(leaves)
    }

    fn list_concat_tree(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        if self.list_tree_len(left)? == 0 {
            return Some(right);
        }
        if self.list_tree_len(right)? == 0 {
            return Some(left);
        }
        if self.is_list_leaf(left)
            && self.is_list_leaf(right)
            && self.list_tree_len(left)? + self.list_tree_len(right)? <= MAX_LIST_LEAF_ITEMS
        {
            let mut items = self.list_leaf_items(left)?;
            items.extend(self.list_leaf_items(right)?);
            return Some(self.context.heap_mut().allocate_list_leaf(&items));
        }
        let left_height = self.list_black_height(left)?;
        let right_height = self.list_black_height(right)?;
        if left_height == right_height {
            self.list_black_node(left, right)
        } else if left_height > right_height {
            let joined = self.list_join_right(left, right, right_height)?;
            self.list_blacken(joined)
        } else {
            let joined = self.list_join_left(left, right, left_height)?;
            self.list_blacken(joined)
        }
    }

    fn list_split_at_unchecked(&mut self, value: YValue, index: usize) -> Option<(YValue, YValue)> {
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::ListLeaf { .. } => {
                let items = self.list_leaf_items(value)?;
                let prefix = self.list_from_items(items.get(..index)?)?;
                let suffix = self.list_from_items(items.get(index..)?)?;
                Some((prefix, suffix))
            }
            MmtkPayloadStorage::ListNode { .. } => {
                let [left, right] = self.tree_binary_children(value)?;
                let left_len = self.list_tree_len(left)?;
                if index < left_len {
                    let (prefix, left_suffix) = self.list_split_at_unchecked(left, index)?;
                    let suffix = self.list_concat_tree(left_suffix, right)?;
                    Some((prefix, suffix))
                } else if index > left_len {
                    let (right_prefix, suffix) =
                        self.list_split_at_unchecked(right, index - left_len)?;
                    let prefix = self.list_concat_tree(left, right_prefix)?;
                    Some((prefix, suffix))
                } else {
                    Some((left, right))
                }
            }
            _ => None,
        }
    }

    fn list_black_node(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        self.list_node(TreeColor::Black, left, right)
    }

    fn list_red_node(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        self.list_node(TreeColor::Red, left, right)
    }

    fn list_node(&mut self, color: TreeColor, left: YValue, right: YValue) -> Option<YValue> {
        let len = self.list_tree_len(left)? + self.list_tree_len(right)?;
        Some(
            self.context
                .heap_mut()
                .allocate_list_node(color, left, right, len),
        )
    }

    fn list_blacken(&mut self, value: YValue) -> Option<YValue> {
        if self.list_node_color(value) == Some(TreeColor::Red) {
            let [left, right] = self.tree_binary_children(value)?;
            self.list_black_node(left, right)
        } else {
            Some(value)
        }
    }

    fn list_join_right(
        &mut self,
        left: YValue,
        right: YValue,
        right_height: usize,
    ) -> Option<YValue> {
        if self.is_list_node(left) {
            let [left_left, left_right] = self.tree_binary_children(left)?;
            if self.list_black_height(left_right)? > right_height {
                let joined = self.list_join_right(left_right, right, right_height)?;
                return self.list_balance(self.list_node_color(left)?, left_left, joined);
            }
            let joined = self.list_red_node(left_right, right)?;
            return self.list_balance(self.list_node_color(left)?, left_left, joined);
        }
        self.list_red_node(left, right)
    }

    fn list_join_left(
        &mut self,
        left: YValue,
        right: YValue,
        left_height: usize,
    ) -> Option<YValue> {
        if self.is_list_node(right) {
            let [right_left, right_right] = self.tree_binary_children(right)?;
            if self.list_black_height(right_left)? > left_height {
                let joined = self.list_join_left(left, right_left, left_height)?;
                return self.list_balance(self.list_node_color(right)?, joined, right_right);
            }
            let joined = self.list_red_node(left, right_left)?;
            return self.list_balance(self.list_node_color(right)?, joined, right_right);
        }
        self.list_red_node(left, right)
    }

    fn list_balance(&mut self, color: TreeColor, left: YValue, right: YValue) -> Option<YValue> {
        if color != TreeColor::Black {
            return self.list_node(color, left, right);
        }

        if self.list_node_color(left) == Some(TreeColor::Red) {
            let [left_left, left_right] = self.tree_binary_children(left)?;
            if self.list_node_color(left_left) == Some(TreeColor::Red) {
                let [ll_left, ll_right] = self.tree_binary_children(left_left)?;
                let new_left = self.list_black_node(ll_left, ll_right)?;
                let new_right = self.list_black_node(left_right, right)?;
                return self.list_red_node(new_left, new_right);
            }
            if self.list_node_color(left_right) == Some(TreeColor::Red) {
                let [lr_left, lr_right] = self.tree_binary_children(left_right)?;
                let new_left = self.list_black_node(left_left, lr_left)?;
                let new_right = self.list_black_node(lr_right, right)?;
                return self.list_red_node(new_left, new_right);
            }
        }

        if self.list_node_color(right) == Some(TreeColor::Red) {
            let [right_left, right_right] = self.tree_binary_children(right)?;
            if self.list_node_color(right_left) == Some(TreeColor::Red) {
                let [rl_left, rl_right] = self.tree_binary_children(right_left)?;
                let new_left = self.list_black_node(left, rl_left)?;
                let new_right = self.list_black_node(rl_right, right_right)?;
                return self.list_red_node(new_left, new_right);
            }
            if self.list_node_color(right_right) == Some(TreeColor::Red) {
                let [rr_left, rr_right] = self.tree_binary_children(right_right)?;
                let new_left = self.list_black_node(left, right_left)?;
                let new_right = self.list_black_node(rr_left, rr_right)?;
                return self.list_red_node(new_left, new_right);
            }
        }

        self.list_black_node(left, right)
    }

    fn list_tree_len(&self, value: YValue) -> Option<usize> {
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::ListLeaf { len } | MmtkPayloadStorage::ListNode { len, .. } => {
                Some(*len)
            }
            _ => None,
        }
    }

    fn list_black_height(&self, value: YValue) -> Option<usize> {
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::ListLeaf { .. } => Some(0),
            MmtkPayloadStorage::ListNode { color, .. } => {
                let [left, _] = self.tree_binary_children(value)?;
                Some(self.list_black_height(left)? + usize::from(*color == TreeColor::Black))
            }
            _ => None,
        }
    }

    #[cfg(test)]
    fn list_red_black_status(&self, value: YValue) -> Option<usize> {
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::ListLeaf { .. } => Some(0),
            MmtkPayloadStorage::ListNode { color, .. } => {
                let [left, right] = self.tree_binary_children(value)?;
                let left_height = self.list_red_black_status(left)?;
                let right_height = self.list_red_black_status(right)?;
                if left_height != right_height {
                    return None;
                }
                if *color == TreeColor::Red
                    && (self.list_node_color(left) == Some(TreeColor::Red)
                        || self.list_node_color(right) == Some(TreeColor::Red))
                {
                    return None;
                }
                Some(left_height + usize::from(*color == TreeColor::Black))
            }
            _ => None,
        }
    }

    fn list_node_color(&self, value: YValue) -> Option<TreeColor> {
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::ListNode { color, .. } => Some(*color),
            _ => None,
        }
    }

    fn is_list_leaf(&self, value: YValue) -> bool {
        matches!(
            self.mmtk_storage(value),
            Some(MmtkPayloadStorage::ListLeaf { .. })
        )
    }

    fn is_list_node(&self, value: YValue) -> bool {
        matches!(
            self.mmtk_storage(value),
            Some(MmtkPayloadStorage::ListNode { .. })
        )
    }

    fn record_fields(&self, value: YValue) -> Option<Vec<(Box<str>, YValue)>> {
        if self.is_compact_kind(value, YObjectKind::Record) {
            let field_count = self.context.heap().native_field_count(value)?;
            let mut fields = Vec::with_capacity(field_count);
            for index in 0..field_count {
                let name = self.context.heap().native_field_name(value, index)?;
                let NativeFieldValue::YValue(field_value) =
                    self.context.heap().native_field_value(value, index)?
                else {
                    return None;
                };
                fields.push((Box::<str>::from(name), field_value));
            }
            return Some(fields);
        }

        let object = self.context.object(value)?;
        let YObjectPayload::Record(fields) = object.payload() else {
            return None;
        };
        Some(fields.to_vec())
    }

    fn is_compact_tuple(&self, value: YValue) -> bool {
        self.is_compact_kind(value, YObjectKind::Tuple)
    }

    fn is_compact_kind(&self, value: YValue, kind: YObjectKind) -> bool {
        self.context.object(value).is_none()
            && self
                .context
                .heap()
                .object_header(value)
                .is_some_and(|header| header.kind == kind)
            && self.context.heap().native_field_count(value).is_some()
    }

    fn is_compact_string_tree(&self, value: YValue) -> bool {
        matches!(
            self.mmtk_storage(value),
            Some(MmtkPayloadStorage::StringLeaf { .. })
                | Some(MmtkPayloadStorage::StringNode { .. })
        )
    }

    fn is_compact_list_tree(&self, value: YValue) -> bool {
        matches!(
            self.mmtk_storage(value),
            Some(MmtkPayloadStorage::ListLeaf { .. }) | Some(MmtkPayloadStorage::ListNode { .. })
        )
    }

    fn mmtk_storage(&self, value: YValue) -> Option<&MmtkPayloadStorage> {
        let raw = value.heap_reference_raw()?;
        self.context.heap().objects.get(&raw)
    }

    fn tree_binary_children(&self, value: YValue) -> Option<[YValue; 2]> {
        let children = self.context.heap().trace_children(value)?;
        Some([*children.first()?, *children.get(1)?])
    }

    fn debug_tuple(&self, value: YValue) -> String {
        let Some(items) = self.tuple_items(value) else {
            return "<invalid compact tuple>".to_string();
        };
        let rendered = items
            .into_iter()
            .map(|item| self.debug_value(item))
            .collect::<Vec<_>>();
        match rendered.as_slice() {
            [] => "()".to_string(),
            [one] => format!("({one},)"),
            _ => format!("({})", rendered.join(", ")),
        }
    }

    fn debug_list(&self, value: YValue) -> String {
        let Some(items) = self.list_items(value) else {
            return "<invalid compact list>".to_string();
        };
        let rendered = items
            .into_iter()
            .map(|item| self.debug_value(item))
            .collect::<Vec<_>>();
        format!("[{}]", rendered.join(", "))
    }

    fn render_string(&self, value: YValue) -> Option<String> {
        if self.is_compact_string_tree(value) {
            let bytes = self.context.heap().raw_payload_bytes(value)?;
            return match self.mmtk_storage(value)? {
                MmtkPayloadStorage::StringLeaf { .. } => {
                    std::str::from_utf8(bytes).map(str::to_string).ok()
                }
                MmtkPayloadStorage::StringNode { .. } => {
                    let [left, right] = self.tree_binary_children(value)?;
                    let mut out = self.render_string(left)?;
                    out.push_str(&self.render_string(right)?);
                    Some(out)
                }
                _ => None,
            };
        }

        let object = self.context.object(value)?;
        let YObjectPayload::String(value) = object.payload() else {
            return None;
        };
        self.render_string_payload(value)
    }

    fn render_bytes(&self, value: YValue) -> Option<Vec<u8>> {
        if self.is_compact_raw_payload(value, YObjectKind::Bytes) {
            return Some(self.context.heap().raw_payload_bytes(value)?.to_vec());
        }

        let object = self.context.object(value)?;
        let YObjectPayload::Bytes(value) = object.payload() else {
            return None;
        };
        Some(value.to_vec())
    }

    fn render_path_bytes(&self, value: YValue) -> Option<Vec<u8>> {
        if self.is_compact_raw_payload(value, YObjectKind::Path) {
            return Some(self.context.heap().raw_payload_bytes(value)?.to_vec());
        }

        let object = self.context.object(value)?;
        let YObjectPayload::Path(value) = object.payload() else {
            return None;
        };
        Some(path_buf_bytes(value))
    }

    fn render_string_payload(&self, value: &YString) -> Option<String> {
        match value {
            YString::Flat(value) => Some(value.to_string()),
            YString::Concat { left, right } => {
                let mut out = self.render_string(*left)?;
                out.push_str(&self.render_string(*right)?);
                Some(out)
            }
            YString::Slice { source, start, end } => {
                let source = self.render_string(*source)?;
                source.get(*start..*end).map(str::to_string)
            }
        }
    }

    fn is_compact_raw_payload(&self, value: YValue, kind: YObjectKind) -> bool {
        matches!(self.mmtk_storage(value), Some(MmtkPayloadStorage::RawBytes))
            && self
                .context
                .heap()
                .object_header(value)
                .is_some_and(|header| header.kind == kind)
    }

    fn list_items(&self, value: YValue) -> Option<Vec<YValue>> {
        if self.is_compact_list_tree(value) {
            match self.mmtk_storage(value)? {
                MmtkPayloadStorage::ListLeaf { .. } => return self.list_leaf_items(value),
                MmtkPayloadStorage::ListNode { .. } => {
                    let [left, right] = self.tree_binary_children(value)?;
                    let mut out = self.list_items(left)?;
                    out.extend(self.list_items(right)?);
                    return Some(out);
                }
                _ => {}
            }
        }

        let object = self.context.object(value)?;
        let YObjectPayload::List(value) = object.payload() else {
            return None;
        };
        self.list_payload_items(value)
    }

    fn list_payload_items(&self, value: &YList) -> Option<Vec<YValue>> {
        match value {
            YList::Flat(items) => Some(items.to_vec()),
            YList::Concat { left, right } => {
                let mut out = self.list_items(*left)?;
                out.extend(self.list_items(*right)?);
                Some(out)
            }
            YList::Slice { source, start, end } => {
                let source = self.list_items(*source)?;
                source.get(*start..*end).map(<[YValue]>::to_vec)
            }
        }
    }

    fn list_leaf_items(&self, value: YValue) -> Option<Vec<YValue>> {
        match self.mmtk_storage(value)? {
            MmtkPayloadStorage::ListLeaf { len } => {
                let children = self.context.heap().trace_children(value)?;
                (children.len() == *len).then_some(children)
            }
            _ => None,
        }
    }

    fn normalized_int_range_value(&self, value: YValue, len: usize) -> Option<(usize, usize)> {
        (self.variant_tag_name(value)?.as_ref() == "within").then_some(())?;
        let payload = self.variant_payload(value)?;
        let items = self.tuple_items(payload)?;
        let [start, end] = items.as_slice() else {
            return None;
        };
        let start = self.normalized_start_bound_value(*start)?;
        let end = self.normalized_end_bound_value(*end, len)?;
        (start <= end && end <= len).then_some((start, end))
    }

    fn normalized_start_bound_value(&self, value: YValue) -> Option<usize> {
        match self.variant_tag_name(value)?.as_ref() {
            "unbounded" => Some(0),
            "included" => self.int_variant_payload(value)?.try_into().ok(),
            "excluded" => self
                .int_variant_payload(value)?
                .checked_add(1)?
                .try_into()
                .ok(),
            _ => None,
        }
    }

    fn normalized_end_bound_value(&self, value: YValue, len: usize) -> Option<usize> {
        match self.variant_tag_name(value)?.as_ref() {
            "unbounded" => Some(len),
            "included" => self
                .int_variant_payload(value)?
                .checked_add(1)?
                .try_into()
                .ok(),
            "excluded" => self.int_variant_payload(value)?.try_into().ok(),
            _ => None,
        }
    }

    fn int_variant_payload(&self, value: YValue) -> Option<i64> {
        self.int_value_i64(self.variant_payload(value)?)
    }

    fn int_value_i64(&self, value: YValue) -> Option<i64> {
        if let Some(value) = value.as_i63() {
            return Some(value);
        }
        let object = self.context.object(value)?;
        let YObjectPayload::BigInt(value) = object.payload() else {
            return None;
        };
        value.parse().ok()
    }

    fn int_value_usize(&self, value: YValue) -> Option<usize> {
        self.int_value_i64(value)?.try_into().ok()
    }

    fn int_text(&self, value: YValue) -> Option<String> {
        if let Some(value) = value.as_i63() {
            return Some(value.to_string());
        }
        let object = self.context.object(value)?;
        let YObjectPayload::BigInt(value) = object.payload() else {
            return None;
        };
        Some(value.clone())
    }

    fn variant_tag_name(&self, value: YValue) -> Option<Box<str>> {
        if self.is_compact_kind(value, YObjectKind::Variant) {
            let NativeFieldValue::Symbol(tag) = self.context.heap().native_field_value(value, 0)?
            else {
                return None;
            };
            return self
                .context
                .symbol(tag)
                .map(|symbol| Box::<str>::from(symbol.path.display_name()));
        }

        let object = self.context.object(value)?;
        let YObjectPayload::Variant { tag, .. } = object.payload() else {
            return None;
        };
        Some(Box::from(tag.as_ref()))
    }
}

#[cfg(feature = "mmtk-runtime")]
fn encode_yvalue(value: YValue) -> i64 {
    value.raw() as i64
}

#[cfg(feature = "mmtk-runtime")]
fn decode_yvalue(value: i64) -> YValue {
    YValue::from_raw(value as usize)
}

#[cfg(feature = "mmtk-runtime")]
fn context_int_from_i64(value: i64) -> Option<i64> {
    YValue::from_i63(value).map(encode_yvalue)
}

#[cfg(feature = "mmtk-runtime")]
fn context_int_from_usize(value: usize) -> Option<i64> {
    i64::try_from(value).ok().and_then(context_int_from_i64)
}

#[cfg(feature = "mmtk-runtime")]
fn bytes_from_raw<'a>(ptr: *const u8, len: usize) -> Option<&'a [u8]> {
    if ptr.is_null() && len != 0 {
        return None;
    }
    Some(unsafe { std::slice::from_raw_parts(ptr, len) })
}

#[cfg(feature = "mmtk-runtime")]
fn mmtk_format_float(value: f64) -> String {
    let mut rendered = value.to_string();
    if !rendered.contains('.') && !rendered.contains('e') && !rendered.contains('E') {
        rendered.push_str(".0");
    }
    rendered
}

#[cfg(all(feature = "mmtk-runtime", unix))]
fn path_buf_bytes(path: &std::path::PathBuf) -> Vec<u8> {
    use std::os::unix::ffi::OsStrExt;

    path.as_os_str().as_bytes().to_vec()
}

#[cfg(all(feature = "mmtk-runtime", not(unix)))]
fn path_buf_bytes(path: &std::path::PathBuf) -> Vec<u8> {
    path.to_string_lossy().as_bytes().to_vec()
}

#[cfg(feature = "mmtk-runtime")]
fn char_range_to_byte_range(text: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    if start > end {
        return None;
    }
    let len = text.chars().count();
    if end > len {
        return None;
    }
    let start_byte = char_index_to_byte_index(text, start)?;
    let end_byte = char_index_to_byte_index(text, end)?;
    Some((start_byte, end_byte))
}

#[cfg(feature = "mmtk-runtime")]
fn char_index_to_byte_index(text: &str, index: usize) -> Option<usize> {
    if index == text.chars().count() {
        return Some(text.len());
    }
    text.char_indices().nth(index).map(|(byte, _)| byte)
}

#[cfg(feature = "mmtk-runtime")]
fn chunk_str_bytes(value: &str) -> Vec<&[u8]> {
    if value.is_empty() {
        return Vec::new();
    }
    let mut chunks = Vec::new();
    let mut start = 0;
    let mut chars = 0;
    for (byte_index, _) in value.char_indices() {
        if chars == MAX_STRING_LEAF_CHARS {
            chunks.push(&value.as_bytes()[start..byte_index]);
            start = byte_index;
            chars = 0;
        }
        chars += 1;
    }
    chunks.push(&value.as_bytes()[start..]);
    chunks
}

#[cfg(feature = "mmtk-runtime")]
thread_local! {
    static MMTK_CPS_CONTEXT: RefCell<Option<MmtkNativeRuntimeContext>> = const { RefCell::new(None) };
    static MMTK_CPS_TAG_NAMES: RefCell<HashMap<i64, Box<str>>> = RefCell::new(HashMap::new());
}

#[cfg(feature = "mmtk-runtime")]
fn with_mmtk_cps_context<R>(f: impl FnOnce(&mut MmtkNativeRuntimeContext) -> R) -> Option<R> {
    MMTK_CPS_CONTEXT.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.is_none() {
            *slot = Some(MmtkNativeRuntimeContext::new_no_gc().ok()?);
        }
        Some(f(slot
            .as_mut()
            .expect("MMTk CPS context should be initialized")))
    })
}

#[cfg(feature = "mmtk-runtime")]
fn mmtk_cps_tag_name(tag: i64) -> String {
    MMTK_CPS_TAG_NAMES.with(|names| {
        names
            .borrow()
            .get(&tag)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{tag}"))
    })
}

#[cfg(feature = "mmtk-runtime")]
fn mmtk_cps_register_tag_name(tag: i64, name: &str) {
    MMTK_CPS_TAG_NAMES.with(|names| {
        names
            .borrow_mut()
            .entry(tag)
            .or_insert_with(|| name.to_string().into_boxed_str());
    });
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_reset_i64() {
    MMTK_CPS_CONTEXT.with(|slot| {
        *slot.borrow_mut() = None;
    });
    MMTK_CPS_TAG_NAMES.with(|names| names.borrow_mut().clear());
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_unit_i64() -> i64 {
    encode_yvalue(YValue::UNIT)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_box_bool_i64(value: i64) -> i64 {
    encode_yvalue(YValue::from_bool(value != 0))
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_make_int_i64(ptr: *const u8, len: i64) -> i64 {
    let Ok(len) = usize::try_from(len) else {
        return 0;
    };
    let Some(bytes) = bytes_from_raw(ptr, len) else {
        return 0;
    };
    with_mmtk_cps_context(|context| context.make_int_text(bytes))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_literal_i64(ptr: *const u8, len: i64) -> i64 {
    let Ok(len) = usize::try_from(len) else {
        return 0;
    };
    let Some(bytes) = bytes_from_raw(ptr, len) else {
        return 0;
    };
    with_mmtk_cps_context(|context| context.make_string(bytes))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_concat_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        context.string_concat(decode_yvalue(left), decode_yvalue(right))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_eq_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.string_eq(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(YValue::from_bool)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_len_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.string_len(decode_yvalue(value)))
        .flatten()
        .and_then(context_int_from_usize)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_index_i64(value: i64, index: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        let index = context.int_value_usize(decode_yvalue(index))?;
        context.string_index(decode_yvalue(value), index)
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_slice_i64(value: i64, start: i64, end: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        let start = context.int_value_usize(decode_yvalue(start))?;
        let end = context.int_value_usize(decode_yvalue(end))?;
        context.string_slice(decode_yvalue(value), start, end)
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_slice_range_i64(value: i64, range: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        context.string_slice_range(decode_yvalue(value), decode_yvalue(range))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_splice_i64(
    value: i64,
    start: i64,
    end: i64,
    insert: i64,
) -> i64 {
    with_mmtk_cps_context(|context| {
        let start = context.int_value_usize(decode_yvalue(start))?;
        let end = context.int_value_usize(decode_yvalue(end))?;
        context.string_splice(decode_yvalue(value), start, end, decode_yvalue(insert))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_splice_range_i64(
    value: i64,
    range: i64,
    insert: i64,
) -> i64 {
    with_mmtk_cps_context(|context| {
        context.string_splice_range(
            decode_yvalue(value),
            decode_yvalue(range),
            decode_yvalue(insert),
        )
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_to_bytes_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.string_to_bytes(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_len_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_len(decode_yvalue(value)))
        .flatten()
        .and_then(context_int_from_usize)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_eq_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_eq(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(YValue::from_bool)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_concat_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_concat(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_index_i64(value: i64, index: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        let index = context.int_value_usize(decode_yvalue(index))?;
        context.bytes_get(decode_yvalue(value), index)
    })
    .flatten()
    .map(|byte| context_int_from_i64(i64::from(byte)))
    .flatten()
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_slice_i64(value: i64, start: i64, end: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        let start = context.int_value_usize(decode_yvalue(start))?;
        let end = context.int_value_usize(decode_yvalue(end))?;
        context.bytes_slice(decode_yvalue(value), start, end)
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_slice_range_i64(value: i64, range: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        context.bytes_slice_range(decode_yvalue(value), decode_yvalue(range))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_to_utf8_raw_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_to_utf8_raw(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_to_path_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_to_path(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_path_to_bytes_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.path_to_bytes(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_0() -> i64 {
    with_mmtk_cps_context(MmtkNativeRuntimeContext::tuple_empty)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_1(a: i64) -> i64 {
    let tuple = yulang_mmtk_cps_tuple_i64_0();
    yulang_mmtk_cps_tuple_push_i64(tuple, a)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_2(a: i64, b: i64) -> i64 {
    let tuple = yulang_mmtk_cps_tuple_i64_1(a);
    yulang_mmtk_cps_tuple_push_i64(tuple, b)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_3(a: i64, b: i64, c: i64) -> i64 {
    let tuple = yulang_mmtk_cps_tuple_i64_2(a, b);
    yulang_mmtk_cps_tuple_push_i64(tuple, c)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_4(a: i64, b: i64, c: i64, d: i64) -> i64 {
    let tuple = yulang_mmtk_cps_tuple_i64_3(a, b, c);
    yulang_mmtk_cps_tuple_push_i64(tuple, d)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_push_i64(tuple: i64, value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.tuple_push(decode_yvalue(tuple), decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_get_i64(tuple: i64, index: i64) -> i64 {
    let Ok(index) = usize::try_from(index) else {
        return 0;
    };
    with_mmtk_cps_context(|context| context.tuple_get(decode_yvalue(tuple), index))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_record_empty_i64() -> i64 {
    with_mmtk_cps_context(MmtkNativeRuntimeContext::record_empty)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_record_insert_i64(
    record: i64,
    name_ptr: *const u8,
    name_len: i64,
    value: i64,
) -> i64 {
    let Ok(name_len) = usize::try_from(name_len) else {
        return 0;
    };
    let Some(name) = bytes_from_raw(name_ptr, name_len) else {
        return 0;
    };
    with_mmtk_cps_context(|context| {
        context.record_insert(decode_yvalue(record), name, decode_yvalue(value))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_record_select_i64(
    record: i64,
    name_ptr: *const u8,
    name_len: i64,
) -> i64 {
    let Ok(name_len) = usize::try_from(name_len) else {
        return 0;
    };
    let Some(name) = bytes_from_raw(name_ptr, name_len) else {
        return 0;
    };
    with_mmtk_cps_context(|context| context.record_get(decode_yvalue(record), name))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_record_select_or_default_i64(
    record: i64,
    name_ptr: *const u8,
    name_len: i64,
    default: i64,
) -> i64 {
    let Ok(name_len) = usize::try_from(name_len) else {
        return 0;
    };
    let Some(name) = bytes_from_raw(name_ptr, name_len) else {
        return 0;
    };
    with_mmtk_cps_context(|context| {
        context.record_get_or_default(decode_yvalue(record), name, decode_yvalue(default))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_record_has_field_i64(
    record: i64,
    name_ptr: *const u8,
    name_len: i64,
) -> i64 {
    let Ok(name_len) = usize::try_from(name_len) else {
        return -1;
    };
    let Some(name) = bytes_from_raw(name_ptr, name_len) else {
        return -1;
    };
    with_mmtk_cps_context(|context| context.record_has_field(decode_yvalue(record), name))
        .flatten()
        .map(YValue::from_bool)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_record_without_field_i64(
    record: i64,
    name_ptr: *const u8,
    name_len: i64,
) -> i64 {
    let Ok(name_len) = usize::try_from(name_len) else {
        return 0;
    };
    let Some(name) = bytes_from_raw(name_ptr, name_len) else {
        return 0;
    };
    with_mmtk_cps_context(|context| context.record_without_field(decode_yvalue(record), name))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_register_tag_i64(tag: i64, ptr: *const u8, len: i64) -> i64 {
    let Ok(len) = usize::try_from(len) else {
        return 0;
    };
    let Some(bytes) = bytes_from_raw(ptr, len) else {
        return 0;
    };
    let Ok(name) = std::str::from_utf8(bytes) else {
        return 0;
    };
    mmtk_cps_register_tag_name(tag, name);
    0
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_variant_i64_0(tag: i64) -> i64 {
    let tag = mmtk_cps_tag_name(tag);
    with_mmtk_cps_context(|context| context.variant(tag.as_bytes(), None))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_variant_i64_1(tag: i64, value: i64) -> i64 {
    let tag = mmtk_cps_tag_name(tag);
    with_mmtk_cps_context(|context| context.variant(tag.as_bytes(), Some(decode_yvalue(value))))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_variant_tag_eq_i64(value: i64, tag: i64) -> i64 {
    let tag = mmtk_cps_tag_name(tag);
    with_mmtk_cps_context(|context| context.variant_tag_eq(decode_yvalue(value), tag.as_bytes()))
        .flatten()
        .map(YValue::from_bool)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_variant_payload_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.variant_payload(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_empty_i64() -> i64 {
    with_mmtk_cps_context(MmtkNativeRuntimeContext::list_empty)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_singleton_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.list_singleton(decode_yvalue(value)))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_merge_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.list_merge(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_len_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.list_len(decode_yvalue(value)))
        .flatten()
        .and_then(context_int_from_usize)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_index_i64(value: i64, index: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        let index = context.int_value_usize(decode_yvalue(index))?;
        context.list_get(decode_yvalue(value), index)
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_slice_i64(value: i64, start: i64, end: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        let start = context.int_value_usize(decode_yvalue(start))?;
        let end = context.int_value_usize(decode_yvalue(end))?;
        context.list_slice(decode_yvalue(value), start, end)
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_slice_range_i64(value: i64, range: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        context.list_slice_range(decode_yvalue(value), decode_yvalue(range))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_splice_i64(
    value: i64,
    start: i64,
    end: i64,
    insert: i64,
) -> i64 {
    with_mmtk_cps_context(|context| {
        let start = context.int_value_usize(decode_yvalue(start))?;
        let end = context.int_value_usize(decode_yvalue(end))?;
        context.list_splice(decode_yvalue(value), start, end, decode_yvalue(insert))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_splice_range_i64(
    value: i64,
    range: i64,
    insert: i64,
) -> i64 {
    with_mmtk_cps_context(|context| {
        context.list_splice_range(
            decode_yvalue(value),
            decode_yvalue(range),
            decode_yvalue(insert),
        )
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_view_raw_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.list_view_raw(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_to_string_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_to_string(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_to_hex_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_to_hex(decode_yvalue(value), false))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_to_upper_hex_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_to_hex(decode_yvalue(value), true))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bool_to_string_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bool_to_string(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_float_to_string_f64(value: f64) -> i64 {
    with_mmtk_cps_context(|context| context.float_to_string(value))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bool_not_i64(value: i64) -> i64 {
    let value = decode_yvalue(value).as_bool().map(|value| !value);
    value.map(YValue::from_bool).map(encode_yvalue).unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bool_eq_i64(left: i64, right: i64) -> i64 {
    let value = decode_yvalue(left)
        .as_bool()
        .zip(decode_yvalue(right).as_bool())
        .map(|(left, right)| left == right);
    value.map(YValue::from_bool).map(encode_yvalue).unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bool_truthy_i64(value: i64) -> i64 {
    decode_yvalue(value).as_bool().map(i64::from).unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_add_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_add(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_sub_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_sub(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_mul_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_mul(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_div_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_div(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_eq_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| {
        ordering == std::cmp::Ordering::Equal
    })
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_lt_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| ordering == std::cmp::Ordering::Less)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_le_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| {
        ordering != std::cmp::Ordering::Greater
    })
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_gt_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| {
        ordering == std::cmp::Ordering::Greater
    })
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_ge_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| ordering != std::cmp::Ordering::Less)
}

#[cfg(feature = "mmtk-runtime")]
fn mmtk_cps_int_compare_pred(
    left: i64,
    right: i64,
    pred: impl FnOnce(std::cmp::Ordering) -> bool,
) -> i64 {
    with_mmtk_cps_context(|context| context.int_compare(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(pred)
        .map(YValue::from_bool)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_context_new() -> *mut MmtkNativeRuntimeContext {
    MmtkNativeRuntimeContext::new_no_gc()
        .map(Box::new)
        .map(Box::into_raw)
        .unwrap_or(std::ptr::null_mut())
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_context_free(context: *mut MmtkNativeRuntimeContext) {
    if !context.is_null() {
        unsafe {
            drop(Box::from_raw(context));
        }
    }
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_make_unit(context: *mut MmtkNativeRuntimeContext) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return 0;
    };
    encode_yvalue(context.make_unit())
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_make_bool(
    context: *mut MmtkNativeRuntimeContext,
    value: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return 0;
    };
    encode_yvalue(context.make_bool(value != 0))
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_make_int(
    context: *mut MmtkNativeRuntimeContext,
    ptr: *const u8,
    len: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    let Some(bytes) = bytes_from_raw(ptr, len) else {
        return 0;
    };
    context.make_int_text(bytes).map(encode_yvalue).unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_make_string(
    context: *mut MmtkNativeRuntimeContext,
    ptr: *const u8,
    len: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    let Some(bytes) = bytes_from_raw(ptr, len) else {
        return 0;
    };
    context.make_string(bytes).map(encode_yvalue).unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_string_concat(
    context: *mut MmtkNativeRuntimeContext,
    left: i64,
    right: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .string_concat(decode_yvalue(left), decode_yvalue(right))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_string_byte_len(
    context: *mut MmtkNativeRuntimeContext,
    value: i64,
) -> isize {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return -1;
    };
    context
        .string_byte_len(decode_yvalue(value))
        .and_then(|len| isize::try_from(len).ok())
        .unwrap_or(-1)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_string_eq(
    context: *mut MmtkNativeRuntimeContext,
    left: i64,
    right: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return -1;
    };
    context
        .string_eq(decode_yvalue(left), decode_yvalue(right))
        .map(i64::from)
        .unwrap_or(-1)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_string_slice(
    context: *mut MmtkNativeRuntimeContext,
    value: i64,
    start: usize,
    end: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .string_slice(decode_yvalue(value), start, end)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_string_splice(
    context: *mut MmtkNativeRuntimeContext,
    value: i64,
    start: usize,
    end: usize,
    insert: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .string_splice(decode_yvalue(value), start, end, decode_yvalue(insert))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_tuple_empty(context: *mut MmtkNativeRuntimeContext) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    encode_yvalue(context.tuple_empty())
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_tuple_push(
    context: *mut MmtkNativeRuntimeContext,
    tuple: i64,
    value: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .tuple_push(decode_yvalue(tuple), decode_yvalue(value))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_tuple_get(
    context: *mut MmtkNativeRuntimeContext,
    tuple: i64,
    index: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return 0;
    };
    context
        .tuple_get(decode_yvalue(tuple), index)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_record_empty(context: *mut MmtkNativeRuntimeContext) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    encode_yvalue(context.record_empty())
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_record_insert(
    context: *mut MmtkNativeRuntimeContext,
    record: i64,
    field_ptr: *const u8,
    field_len: usize,
    value: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    let Some(field) = bytes_from_raw(field_ptr, field_len) else {
        return 0;
    };
    context
        .record_insert(decode_yvalue(record), field, decode_yvalue(value))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_record_get(
    context: *mut MmtkNativeRuntimeContext,
    record: i64,
    field_ptr: *const u8,
    field_len: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return 0;
    };
    let Some(field) = bytes_from_raw(field_ptr, field_len) else {
        return 0;
    };
    context
        .record_get(decode_yvalue(record), field)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_record_get_or_default(
    context: *mut MmtkNativeRuntimeContext,
    record: i64,
    field_ptr: *const u8,
    field_len: usize,
    default: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return 0;
    };
    let Some(field) = bytes_from_raw(field_ptr, field_len) else {
        return 0;
    };
    context
        .record_get_or_default(decode_yvalue(record), field, decode_yvalue(default))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_record_has_field(
    context: *mut MmtkNativeRuntimeContext,
    record: i64,
    field_ptr: *const u8,
    field_len: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return -1;
    };
    let Some(field) = bytes_from_raw(field_ptr, field_len) else {
        return -1;
    };
    context
        .record_has_field(decode_yvalue(record), field)
        .map(i64::from)
        .unwrap_or(-1)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_record_without_field(
    context: *mut MmtkNativeRuntimeContext,
    record: i64,
    field_ptr: *const u8,
    field_len: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    let Some(field) = bytes_from_raw(field_ptr, field_len) else {
        return 0;
    };
    context
        .record_without_field(decode_yvalue(record), field)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_variant(
    context: *mut MmtkNativeRuntimeContext,
    tag_ptr: *const u8,
    tag_len: usize,
    has_payload: i64,
    payload: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    let Some(tag) = bytes_from_raw(tag_ptr, tag_len) else {
        return 0;
    };
    let payload = (has_payload != 0).then(|| decode_yvalue(payload));
    context
        .variant(tag, payload)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_variant_tag_eq(
    context: *mut MmtkNativeRuntimeContext,
    variant: i64,
    tag_ptr: *const u8,
    tag_len: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return -1;
    };
    let Some(tag) = bytes_from_raw(tag_ptr, tag_len) else {
        return -1;
    };
    context
        .variant_tag_eq(decode_yvalue(variant), tag)
        .map(i64::from)
        .unwrap_or(-1)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_variant_payload(
    context: *mut MmtkNativeRuntimeContext,
    variant: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return 0;
    };
    context
        .variant_payload(decode_yvalue(variant))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_list_empty(context: *mut MmtkNativeRuntimeContext) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    encode_yvalue(context.list_empty())
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_list_singleton(
    context: *mut MmtkNativeRuntimeContext,
    value: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    encode_yvalue(context.list_singleton(decode_yvalue(value)))
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_list_merge(
    context: *mut MmtkNativeRuntimeContext,
    left: i64,
    right: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .list_merge(decode_yvalue(left), decode_yvalue(right))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_list_len(
    context: *mut MmtkNativeRuntimeContext,
    list: i64,
) -> isize {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return -1;
    };
    context
        .list_len(decode_yvalue(list))
        .and_then(|len| isize::try_from(len).ok())
        .unwrap_or(-1)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_list_get(
    context: *mut MmtkNativeRuntimeContext,
    list: i64,
    index: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return 0;
    };
    context
        .list_get(decode_yvalue(list), index)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_list_slice(
    context: *mut MmtkNativeRuntimeContext,
    list: i64,
    start: usize,
    end: usize,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .list_slice(decode_yvalue(list), start, end)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_list_splice(
    context: *mut MmtkNativeRuntimeContext,
    list: i64,
    start: usize,
    end: usize,
    insert: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .list_splice(decode_yvalue(list), start, end, decode_yvalue(insert))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_int_add(
    context: *mut MmtkNativeRuntimeContext,
    left: i64,
    right: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .int_add(decode_yvalue(left), decode_yvalue(right))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_int_sub(
    context: *mut MmtkNativeRuntimeContext,
    left: i64,
    right: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .int_sub(decode_yvalue(left), decode_yvalue(right))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_int_mul(
    context: *mut MmtkNativeRuntimeContext,
    left: i64,
    right: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    context
        .int_mul(decode_yvalue(left), decode_yvalue(right))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[cfg(feature = "mmtk-runtime")]
#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_int_compare(
    context: *mut MmtkNativeRuntimeContext,
    left: i64,
    right: i64,
) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return -2;
    };
    match context.int_compare(decode_yvalue(left), decode_yvalue(right)) {
        Some(std::cmp::Ordering::Less) => -1,
        Some(std::cmp::Ordering::Equal) => 0,
        Some(std::cmp::Ordering::Greater) => 1,
        None => -2,
    }
}

#[cfg(all(test, feature = "mmtk-runtime"))]
pub(crate) fn mmtk_test_lock() -> std::sync::MutexGuard<'static, ()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    LOCK.lock().unwrap_or_else(|poison| poison.into_inner())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "mmtk-runtime")]
    fn encoded_i63(value: i64) -> i64 {
        encode_yvalue(YValue::from_i63(value).expect("test integer should fit i63"))
    }

    #[cfg(feature = "mmtk-runtime")]
    fn encoded_bool(value: bool) -> i64 {
        encode_yvalue(YValue::from_bool(value))
    }

    #[cfg(feature = "mmtk-runtime")]
    fn declare_jit_import(
        module: &mut cranelift_jit::JITModule,
        builder: &mut cranelift_frontend::FunctionBuilder<'_>,
        name: &str,
        params: &[cranelift_codegen::ir::Type],
        returns: &[cranelift_codegen::ir::Type],
    ) -> cranelift_codegen::ir::FuncRef {
        use cranelift_codegen::ir::AbiParam;
        use cranelift_module::{Linkage, Module};

        let mut sig = module.make_signature();
        sig.params.extend(params.iter().copied().map(AbiParam::new));
        sig.returns
            .extend(returns.iter().copied().map(AbiParam::new));
        let id = module
            .declare_function(name, Linkage::Import, &sig)
            .unwrap_or_else(|error| panic!("declare import {name}: {error}"));
        module.declare_func_in_func(id, builder.func)
    }

    #[cfg(feature = "mmtk-runtime")]
    fn call_jit_i64(
        builder: &mut cranelift_frontend::FunctionBuilder<'_>,
        callee: cranelift_codegen::ir::FuncRef,
        args: &[cranelift_codegen::ir::Value],
    ) -> cranelift_codegen::ir::Value {
        use cranelift_codegen::ir::InstBuilder;

        let call = builder.ins().call(callee, args);
        match builder.inst_results(call) {
            [result] => *result,
            results => panic!("expected one i64 result, got {}", results.len()),
        }
    }

    #[test]
    fn default_mmtk_runtime_config_selects_single_threaded_nogc_spike() {
        let config = MmtkRuntimeConfig::default();

        assert_eq!(config.plan, MmtkRuntimePlan::NoGc);
        assert_eq!(
            config.option_pairs(),
            vec![("plan", "NoGC".to_string()), ("threads", "1".to_string())]
        );
        assert_eq!(config.options_string(), "plan=NoGC threads=1");
    }

    #[test]
    fn mmtk_runtime_config_formats_heap_and_plan_options() {
        let config = MmtkRuntimeConfig {
            plan: MmtkRuntimePlan::Immix,
            heap_min: Some("32M".to_string()),
            heap_max: Some("256M".to_string()),
            threads: Some(2),
        };

        assert_eq!(
            config.options_string(),
            "plan=Immix min_heap=32M max_heap=256M threads=2"
        );
    }

    #[test]
    fn mmtk_runtime_boundary_exposes_config_without_constructing_binding() {
        let boundary = MmtkRuntimeBoundary::new(MmtkRuntimeConfig {
            plan: MmtkRuntimePlan::MarkSweep,
            heap_min: None,
            heap_max: Some("64M".to_string()),
            threads: None,
        });

        assert_eq!(boundary.config().plan, MmtkRuntimePlan::MarkSweep);
        assert_eq!(boundary.options_string(), "plan=MarkSweep max_heap=64M");
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_runtime_boundary_builds_yulang_nogc_binding() {
        let _guard = mmtk_test_lock();
        let boundary = MmtkRuntimeBoundary::new(MmtkRuntimeConfig::prototype_no_gc());

        let _mmtk = boundary
            .build_yulang_mmtk()
            .expect("NoGC prototype config should build a Yulang MMTk binding");
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_heap_allocates_yheap_objects_and_records_trace_slots() {
        let _guard = mmtk_test_lock();
        use crate::gc_runtime::{GcRuntimeContext, YValue};
        use crate::mmtk_binding::{YulangMmtkScanning, YulangMmtkSlot};
        use mmtk::util::opaque_pointer::{VMThread, VMWorkerThread};
        use mmtk::vm::slot::Slot;
        use mmtk::vm::{Scanning, SlotVisitor};

        struct Slots(Vec<YulangMmtkSlot>);

        impl SlotVisitor<YulangMmtkSlot> for Slots {
            fn visit_slot(&mut self, slot: YulangMmtkSlot) {
                self.0.push(slot);
            }
        }

        let heap = MmtkHeap::new_no_gc().expect("NoGC MMTk heap should initialize");
        let mut context = GcRuntimeContext::with_heap(heap);
        let child = context.alloc_string("child");
        let tuple = context.alloc_tuple(vec![child, YValue::from_i63(7).unwrap()]);

        assert_eq!(context.heap().object_count(), 2);
        assert!(context.heap().object(tuple).is_some());

        let object_ref = context
            .heap()
            .object_reference(tuple)
            .expect("tuple should be backed by an MMTk object");
        let mut slots = Slots(Vec::new());
        YulangMmtkScanning::scan_object(
            VMWorkerThread(VMThread::UNINITIALIZED),
            object_ref,
            &mut slots,
        );

        assert_eq!(slots.0.len(), 2);
        assert_eq!(slots.0[0].load(), context.heap().object_reference(child));
        assert_eq!(slots.0[1].load(), None);

        let trace = context.heap().trace_roots(&[tuple]);
        assert_eq!(trace.len(), 2);
        assert_eq!(trace[0].value, tuple);
        assert_eq!(trace[1].value, child);
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_heap_supports_gc_runtime_surface_smoke() {
        let _guard = mmtk_test_lock();
        use crate::gc_runtime::{GcRuntimeContext, YObjectKind, YTraceOrigin, YValue};

        let heap = MmtkHeap::new_no_gc().expect("NoGC MMTk heap should initialize");
        let mut context = GcRuntimeContext::with_heap(heap);

        let orphan = context.alloc_string("orphan");
        let captured = context.alloc_string("captured");
        let closure = context.alloc_closure(7, vec![captured]);
        let tuple = context.alloc_tuple(vec![closure, YValue::UNIT]);
        context.root_stack_mut().push(tuple);

        assert_eq!(context.debug_value(orphan), "\"orphan\"");
        assert_eq!(context.debug_value(tuple), "(<closure code=7 env=1>, ())");

        let stats = context.heap_stats();
        assert_eq!(stats.allocated_objects, 4);
        assert_eq!(stats.allocated_trace_slots, 3);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::String], 2);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::Closure], 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::Tuple], 1);

        let trace = context.trace_roots();
        assert_eq!(
            trace
                .iter()
                .map(|edge| edge.object_kind)
                .collect::<Vec<_>>(),
            vec![
                YObjectKind::Tuple,
                YObjectKind::Closure,
                YObjectKind::String,
            ]
        );
        assert_eq!(trace[0].origin, YTraceOrigin::Root(0));
        assert_eq!(trace[1].origin, YTraceOrigin::Object(YObjectKind::Tuple));

        let report = context.trace_root_report();
        assert_eq!(report.root_count, 1);
        assert_eq!(report.live_objects, 3);
        assert_eq!(report.live_trace_slots, 3);
        assert_eq!(report.live_by_kind[&YObjectKind::String], 1);
        assert_eq!(report.live_by_kind[&YObjectKind::Closure], 1);
        assert_eq!(report.live_by_kind[&YObjectKind::Tuple], 1);
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_heap_supports_compact_raw_payload_objects() {
        let _guard = mmtk_test_lock();
        use crate::gc_runtime::{GcRuntimeContext, YHeap, YObjectKind, YValue};

        let heap = MmtkHeap::new_no_gc().expect("NoGC MMTk heap should initialize");
        let mut context = GcRuntimeContext::with_heap(heap);
        let child = context.alloc_string("child");
        let compact = context.heap_mut().allocate_raw_payload(
            YObjectKind::Tuple,
            &[child, YValue::from_i63(9).unwrap()],
            &[0xaa, 0xbb, 0xcc, 0xdd],
        );
        context.root_stack_mut().push(compact);

        assert!(context.object(compact).is_none());
        assert_eq!(
            context.heap().raw_payload_bytes(compact),
            Some(&[0xaa, 0xbb, 0xcc, 0xdd][..])
        );
        assert_eq!(
            context.heap().trace_children(compact),
            Some(vec![child, YValue::from_i63(9).unwrap()])
        );

        let stats = context.heap_stats();
        assert_eq!(stats.allocated_objects, 2);
        assert_eq!(stats.allocated_trace_slots, 2);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::String], 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::Tuple], 1);

        let trace = context.trace_roots();
        assert_eq!(
            trace
                .iter()
                .map(|edge| edge.object_kind)
                .collect::<Vec<_>>(),
            vec![YObjectKind::Tuple, YObjectKind::String]
        );
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_heap_supports_compact_native_heap_blocks() {
        let _guard = mmtk_test_lock();
        use crate::gc_runtime::{
            GcRuntimeContext, NativeFieldLane, NativeFieldLayout, NativeFieldValue,
            NativeHeapBlock, NativeLayout, YHeap, YObjectKind,
        };

        let heap = MmtkHeap::new_no_gc().expect("NoGC MMTk heap should initialize");
        let mut context = GcRuntimeContext::with_heap(heap);
        let label = context.alloc_string("label");
        let layout = context.intern_native_layout(NativeLayout::tuple(vec![
            NativeFieldLayout::named("index", NativeFieldLane::U64),
            NativeFieldLayout::named("label", NativeFieldLane::YValue),
        ]));
        let block = NativeHeapBlock::new(
            layout,
            vec![NativeFieldValue::U64(77), NativeFieldValue::YValue(label)],
        )
        .expect("native heap block should match layout");
        let compact = context.heap_mut().allocate_native_heap_block(&block);

        assert!(context.object(compact).is_none());
        assert_eq!(
            context.heap().raw_payload_bytes(compact),
            Some(block.payload().bytes())
        );
        assert_eq!(
            context.heap().native_field_value(compact, 0),
            Some(NativeFieldValue::U64(77))
        );
        assert_eq!(
            context.heap().native_field_value(compact, 1),
            Some(NativeFieldValue::YValue(label))
        );
        assert_eq!(context.heap().trace_children(compact), Some(vec![label]));

        let stats = context.heap_stats();
        assert_eq!(stats.allocated_objects, 2);
        assert_eq!(stats.allocated_trace_slots, 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::Tuple], 1);
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_heap_supports_compact_control_payloads() {
        let _guard = mmtk_test_lock();
        use crate::gc_runtime::{GcRuntimeContext, YHeap, YObjectKind};

        let heap = MmtkHeap::new_no_gc().expect("NoGC MMTk heap should initialize");
        let mut context = GcRuntimeContext::with_heap(heap);
        let captured = context.alloc_string("captured");
        let closure = context.heap_mut().allocate_compact_closure(11, &[captured]);
        let thunk = context.heap_mut().allocate_compact_thunk(12, &[captured]);
        let resumption = context
            .heap_mut()
            .allocate_compact_resumption(13, &[captured]);
        let continuation_env = context
            .heap_mut()
            .allocate_compact_continuation_env(&[captured]);
        let handler_frame = context
            .heap_mut()
            .allocate_compact_handler_frame(14, &[captured]);
        let return_frame = context
            .heap_mut()
            .allocate_compact_return_frame(15, &[captured]);
        context.root_stack_mut().push(return_frame);

        for (value, kind, word) in [
            (closure, YObjectKind::Closure, Some(11)),
            (thunk, YObjectKind::Thunk, Some(12)),
            (resumption, YObjectKind::Resumption, Some(13)),
            (continuation_env, YObjectKind::ContinuationEnv, None),
            (handler_frame, YObjectKind::HandlerFrame, Some(14)),
            (return_frame, YObjectKind::ReturnFrame, Some(15)),
        ] {
            assert!(context.object(value).is_none());
            assert_eq!(
                context.heap().object_header(value).map(|h| h.kind),
                Some(kind)
            );
            assert_eq!(context.heap().compact_control_word(value), word);
            assert_eq!(
                context.heap().compact_env_slots(value),
                Some(vec![captured])
            );
            assert_eq!(context.heap().trace_children(value), Some(vec![captured]));
        }

        assert_eq!(context.heap().native_field_name(closure, 0), Some("code"));
        assert_eq!(
            context.heap().native_field_name(handler_frame, 0),
            Some("prompt")
        );
        assert_eq!(
            context.heap().native_field_name(return_frame, 0),
            Some("continuation")
        );

        let stats = context.heap_stats();
        assert_eq!(stats.allocated_objects, 7);
        assert_eq!(stats.allocated_trace_slots, 6);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::String], 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::Closure], 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::Thunk], 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::Resumption], 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::ContinuationEnv], 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::HandlerFrame], 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::ReturnFrame], 1);

        let trace = context.trace_roots();
        assert_eq!(
            trace
                .iter()
                .map(|edge| edge.object_kind)
                .collect::<Vec<_>>(),
            vec![YObjectKind::ReturnFrame, YObjectKind::String]
        );
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_heap_supports_rope_nodes_and_temporary_roots() {
        let _guard = mmtk_test_lock();
        use crate::gc_runtime::{GcRuntimeContext, YObjectKind, YValue};

        let heap = MmtkHeap::new_no_gc().expect("NoGC MMTk heap should initialize");
        let mut context = GcRuntimeContext::with_heap(heap);
        context.enable_collect_every_allocation();

        let left = context.alloc_string("hel");
        let right = context.alloc_string("lo");
        let concat = context.alloc_string_concat(left, right);
        let slice = context.alloc_string_slice(concat, 1, 4);
        context.root_stack_mut().push(slice);

        assert_eq!(context.debug_value(concat), "\"hello\"");
        assert_eq!(context.debug_value(slice), "\"ell\"");
        assert_eq!(
            context
                .trace_roots()
                .iter()
                .map(|edge| edge.object_kind)
                .collect::<Vec<_>>(),
            vec![
                YObjectKind::String,
                YObjectKind::String,
                YObjectKind::String,
                YObjectKind::String,
            ]
        );

        let rendered = context.with_temporary_roots([concat], |context, roots| {
            let captured = context.root_stack().get(roots[0]);
            let list = context.alloc_list(vec![captured, YValue::from_i63(2).unwrap()]);
            context.debug_value(list)
        });

        assert_eq!(rendered, "[\"hello\", 2]");
        assert_eq!(context.root_stack().values(), &[slice]);
        assert_eq!(context.stress_collection_count(), 5);
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_native_runtime_context_builds_small_language_values() {
        let _guard = mmtk_test_lock();
        let mut runtime =
            MmtkNativeRuntimeContext::new_no_gc().expect("NoGC runtime should initialize");

        let hello = runtime.make_string(b"hello").expect("string");
        let forty_two = runtime.make_int_text(b"42").expect("int");
        let tuple = runtime.tuple_empty();
        let tuple = runtime.tuple_push(tuple, hello).unwrap();
        let tuple = runtime.tuple_push(tuple, forty_two).unwrap();
        let left = runtime.list_singleton(hello);
        let right = runtime.list_singleton(forty_two);
        let list = runtime.list_merge(left, right).unwrap();
        let list_tail = runtime.list_slice(list, 1, 2).unwrap();
        let greeting = runtime.make_string(b", world").expect("string");
        let greeting = runtime.string_concat(hello, greeting).unwrap();
        let record = runtime.record_empty();
        let record = runtime.record_insert(record, b"name", greeting).unwrap();
        let record = runtime.record_insert(record, b"answer", forty_two).unwrap();
        let variant = runtime.variant(b"some", Some(record)).unwrap();
        let sum = runtime.int_add(forty_two, forty_two).unwrap();
        let world = runtime.string_slice(greeting, 7, 12).unwrap();
        let i = runtime.make_string(b"i").expect("string");
        let hio = runtime.string_splice(hello, 1, 4, i).unwrap();
        let hello_bytes = runtime.string_to_bytes(hello).unwrap();
        let hello_bang_bytes = runtime.string_to_bytes(greeting).unwrap();
        let bytes_joined = runtime.bytes_concat(hello_bytes, hello_bang_bytes).unwrap();
        let bytes_tail = runtime.bytes_slice(hello_bang_bytes, 5, 12).unwrap();
        let utf8_raw = runtime.bytes_to_utf8_raw(hello_bang_bytes).unwrap();
        let path = runtime.bytes_to_path(hello_bytes).unwrap();
        let path_bytes = runtime.path_to_bytes(path).unwrap();
        let inserted = runtime.list_singleton(greeting);
        let list_spliced = runtime.list_splice(list, 1, 2, inserted).unwrap();
        let record_without_answer = runtime.record_without_field(record, b"answer").unwrap();

        assert!(runtime.context().object(hello).is_none());
        assert_eq!(
            runtime.context().heap().raw_payload_bytes(hello),
            Some(&b"hello"[..])
        );
        assert!(runtime.context().object(tuple).is_none());
        assert_eq!(runtime.context().heap().native_field_count(tuple), Some(2));
        assert_eq!(runtime.tuple_get(tuple, 0), Some(hello));
        assert_eq!(runtime.tuple_get(tuple, 1), Some(forty_two));
        assert_eq!(runtime.string_byte_len(greeting), Some(12));
        assert!(runtime.string_red_black_status(greeting).is_some());
        assert_eq!(runtime.string_eq(hello, greeting), Some(false));
        assert_eq!(runtime.debug_value(world), "\"world\"");
        assert_eq!(runtime.debug_value(hio), "\"hio\"");
        assert_eq!(runtime.bytes_len(hello_bytes), Some(5));
        assert_eq!(runtime.bytes_eq(hello_bytes, path_bytes), Some(true));
        assert_eq!(runtime.bytes_get(hello_bytes, 1), Some(b'e'));
        assert_eq!(runtime.bytes_len(bytes_joined), Some(17));
        assert_eq!(runtime.debug_value(bytes_tail), "<bytes len=7>");
        assert_eq!(runtime.debug_value(path), "hello");
        let utf8_text = runtime.tuple_get(utf8_raw, 0).unwrap();
        assert_eq!(runtime.string_eq(utf8_text, greeting), Some(true));
        assert_eq!(runtime.tuple_get(utf8_raw, 1), YValue::from_i63(12));
        assert!(runtime.context().object(list).is_none());
        assert_eq!(
            runtime.context().heap().trace_children(list),
            Some(vec![hello, forty_two])
        );
        assert_eq!(runtime.list_len(list), Some(2));
        assert!(runtime.list_red_black_status(list).is_some());
        assert_eq!(runtime.list_get(list, 1), Some(forty_two));
        assert!(runtime.context().object(list_tail).is_none());
        assert_eq!(runtime.debug_value(list_tail), "[42]");
        assert_eq!(
            runtime.debug_value(list_spliced),
            "[\"hello\", \"hello, world\"]"
        );
        assert!(runtime.list_red_black_status(list_spliced).is_some());
        assert!(runtime.context().object(record).is_none());
        assert_eq!(runtime.context().heap().native_field_count(record), Some(2));
        assert_eq!(runtime.record_has_field(record, b"name"), Some(true));
        assert_eq!(runtime.record_has_field(record, b"missing"), Some(false));
        assert_eq!(runtime.record_get(record, b"name"), Some(greeting));
        assert_eq!(runtime.record_get(record, b"answer"), Some(forty_two));
        assert_eq!(
            runtime.record_get_or_default(record, b"missing", hello),
            Some(hello)
        );
        assert_eq!(runtime.record_get(record_without_answer, b"answer"), None);
        assert!(runtime.context().object(variant).is_none());
        assert_eq!(
            runtime.context().heap().native_field_count(variant),
            Some(2)
        );
        assert_eq!(runtime.variant_tag_eq(variant, b"some"), Some(true));
        assert_eq!(runtime.variant_payload(variant), Some(record));
        assert_eq!(runtime.debug_value(sum), "84");
        assert_eq!(runtime.debug_value(tuple), "(\"hello\", 42)");
        assert_eq!(runtime.debug_value(list), "[\"hello\", 42]");
        assert_eq!(runtime.context().heap_stats().allocated_objects, 38);
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_native_runtime_context_keeps_string_and_list_trees_balanced() {
        let _guard = mmtk_test_lock();
        let mut runtime =
            MmtkNativeRuntimeContext::new_no_gc().expect("NoGC runtime should initialize");

        let mut text = runtime.make_string(b"").expect("empty string");
        for _ in 0..160 {
            let chunk = runtime.make_string("あ".as_bytes()).expect("string chunk");
            text = runtime.string_concat(text, chunk).expect("concat string");
            assert!(runtime.string_red_black_status(text).is_some());
        }
        assert_eq!(runtime.string_len(text), Some(160));
        assert_eq!(runtime.string_byte_len(text), Some(480));
        let middle = runtime.string_slice(text, 70, 75).expect("string slice");
        assert!(runtime.string_red_black_status(middle).is_some());
        assert_eq!(runtime.string_len(middle), Some(5));

        let mut list = runtime.list_empty();
        for index in 0..160 {
            let value = YValue::from_i63(index).expect("small int");
            let singleton = runtime.list_singleton(value);
            list = runtime.list_merge(list, singleton).expect("concat list");
            assert!(runtime.list_red_black_status(list).is_some());
        }
        assert_eq!(runtime.list_len(list), Some(160));
        assert_eq!(runtime.list_get(list, 65), YValue::from_i63(65));
        let slice = runtime.list_slice(list, 70, 75).expect("list slice");
        assert!(runtime.list_red_black_status(slice).is_some());
        assert_eq!(
            runtime.list_items(slice),
            Some(
                (70..75)
                    .map(|value| YValue::from_i63(value).unwrap())
                    .collect()
            )
        );
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_native_runtime_c_abi_roundtrips_yvalue_words() {
        let _guard = mmtk_test_lock();
        let runtime = yulang_mmtk_native_context_new();
        assert!(!runtime.is_null());

        let hello = yulang_mmtk_native_make_string(runtime, b"hello".as_ptr(), 5);
        let one = yulang_mmtk_native_make_int(runtime, b"1".as_ptr(), 1);
        let two = yulang_mmtk_native_make_int(runtime, b"2".as_ptr(), 1);
        let tuple = yulang_mmtk_native_tuple_empty(runtime);
        let tuple = yulang_mmtk_native_tuple_push(runtime, tuple, hello);
        let tuple = yulang_mmtk_native_tuple_push(runtime, tuple, one);
        let hello_bang = yulang_mmtk_native_make_string(runtime, b"!".as_ptr(), 1);
        let hello_bang = yulang_mmtk_native_string_concat(runtime, hello, hello_bang);
        let record = yulang_mmtk_native_record_empty(runtime);
        let record =
            yulang_mmtk_native_record_insert(runtime, record, b"greeting".as_ptr(), 8, hello_bang);
        let record = yulang_mmtk_native_record_insert(runtime, record, b"count".as_ptr(), 5, two);
        let variant = yulang_mmtk_native_variant(runtime, b"some".as_ptr(), 4, 1, record);
        let list = yulang_mmtk_native_list_singleton(runtime, one);
        let list = yulang_mmtk_native_list_merge(
            runtime,
            list,
            yulang_mmtk_native_list_singleton(runtime, two),
        );
        let sliced = yulang_mmtk_native_string_slice(runtime, hello_bang, 0, 5);
        let insert = yulang_mmtk_native_make_string(runtime, b"i".as_ptr(), 1);
        let spliced = yulang_mmtk_native_string_splice(runtime, hello, 1, 4, insert);
        let list_spliced = yulang_mmtk_native_list_splice(
            runtime,
            list,
            1,
            2,
            yulang_mmtk_native_list_singleton(runtime, hello),
        );
        let record_without_count =
            yulang_mmtk_native_record_without_field(runtime, record, b"count".as_ptr(), 5);
        let sum = yulang_mmtk_native_int_add(runtime, one, two);

        assert_ne!(hello, 0);
        assert_ne!(tuple, 0);
        assert_eq!(yulang_mmtk_native_tuple_get(runtime, tuple, 0), hello);
        assert_eq!(yulang_mmtk_native_tuple_get(runtime, tuple, 1), one);
        assert_eq!(yulang_mmtk_native_string_byte_len(runtime, hello_bang), 6);
        assert_eq!(yulang_mmtk_native_string_eq(runtime, hello, hello_bang), 0);
        assert_eq!(yulang_mmtk_native_string_eq(runtime, sliced, hello), 1);
        assert_eq!(
            yulang_mmtk_native_record_get(runtime, record, b"greeting".as_ptr(), 8),
            hello_bang
        );
        assert_eq!(
            yulang_mmtk_native_record_has_field(runtime, record, b"count".as_ptr(), 5),
            1
        );
        assert_eq!(
            yulang_mmtk_native_record_get_or_default(runtime, record, b"missing".as_ptr(), 7, one,),
            one
        );
        assert_eq!(
            yulang_mmtk_native_record_has_field(
                runtime,
                record_without_count,
                b"count".as_ptr(),
                5,
            ),
            0
        );
        assert_eq!(
            yulang_mmtk_native_variant_tag_eq(runtime, variant, b"some".as_ptr(), 4),
            1
        );
        assert_eq!(yulang_mmtk_native_variant_payload(runtime, variant), record);
        assert_eq!(yulang_mmtk_native_list_len(runtime, list), 2);
        assert_eq!(yulang_mmtk_native_list_get(runtime, list, 1), two);
        assert_eq!(yulang_mmtk_native_list_len(runtime, list_spliced), 2);
        assert_eq!(yulang_mmtk_native_int_compare(runtime, sum, two), 1);

        let runtime_ref = unsafe { runtime.as_ref() }.expect("runtime");
        assert_eq!(
            runtime_ref.debug_value(decode_yvalue(tuple)),
            "(\"hello\", 1)"
        );
        assert_eq!(runtime_ref.debug_value(decode_yvalue(spliced)), "\"hio\"");
        assert_eq!(runtime_ref.debug_value(decode_yvalue(sum)), "3");

        yulang_mmtk_native_context_free(runtime);
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_cps_yvalue_lane_helpers_are_contextless_symbols() {
        let _guard = mmtk_test_lock();
        yulang_mmtk_cps_reset_i64();

        let hello = yulang_mmtk_cps_string_literal_i64(b"hello".as_ptr(), 5);
        let bang = yulang_mmtk_cps_string_literal_i64(b"!".as_ptr(), 1);
        let hello_bang = yulang_mmtk_cps_string_concat_i64(hello, bang);
        let one = yulang_mmtk_cps_make_int_i64(b"1".as_ptr(), 1);
        let two = yulang_mmtk_cps_make_int_i64(b"2".as_ptr(), 1);
        let three = yulang_mmtk_cps_int_add_i64(one, two);
        let tuple = yulang_mmtk_cps_tuple_i64_2(hello, one);
        let record = yulang_mmtk_cps_record_empty_i64();
        let record = yulang_mmtk_cps_record_insert_i64(record, b"greeting".as_ptr(), 8, hello_bang);
        let record = yulang_mmtk_cps_record_insert_i64(record, b"count".as_ptr(), 5, three);
        let record_without_count =
            yulang_mmtk_cps_record_without_field_i64(record, b"count".as_ptr(), 5);
        let _ = yulang_mmtk_cps_register_tag_i64(7, b"some".as_ptr(), 4);
        let variant = yulang_mmtk_cps_variant_i64_1(7, record_without_count);
        let list = yulang_mmtk_cps_list_merge_i64(
            yulang_mmtk_cps_list_singleton_i64(hello),
            yulang_mmtk_cps_list_singleton_i64(one),
        );
        let list = yulang_mmtk_cps_list_splice_i64(
            list,
            one,
            two,
            yulang_mmtk_cps_list_singleton_i64(hello_bang),
        );
        let list_head = yulang_mmtk_cps_list_slice_i64(list, encoded_i63(0), one);
        let hello_head =
            yulang_mmtk_cps_string_slice_i64(hello_bang, encoded_i63(0), encoded_i63(5));
        let hio_insert = yulang_mmtk_cps_string_literal_i64(b"i".as_ptr(), 1);
        let hio = yulang_mmtk_cps_string_splice_i64(hello, one, encoded_i63(4), hio_insert);
        let hello_bytes = yulang_mmtk_cps_string_to_bytes_i64(hello);
        let hello_bang_bytes = yulang_mmtk_cps_string_to_bytes_i64(hello_bang);
        let bytes_joined = yulang_mmtk_cps_bytes_concat_i64(hello_bytes, hello_bang_bytes);
        let bytes_tail =
            yulang_mmtk_cps_bytes_slice_i64(hello_bang_bytes, encoded_i63(5), encoded_i63(6));
        let utf8_raw = yulang_mmtk_cps_bytes_to_utf8_raw_i64(hello_bang_bytes);
        let path = yulang_mmtk_cps_bytes_to_path_i64(hello_bytes);
        let path_bytes = yulang_mmtk_cps_path_to_bytes_i64(path);

        assert_ne!(hello, 0);
        let mixed = yulang_mmtk_cps_string_literal_i64("aあ🙂".as_ptr(), "aあ🙂".len() as i64);
        assert_eq!(yulang_mmtk_cps_string_len_i64(mixed), encoded_i63(3));
        assert_eq!(yulang_mmtk_cps_string_len_i64(hello_bang), encoded_i63(6));
        assert_eq!(
            yulang_mmtk_cps_string_eq_i64(hello, hello_bang),
            encoded_bool(false)
        );
        assert_eq!(
            yulang_mmtk_cps_string_eq_i64(hello, hello_head),
            encoded_bool(true)
        );
        assert_eq!(yulang_mmtk_cps_tuple_get_i64(tuple, 1), one);
        assert_eq!(
            yulang_mmtk_cps_record_select_i64(record, b"greeting".as_ptr(), 8),
            hello_bang
        );
        assert_eq!(
            yulang_mmtk_cps_record_select_or_default_i64(record, b"missing".as_ptr(), 7, one),
            one
        );
        assert_eq!(
            yulang_mmtk_cps_record_has_field_i64(record, b"count".as_ptr(), 5),
            encoded_bool(true)
        );
        assert_eq!(
            yulang_mmtk_cps_record_has_field_i64(record_without_count, b"count".as_ptr(), 5),
            encoded_bool(false)
        );
        assert_eq!(
            yulang_mmtk_cps_variant_tag_eq_i64(variant, 7),
            encoded_bool(true)
        );
        assert_eq!(
            yulang_mmtk_cps_variant_payload_i64(variant),
            record_without_count
        );
        assert_eq!(yulang_mmtk_cps_list_len_i64(list), encoded_i63(2));
        assert_eq!(yulang_mmtk_cps_list_index_i64(list, encoded_i63(0)), hello);
        assert_eq!(yulang_mmtk_cps_list_len_i64(list_head), one);
        assert_eq!(yulang_mmtk_cps_int_sub_i64(three, two), one);
        assert_eq!(yulang_mmtk_cps_int_mul_i64(one, two), two);
        assert_eq!(yulang_mmtk_cps_int_gt_i64(three, two), encoded_bool(true));
        assert_eq!(yulang_mmtk_cps_bytes_len_i64(hello_bytes), encoded_i63(5));
        assert_eq!(yulang_mmtk_cps_bytes_len_i64(bytes_joined), encoded_i63(11));
        assert_eq!(
            yulang_mmtk_cps_bytes_index_i64(hello_bytes, one),
            encoded_i63(i64::from(b'e'))
        );
        assert_eq!(yulang_mmtk_cps_bytes_len_i64(bytes_tail), one);
        assert_eq!(
            yulang_mmtk_cps_bytes_eq_i64(hello_bytes, path_bytes),
            encoded_bool(true)
        );

        let utf8_text = yulang_mmtk_cps_tuple_get_i64(utf8_raw, 0);
        let rendered = with_mmtk_cps_context(|context| {
            (
                context.debug_value(decode_yvalue(tuple)),
                context.debug_value(decode_yvalue(list)),
                context.debug_value(decode_yvalue(hio)),
                context.debug_value(decode_yvalue(bytes_tail)),
                context.debug_value(decode_yvalue(path)),
                context.string_eq(decode_yvalue(utf8_text), decode_yvalue(hello_bang)),
            )
        })
        .expect("MMTk CPS context should exist after helper calls");
        assert_eq!(rendered.0, "(\"hello\", 1)");
        assert_eq!(rendered.1, "[\"hello\", \"hello!\"]");
        assert_eq!(rendered.2, "\"hio\"");
        assert_eq!(rendered.3, "<bytes len=1>");
        assert_eq!(rendered.4, "hello");
        assert_eq!(rendered.5, Some(true));
    }

    #[cfg(feature = "mmtk-runtime")]
    #[test]
    fn mmtk_cps_yvalue_lane_symbols_can_be_called_from_jit() {
        use cranelift_codegen::ir::{AbiParam, InstBuilder, types};
        use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
        use cranelift_jit::{JITBuilder, JITModule};
        use cranelift_module::{Linkage, Module};

        let _guard = mmtk_test_lock();
        static HELLO: &[u8] = b"hello";

        let mut jit_builder =
            JITBuilder::new(cranelift_module::default_libcall_names()).expect("JIT builder");
        register_mmtk_cps_jit_symbols(&mut jit_builder);
        let mut module = JITModule::new(jit_builder);

        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));
        let root = module
            .declare_function("mmtk_yvalue_lane_smoke", Linkage::Export, &sig)
            .expect("declare smoke root");

        let mut ctx = module.make_context();
        ctx.func.signature = sig;

        let mut builder_context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
        let block = builder.create_block();
        builder.switch_to_block(block);

        let reset = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_cps_reset_i64",
            &[],
            &[],
        );
        let string_literal = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_cps_string_literal_i64",
            &[types::I64, types::I64],
            &[types::I64],
        );
        let string_len = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_cps_string_len_i64",
            &[types::I64],
            &[types::I64],
        );
        let string_to_bytes = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_cps_string_to_bytes_i64",
            &[types::I64],
            &[types::I64],
        );
        let bytes_len = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_cps_bytes_len_i64",
            &[types::I64],
            &[types::I64],
        );
        let tuple_i64_2 = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_cps_tuple_i64_2",
            &[types::I64, types::I64],
            &[types::I64],
        );
        let tuple_get = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_cps_tuple_get_i64",
            &[types::I64, types::I64],
            &[types::I64],
        );
        let int_add = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_cps_int_add_i64",
            &[types::I64, types::I64],
            &[types::I64],
        );

        builder.ins().call(reset, &[]);

        let ptr = builder.ins().iconst(types::I64, HELLO.as_ptr() as i64);
        let len = builder.ins().iconst(types::I64, HELLO.len() as i64);
        let hello = call_jit_i64(&mut builder, string_literal, &[ptr, len]);
        let bytes = call_jit_i64(&mut builder, string_to_bytes, &[hello]);
        let tuple = call_jit_i64(&mut builder, tuple_i64_2, &[hello, bytes]);
        let zero = builder.ins().iconst(types::I64, 0);
        let tuple_hello = call_jit_i64(&mut builder, tuple_get, &[tuple, zero]);
        let tuple_bytes = call_jit_i64(&mut builder, string_to_bytes, &[tuple_hello]);
        let tuple_bytes_len = call_jit_i64(&mut builder, bytes_len, &[tuple_bytes]);
        let direct_len = call_jit_i64(&mut builder, string_len, &[hello]);
        let total = call_jit_i64(&mut builder, int_add, &[tuple_bytes_len, direct_len]);
        builder.ins().return_(&[total]);
        builder.seal_all_blocks();
        builder.finalize();

        module
            .define_function(root, &mut ctx)
            .expect("define smoke root");
        module.clear_context(&mut ctx);
        module.finalize_definitions().expect("finalize JIT module");

        let ptr = module.get_finalized_function(root);
        let run = unsafe { std::mem::transmute::<_, extern "C" fn() -> i64>(ptr) };

        assert_eq!(run(), encoded_i63(10));
    }
}
