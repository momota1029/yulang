//! MMTk runtime integration boundary.
//!
//! This module is intentionally thin. The GC runtime object model is still in
//! `gc_runtime`; this file records the MMTk plan/options surface that will back
//! that heap once the VM binding and object model callbacks are implemented.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;

use mmtk::plan::AllocationSemantics;
use mmtk::util::ObjectReference;
use mmtk::util::opaque_pointer::{VMMutatorThread, VMThread};
use rustc_hash::FxHashMap;

use crate::gc_runtime::{
    GcRuntimeContext, NativeFieldValue, NativeHeapBlock, NativeLayoutHandle, NativePayloadBuffer,
    YHeap, YHeapStats, YList, YObject, YObjectKind, YObjectPayload, YString, YSymbolId, YValue,
};
use crate::mmtk_binding::{YulangMmtkObjectHeader, YulangMmtkVM, initialize_yulang_mmtk_object};

unsafe extern "C" {
    fn yulang_cps_print_debug_i64(value: i64);
}

const MAX_STRING_LEAF_CHARS: usize = yulang_runtime::runtime::string_tree::MAX_LEAF_CHARS;

const MAX_LIST_LEAF_ITEMS: usize = 64;
const COMPACT_STRING_NODE_TAG: u8 = 1;
const COMPACT_LIST_NODE_TAG: u8 = 2;
const COMPACT_CONTROL_STACK_TAG: u8 = 3;
const COMPACT_CONTROL_BLOCK_TAG: u8 = 4;
const COMPACT_TUPLE_TAG: u8 = 5;
const COMPACT_VARIANT_TAG: u8 = 6;
const COMPACT_RECORD_TAG: u8 = 7;
const GC_CONTROL_STATE_TAG: u8 = 8;
const GC_CONTROL_THUNK_TAG: u8 = 9;
const GC_CONTROL_GUARD_STACK_TAG: u8 = 10;
const GC_CONTROL_STATE_FIELD_COUNT: usize = 4;
const GC_CONTROL_STATE_PAYLOAD_SIZE: usize = 8 + GC_CONTROL_STATE_FIELD_COUNT * 8;
const GC_CONTROL_THUNK_HEADER_SIZE: usize = 32;
const GC_CONTROL_GUARD_STACK_PAYLOAD_SIZE: usize = 24;
const COMPACT_NODE_HEADER_SIZE: usize = 2;
const COMPACT_CONTROL_HEADER_SIZE: usize = 16;
const COMPACT_VARIANT_HEADER_SIZE: usize = 6;
const COMPACT_RECORD_HEADER_SIZE: usize = 5;

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
    pub fn builder(&self) -> Result<mmtk::MMTKBuilder, MmtkConfigError> {
        let mut builder = mmtk::MMTKBuilder::new_no_env_vars();
        self.config.configure_builder(&mut builder)?;
        Ok(builder)
    }
    pub fn build_yulang_mmtk(
        &self,
    ) -> Result<mmtk::MMTK<crate::mmtk_binding::YulangMmtkVM>, MmtkConfigError> {
        Ok(self.builder()?.build::<crate::mmtk_binding::YulangMmtkVM>())
    }
}

pub struct MmtkHeap {
    _mmtk: &'static mmtk::MMTK<YulangMmtkVM>,
    mutator: Box<mmtk::Mutator<YulangMmtkVM>>,
    objects: FxHashMap<usize, MmtkPayloadStorage>,
    allocation_profile: MmtkAllocationProfile,
    min_object_raw: usize,
    max_object_raw: usize,
}

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
            objects: FxHashMap::default(),
            allocation_profile: MmtkAllocationProfile::default(),
            min_object_raw: usize::MAX,
            max_object_raw: 0,
        })
    }

    pub fn object_reference(&self, value: YValue) -> Option<ObjectReference> {
        value
            .heap_reference_raw()
            .and_then(|raw| ObjectReference::from_raw_address(raw_address(raw)))
    }

    pub fn object_count(&self) -> usize {
        self.objects.len()
    }

    pub fn allocation_profile(&self) -> &MmtkAllocationProfile {
        &self.allocation_profile
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
        let raw_payload = encode_compact_string_node_payload(color, len_chars, len_bytes);
        self.allocate_raw_payload_with_storage(
            YObjectKind::String,
            &[left, right],
            &raw_payload,
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
        let raw_payload = encode_compact_list_node_payload(color, len);
        self.allocate_raw_payload_with_storage(
            YObjectKind::List,
            &[left, right],
            &raw_payload,
            MmtkPayloadStorage::ListNode { color, len },
        )
    }

    fn allocate_compact_tuple(&mut self, items: &[YValue]) -> YValue {
        self.allocate_raw_payload_with_storage(
            YObjectKind::Tuple,
            items,
            &[COMPACT_TUPLE_TAG],
            MmtkPayloadStorage::RawBytes,
        )
    }

    fn allocate_compact_variant(&mut self, tag: YSymbolId, value: Option<YValue>) -> YValue {
        let raw_payload = encode_compact_variant_payload(tag, value.is_some());
        let trace_slots = value.into_iter().collect::<Vec<_>>();
        self.allocate_raw_payload_with_storage(
            YObjectKind::Variant,
            &trace_slots,
            &raw_payload,
            MmtkPayloadStorage::RawBytes,
        )
    }

    fn allocate_compact_record(&mut self, fields: &[(Box<str>, YValue)]) -> YValue {
        let raw_payload = encode_compact_record_payload(fields);
        let trace_slots = fields.iter().map(|(_, value)| *value).collect::<Vec<_>>();
        self.allocate_raw_payload_with_storage(
            YObjectKind::Record,
            &trace_slots,
            &raw_payload,
            MmtkPayloadStorage::RawBytes,
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
        NativePayloadBuffer::read_field_from_bytes(
            layout.layout(),
            index,
            self.raw_payload_bytes(value)?,
        )
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
        match self.objects.get(&raw)? {
            MmtkPayloadStorage::NativeBlock { layout } => {
                layout.layout().fields.get(index)?.name.as_deref()
            }
            MmtkPayloadStorage::ControlBlock {
                head_name: Some(name),
                ..
            } if index == 0 => Some(name),
            _ => None,
        }
    }

    pub fn allocate_compact_closure(&mut self, code: usize, env: &[YValue]) -> YValue {
        self.allocate_compact_control_block(
            YObjectKind::Closure,
            Some(("code", NativeFieldValue::U64(code as u64))),
            env,
        )
    }

    pub(crate) fn allocate_compact_closure_i64(&mut self, code: usize, env: &[i64]) -> YValue {
        self.allocate_compact_control_block_i64(
            YObjectKind::Closure,
            Some(("code", code as u64)),
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

    pub(crate) fn allocate_compact_thunk_i64(&mut self, code: usize, env: &[i64]) -> YValue {
        self.allocate_compact_control_block_i64(
            YObjectKind::Thunk,
            Some(("code", code as u64)),
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

    pub(crate) fn allocate_compact_resumption_i64(&mut self, code: usize, env: &[i64]) -> YValue {
        self.allocate_compact_control_block_i64(
            YObjectKind::Resumption,
            Some(("code", code as u64)),
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

    pub fn allocate_compact_control_stack_snapshot(
        &mut self,
        item_count: usize,
        raw_trace_words: &[i64],
    ) -> YValue {
        self.allocate_compact_control_stack_chunk(item_count, None, raw_trace_words)
    }

    pub fn allocate_compact_control_stack_chunk(
        &mut self,
        item_count: usize,
        parent: Option<YValue>,
        raw_trace_words: &[i64],
    ) -> YValue {
        let trace_slots = self.control_stack_trace_slots(parent, raw_trace_words);
        self.allocate_compact_control_stack_chunk_with_trace_slots(
            item_count,
            parent.is_some(),
            raw_trace_words,
            &trace_slots,
        )
    }

    fn control_stack_trace_slots(
        &self,
        parent: Option<YValue>,
        raw_trace_words: &[i64],
    ) -> Vec<YValue> {
        let mut trace_slots =
            Vec::with_capacity(raw_trace_words.len() + usize::from(parent.is_some()));
        if let Some(parent) = parent {
            trace_slots.push(parent);
        }
        trace_slots.extend(self.mmtk_trace_slots_from_raw_words(raw_trace_words));
        trace_slots
    }

    fn allocate_compact_control_stack_chunk_with_trace_slots(
        &mut self,
        item_count: usize,
        has_parent: bool,
        raw_trace_words: &[i64],
        trace_slots: &[YValue],
    ) -> YValue {
        let raw_payload =
            encode_compact_control_stack_payload(item_count, raw_trace_words.len(), has_parent);
        self.allocate_raw_payload_with_storage(
            YObjectKind::ControlStack,
            trace_slots,
            &raw_payload,
            MmtkPayloadStorage::ControlStack {
                item_count,
                raw_trace_word_count: raw_trace_words.len(),
                has_parent,
            },
        )
    }

    pub fn compact_control_word(&self, value: YValue) -> Option<u64> {
        let object = self.mmtk_object_reference(value)?;
        if !compact_control_kind_has_head(Self::object_header_from_ref(object).kind) {
            return None;
        };
        let bytes = self.raw_payload_bytes_from_ref(object);
        let (_, _, word) = decode_compact_control_payload_header(bytes)?;
        Some(word?)
    }

    pub fn compact_env_slots(&self, value: YValue) -> Option<Vec<YValue>> {
        let object = self.mmtk_object_reference(value)?;
        let bytes = self.raw_payload_bytes_from_ref(object);
        let (env_len, has_head, _) = decode_compact_control_payload_header(bytes)?;
        let start = COMPACT_CONTROL_HEADER_SIZE + usize::from(has_head) * 8;
        let words = bytes.get(start..start + env_len * 8)?;
        let mut slots = Vec::with_capacity(env_len);
        for chunk in words.chunks_exact(8) {
            slots.push(YValue::from_raw(
                u64::from_ne_bytes(chunk.try_into().ok()?) as usize
            ));
        }
        Some(slots)
    }

    pub(crate) fn compact_control_entry_parts(
        &self,
        value: YValue,
        expected_kind: YObjectKind,
    ) -> Option<(u64, *const i64)> {
        let object = self.mmtk_object_reference(value)?;
        let header = Self::object_header_from_ref(object);
        if header.kind != expected_kind || !compact_control_kind_has_head(header.kind) {
            return None;
        }
        let bytes = self.raw_payload_bytes_from_ref(object);
        let (env_len, has_head, code) = decode_compact_control_payload_header(bytes)?;
        debug_assert!(has_head);
        let code = code?;
        let start = COMPACT_CONTROL_HEADER_SIZE + 8;
        let _ = bytes.get(start..start + env_len * 8)?;
        let env_ptr = unsafe { bytes.as_ptr().add(start).cast::<i64>() };
        Some((code, env_ptr))
    }

    pub(crate) fn compact_control_env_len(&self, value: YValue) -> Option<usize> {
        let object = self.mmtk_object_reference(value)?;
        let bytes = self.raw_payload_bytes_from_ref(object);
        let (env_len, _, _) = decode_compact_control_payload_header(bytes)?;
        Some(env_len)
    }

    pub(crate) fn is_tracked_object_kind(&self, value: YValue, expected_kind: YObjectKind) -> bool {
        self.mmtk_object_reference(value)
            .is_some_and(|object| Self::object_header_from_ref(object).kind == expected_kind)
    }

    pub fn allocate_gc_control_state(&mut self, parts: GcControlStateParts) -> YValue {
        let fields = [
            parts.handler_stack,
            parts.guard_stack,
            parts.return_frames,
            parts.active_blocked,
        ];
        let mut raw_payload = Vec::with_capacity(GC_CONTROL_STATE_PAYLOAD_SIZE);
        raw_payload.push(GC_CONTROL_STATE_TAG);
        raw_payload.resize(8, 0);
        for field in fields {
            raw_payload.extend_from_slice(&(field.raw() as u64).to_ne_bytes());
        }
        let trace_slots = fields
            .into_iter()
            .filter(|value| {
                value
                    .heap_reference_raw()
                    .is_some_and(|raw| self.objects.contains_key(&raw))
            })
            .collect::<Vec<_>>();
        self.allocate_raw_payload_with_storage(
            YObjectKind::ControlState,
            &trace_slots,
            &raw_payload,
            MmtkPayloadStorage::GcControlState,
        )
    }

    pub fn gc_control_state_parts(&self, value: YValue) -> Option<GcControlStateParts> {
        let object = self.mmtk_object_reference(value)?;
        let header = Self::object_header_from_ref(object);
        if header.kind != YObjectKind::ControlState {
            return None;
        }
        decode_gc_control_state_payload(self.raw_payload_bytes_from_ref(object))
    }

    pub fn allocate_gc_control_thunk_i64(
        &mut self,
        code: usize,
        context: YValue,
        env: &[i64],
    ) -> YValue {
        let mut raw_payload = Vec::with_capacity(GC_CONTROL_THUNK_HEADER_SIZE + env.len() * 8);
        raw_payload.push(GC_CONTROL_THUNK_TAG);
        raw_payload.resize(8, 0);
        raw_payload.extend_from_slice(&(env.len() as u64).to_ne_bytes());
        raw_payload.extend_from_slice(&(code as u64).to_ne_bytes());
        raw_payload.extend_from_slice(&(context.raw() as u64).to_ne_bytes());
        for slot in env {
            raw_payload.extend_from_slice(&(*slot as u64).to_ne_bytes());
        }
        let mut trace_slots = Vec::with_capacity(env.len() + 1);
        if context
            .heap_reference_raw()
            .is_some_and(|raw| self.objects.contains_key(&raw))
        {
            trace_slots.push(context);
        }
        trace_slots.extend(self.mmtk_trace_slots_from_raw_words(env));
        self.allocate_raw_payload_with_storage(
            YObjectKind::Thunk,
            &trace_slots,
            &raw_payload,
            MmtkPayloadStorage::GcControlThunk { env_len: env.len() },
        )
    }

    pub fn gc_control_thunk_parts_i64(&self, value: YValue) -> Option<GcControlThunkParts> {
        let object = self.mmtk_object_reference(value)?;
        let header = Self::object_header_from_ref(object);
        if header.kind != YObjectKind::Thunk {
            return None;
        }
        decode_gc_control_thunk_payload(self.raw_payload_bytes_from_ref(object))
    }

    pub fn allocate_gc_control_guard_stack_push(
        &mut self,
        parent: YValue,
        guard_id: i64,
    ) -> YValue {
        let mut raw_payload = Vec::with_capacity(GC_CONTROL_GUARD_STACK_PAYLOAD_SIZE);
        raw_payload.push(GC_CONTROL_GUARD_STACK_TAG);
        raw_payload.resize(8, 0);
        raw_payload.extend_from_slice(&(parent.raw() as u64).to_ne_bytes());
        raw_payload.extend_from_slice(&(guard_id as u64).to_ne_bytes());
        let trace_slots = if parent
            .heap_reference_raw()
            .is_some_and(|raw| self.objects.contains_key(&raw))
        {
            vec![parent]
        } else {
            Vec::new()
        };
        self.allocate_raw_payload_with_storage(
            YObjectKind::ControlStack,
            &trace_slots,
            &raw_payload,
            MmtkPayloadStorage::ControlStack {
                item_count: 1,
                raw_trace_word_count: 0,
                has_parent: !parent.is_unit(),
            },
        )
    }

    pub fn gc_control_guard_stack_node(&self, value: YValue) -> Option<GcControlGuardStackNode> {
        if value.is_unit() {
            return None;
        }
        let object = self.mmtk_object_reference(value)?;
        let header = Self::object_header_from_ref(object);
        if header.kind != YObjectKind::ControlStack {
            return None;
        }
        decode_gc_control_guard_stack_payload(self.raw_payload_bytes_from_ref(object))
    }

    pub fn gc_control_guard_stack_contains(&self, stack: YValue, guard_id: i64) -> bool {
        let mut cursor = stack;
        while let Some(node) = self.gc_control_guard_stack_node(cursor) {
            if node.guard_id == guard_id {
                return true;
            }
            cursor = node.parent;
        }
        false
    }

    pub fn gc_control_guard_stack_peek(&self, stack: YValue) -> Option<i64> {
        self.gc_control_guard_stack_node(stack)
            .map(|node| node.guard_id)
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
        self.remember_object(raw, storage);
        YValue::from_heap_reference_raw(raw).expect("MMTk object reference must fit YValue")
    }

    fn allocate_compact_control_block(
        &mut self,
        kind: YObjectKind,
        head: Option<(&'static str, NativeFieldValue)>,
        env: &[YValue],
    ) -> YValue {
        let head_name = head.as_ref().map(|(name, _)| *name);
        let mut raw_payload = Vec::with_capacity(
            COMPACT_CONTROL_HEADER_SIZE + (usize::from(head_name.is_some()) + env.len()) * 8,
        );
        raw_payload.push(COMPACT_CONTROL_BLOCK_TAG);
        raw_payload.push(u8::from(head_name.is_some()));
        raw_payload.extend_from_slice(&(env.len() as u64).to_ne_bytes());
        raw_payload.resize(COMPACT_CONTROL_HEADER_SIZE, 0);
        if let Some((_, NativeFieldValue::U64(word))) = head {
            raw_payload.extend_from_slice(&word.to_ne_bytes());
        } else if head.is_some() {
            panic!("compact control head must be a u64 word");
        }
        for slot in env {
            raw_payload.extend_from_slice(&(slot.raw() as u64).to_ne_bytes());
        }
        let trace_slots = env
            .iter()
            .copied()
            .filter(|value| {
                value
                    .heap_reference_raw()
                    .is_some_and(|raw| self.objects.contains_key(&raw))
            })
            .collect::<Vec<_>>();
        self.allocate_raw_payload_with_storage(
            kind,
            &trace_slots,
            &raw_payload,
            MmtkPayloadStorage::ControlBlock {
                env_len: env.len(),
                head_name,
            },
        )
    }

    fn allocate_compact_control_block_i64(
        &mut self,
        kind: YObjectKind,
        head: Option<(&'static str, u64)>,
        env: &[i64],
    ) -> YValue {
        let head_name = head.as_ref().map(|(name, _)| *name);
        let mut raw_payload = Vec::with_capacity(
            COMPACT_CONTROL_HEADER_SIZE + (usize::from(head_name.is_some()) + env.len()) * 8,
        );
        raw_payload.push(COMPACT_CONTROL_BLOCK_TAG);
        raw_payload.push(u8::from(head_name.is_some()));
        raw_payload.extend_from_slice(&(env.len() as u64).to_ne_bytes());
        raw_payload.resize(COMPACT_CONTROL_HEADER_SIZE, 0);
        if let Some((_, word)) = head {
            raw_payload.extend_from_slice(&word.to_ne_bytes());
        }
        for slot in env {
            raw_payload.extend_from_slice(&(*slot as u64).to_ne_bytes());
        }
        let trace_slots = self.mmtk_trace_slots_from_raw_words(env);
        self.allocate_raw_payload_with_storage(
            kind,
            &trace_slots,
            &raw_payload,
            MmtkPayloadStorage::ControlBlock {
                env_len: env.len(),
                head_name,
            },
        )
    }

    fn mmtk_trace_slots_from_raw_words(&self, raw_words: &[i64]) -> Vec<YValue> {
        raw_words
            .iter()
            .filter_map(|word| {
                let value = YValue::from_raw(*word as usize);
                let raw = value.heap_reference_raw()?;
                if !self.may_be_tracked_object_raw(raw) {
                    return None;
                }
                self.objects.contains_key(&raw).then_some(value)
            })
            .collect()
    }

    pub fn raw_payload_bytes(&self, value: YValue) -> Option<&[u8]> {
        let object = self.object_reference(value)?;
        Some(self.raw_payload_bytes_from_ref(object))
    }

    fn raw_payload_bytes_from_ref(&self, object: ObjectReference) -> &[u8] {
        let header = Self::mmtk_header(object);
        let raw_size = header
            .total_size()
            .checked_sub(YulangMmtkObjectHeader::header_size())
            .expect("MMTk object total size should include the header")
            .checked_sub(YulangMmtkObjectHeader::trace_slots_byte_size(
                header.trace_slot_count(),
            ))
            .expect("MMTk object total size should include trace slots");
        unsafe {
            std::slice::from_raw_parts(
                YulangMmtkObjectHeader::raw_payload_address(object).to_ptr(),
                raw_size,
            )
        }
    }

    fn trace_child(&self, value: YValue, index: usize) -> Option<YValue> {
        let raw = value.heap_reference_raw()?;
        let object = Self::object_reference_from_raw(raw);
        let header = Self::mmtk_header(object);
        if index >= header.trace_slot_count() {
            return None;
        }
        let raw =
            unsafe { YulangMmtkObjectHeader::trace_slot_address(object, index).load::<usize>() };
        Some(YValue::from_raw(raw))
    }

    fn mmtk_object_reference(&self, value: YValue) -> Option<ObjectReference> {
        let raw = value.heap_reference_raw()?;
        if !self.may_be_tracked_object_raw(raw) {
            return None;
        }
        self.objects.contains_key(&raw).then(|| {
            ObjectReference::from_raw_address(raw_address(raw))
                .expect("tracked MMTk object reference should remain valid")
        })
    }
}

impl std::fmt::Debug for MmtkHeap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MmtkHeap")
            .field("object_count", &self.objects.len())
            .finish_non_exhaustive()
    }
}

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
        self.remember_object(raw, MmtkPayloadStorage::SemanticObject);
        YValue::from_heap_reference_raw(raw).expect("MMTk object reference must fit YValue")
    }

    fn object(&self, value: YValue) -> Option<&YObject> {
        let raw = value.heap_reference_raw()?;
        (self.objects.get(&raw) == Some(&MmtkPayloadStorage::SemanticObject)).then(|| {
            let object = Self::object_reference_from_raw(raw);
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
        let raw = value.heap_reference_raw()?;
        let object = Self::object_reference_from_raw(raw);
        Some(Self::object_header_from_ref(object))
    }

    fn trace_children(&self, value: YValue) -> Option<Vec<YValue>> {
        let raw = value.heap_reference_raw()?;
        let object = Self::object_reference_from_raw(raw);
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

impl MmtkHeap {
    fn allocate_mmtk_object(
        &mut self,
        kind: YObjectKind,
        trace_slots: &[YValue],
        raw_payload_size: usize,
    ) -> ObjectReference {
        let bytes = YulangMmtkObjectHeader::total_size_for(trace_slots.len(), raw_payload_size);
        self.allocation_profile
            .record(kind, trace_slots.len(), raw_payload_size, bytes);
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

    fn object_reference_from_raw(raw: usize) -> ObjectReference {
        ObjectReference::from_raw_address(raw_address(raw))
            .expect("YValue heap reference should be a valid MMTk object reference")
    }

    fn remember_object(&mut self, raw: usize, storage: MmtkPayloadStorage) {
        self.min_object_raw = self.min_object_raw.min(raw);
        self.max_object_raw = self.max_object_raw.max(raw);
        self.allocation_profile
            .record_storage(storage.profile_label());
        self.objects.insert(raw, storage);
    }

    fn may_be_tracked_object_raw(&self, raw: usize) -> bool {
        !self.objects.is_empty() && (self.min_object_raw..=self.max_object_raw).contains(&raw)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct MmtkAllocationProfile {
    pub objects: usize,
    pub trace_slots: usize,
    pub raw_payload_bytes: usize,
    pub total_object_bytes: usize,
    pub max_trace_slots: usize,
    pub max_raw_payload_bytes: usize,
    pub by_kind: BTreeMap<YObjectKind, MmtkAllocationKindProfile>,
    pub by_storage: BTreeMap<&'static str, usize>,
}

impl MmtkAllocationProfile {
    fn record(
        &mut self,
        kind: YObjectKind,
        trace_slots: usize,
        raw_payload_bytes: usize,
        total_object_bytes: usize,
    ) {
        self.objects += 1;
        self.trace_slots += trace_slots;
        self.raw_payload_bytes += raw_payload_bytes;
        self.total_object_bytes += total_object_bytes;
        self.max_trace_slots = self.max_trace_slots.max(trace_slots);
        self.max_raw_payload_bytes = self.max_raw_payload_bytes.max(raw_payload_bytes);
        self.by_kind.entry(kind).or_default().record(
            trace_slots,
            raw_payload_bytes,
            total_object_bytes,
        );
    }

    fn record_storage(&mut self, storage: &'static str) {
        *self.by_storage.entry(storage).or_default() += 1;
    }

    fn kind_summary(&self) -> String {
        self.by_kind
            .iter()
            .map(|(kind, profile)| {
                format!(
                    "{}:objects={},trace_slots={},raw_bytes={},total_bytes={}",
                    kind,
                    profile.objects,
                    profile.trace_slots,
                    profile.raw_payload_bytes,
                    profile.total_object_bytes,
                )
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn storage_summary(&self) -> String {
        self.by_storage
            .iter()
            .map(|(storage, count)| format!("{storage}={count}"))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct MmtkAllocationKindProfile {
    pub objects: usize,
    pub trace_slots: usize,
    pub raw_payload_bytes: usize,
    pub total_object_bytes: usize,
}

impl MmtkAllocationKindProfile {
    fn record(&mut self, trace_slots: usize, raw_payload_bytes: usize, total_object_bytes: usize) {
        self.objects += 1;
        self.trace_slots += trace_slots;
        self.raw_payload_bytes += raw_payload_bytes;
        self.total_object_bytes += total_object_bytes;
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum MmtkPayloadStorage {
    SemanticObject,
    RawBytes,
    NativeBlock {
        layout: NativeLayoutHandle,
    },
    ControlBlock {
        env_len: usize,
        head_name: Option<&'static str>,
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
    ControlStack {
        item_count: usize,
        raw_trace_word_count: usize,
        has_parent: bool,
    },
    GcControlState,
    GcControlThunk {
        env_len: usize,
    },
}

impl MmtkPayloadStorage {
    fn profile_label(&self) -> &'static str {
        match self {
            Self::SemanticObject => "semantic",
            Self::RawBytes => "raw",
            Self::NativeBlock { .. } => "native-block",
            Self::StringLeaf { .. } => "string-leaf",
            Self::StringNode { .. } => "string-node",
            Self::ListLeaf { .. } => "list-leaf",
            Self::ListNode { .. } => "list-node",
            Self::ControlBlock { .. } => "control-block",
            Self::ControlStack { .. } => "control-stack",
            Self::GcControlState => "gc-control-state",
            Self::GcControlThunk { .. } => "gc-control-thunk",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GcControlStateParts {
    pub handler_stack: YValue,
    pub guard_stack: YValue,
    pub return_frames: YValue,
    pub active_blocked: YValue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GcControlThunkParts {
    pub code: usize,
    pub context: YValue,
    pub env_ptr: *const i64,
    pub env_len: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GcControlGuardStackNode {
    pub parent: YValue,
    pub guard_id: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TreeColor {
    Red,
    Black,
}

impl TreeColor {
    fn encode(self) -> u8 {
        match self {
            Self::Red => 0,
            Self::Black => 1,
        }
    }

    fn decode(value: u8) -> Option<Self> {
        match value {
            0 => Some(Self::Red),
            1 => Some(Self::Black),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompactStringTreeStorage {
    Leaf {
        len_chars: usize,
        len_bytes: usize,
    },
    Node {
        color: TreeColor,
        len_chars: usize,
        len_bytes: usize,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompactListTreeStorage {
    Leaf { len: usize },
    Node { color: TreeColor, len: usize },
}

impl CompactListTreeStorage {
    fn len(self) -> usize {
        match self {
            Self::Leaf { len } | Self::Node { len, .. } => len,
        }
    }

    fn is_leaf(self) -> bool {
        matches!(self, Self::Leaf { .. })
    }
}

fn raw_address(raw: usize) -> mmtk::util::Address {
    unsafe { mmtk::util::Address::from_usize(raw) }
}

fn encode_compact_string_node_payload(
    color: TreeColor,
    len_chars: usize,
    len_bytes: usize,
) -> Vec<u8> {
    let mut payload =
        Vec::with_capacity(COMPACT_NODE_HEADER_SIZE + 2 * std::mem::size_of::<usize>());
    payload.push(COMPACT_STRING_NODE_TAG);
    payload.push(color.encode());
    payload.extend_from_slice(&len_chars.to_ne_bytes());
    payload.extend_from_slice(&len_bytes.to_ne_bytes());
    payload
}

fn decode_compact_string_node_payload(bytes: &[u8]) -> Option<(TreeColor, usize, usize)> {
    let word = std::mem::size_of::<usize>();
    if bytes.len() != COMPACT_NODE_HEADER_SIZE + 2 * word {
        return None;
    }
    if bytes[0] != COMPACT_STRING_NODE_TAG {
        return None;
    }
    let color = TreeColor::decode(bytes[1])?;
    let len_chars = usize::from_ne_bytes(bytes[2..2 + word].try_into().ok()?);
    let len_bytes = usize::from_ne_bytes(bytes[2 + word..2 + 2 * word].try_into().ok()?);
    Some((color, len_chars, len_bytes))
}

fn encode_compact_list_node_payload(color: TreeColor, len: usize) -> Vec<u8> {
    let mut payload = Vec::with_capacity(COMPACT_NODE_HEADER_SIZE + std::mem::size_of::<usize>());
    payload.push(COMPACT_LIST_NODE_TAG);
    payload.push(color.encode());
    payload.extend_from_slice(&len.to_ne_bytes());
    payload
}

fn decode_compact_list_node_payload(bytes: &[u8]) -> Option<(TreeColor, usize)> {
    let word = std::mem::size_of::<usize>();
    if bytes.len() != COMPACT_NODE_HEADER_SIZE + word {
        return None;
    }
    if bytes[0] != COMPACT_LIST_NODE_TAG {
        return None;
    }
    let color = TreeColor::decode(bytes[1])?;
    let len = usize::from_ne_bytes(bytes[2..2 + word].try_into().ok()?);
    Some((color, len))
}

fn encode_compact_variant_payload(
    tag: YSymbolId,
    has_payload: bool,
) -> [u8; COMPACT_VARIANT_HEADER_SIZE] {
    let mut payload = [0; COMPACT_VARIANT_HEADER_SIZE];
    payload[0] = COMPACT_VARIANT_TAG;
    payload[1] = u8::from(has_payload);
    payload[2..6].copy_from_slice(&tag.0.to_ne_bytes());
    payload
}

fn decode_compact_variant_payload(bytes: &[u8]) -> Option<(YSymbolId, bool)> {
    if bytes.len() != COMPACT_VARIANT_HEADER_SIZE {
        return None;
    }
    if bytes[0] != COMPACT_VARIANT_TAG {
        return None;
    }
    let has_payload = match bytes[1] {
        0 => false,
        1 => true,
        _ => return None,
    };
    let tag = YSymbolId(u32::from_ne_bytes(bytes[2..6].try_into().ok()?));
    Some((tag, has_payload))
}

fn encode_compact_record_payload(fields: &[(Box<str>, YValue)]) -> Vec<u8> {
    let names_len = fields.iter().map(|(name, _)| name.len()).sum::<usize>();
    let mut payload = Vec::with_capacity(
        COMPACT_RECORD_HEADER_SIZE + fields.len() * std::mem::size_of::<u32>() + names_len,
    );
    payload.push(COMPACT_RECORD_TAG);
    payload.extend_from_slice(&(fields.len() as u32).to_ne_bytes());
    for (name, _) in fields {
        let bytes = name.as_bytes();
        payload.extend_from_slice(&(bytes.len() as u32).to_ne_bytes());
        payload.extend_from_slice(bytes);
    }
    payload
}

fn decode_compact_record_payload(bytes: &[u8]) -> Option<Vec<Box<str>>> {
    let header = bytes.get(..COMPACT_RECORD_HEADER_SIZE)?;
    if header.first().copied()? != COMPACT_RECORD_TAG {
        return None;
    }
    let count = usize::try_from(u32::from_ne_bytes(header.get(1..5)?.try_into().ok()?)).ok()?;
    let mut names = Vec::with_capacity(count);
    let mut cursor = COMPACT_RECORD_HEADER_SIZE;
    for _ in 0..count {
        let len = usize::try_from(u32::from_ne_bytes(
            bytes.get(cursor..cursor + 4)?.try_into().ok()?,
        ))
        .ok()?;
        cursor += 4;
        let name = std::str::from_utf8(bytes.get(cursor..cursor + len)?).ok()?;
        names.push(Box::<str>::from(name));
        cursor += len;
    }
    (cursor == bytes.len()).then_some(names)
}

fn compact_control_kind_has_head(kind: YObjectKind) -> bool {
    matches!(
        kind,
        YObjectKind::Closure
            | YObjectKind::Thunk
            | YObjectKind::Resumption
            | YObjectKind::HandlerFrame
            | YObjectKind::ReturnFrame
    )
}

fn decode_compact_control_payload_header(bytes: &[u8]) -> Option<(usize, bool, Option<u64>)> {
    let header = bytes.get(..COMPACT_CONTROL_HEADER_SIZE)?;
    if header.first().copied()? != COMPACT_CONTROL_BLOCK_TAG {
        return None;
    }
    let has_head = match header.get(1).copied()? {
        0 => false,
        1 => true,
        _ => return None,
    };
    let env_len = usize::try_from(u64::from_ne_bytes(header.get(2..10)?.try_into().ok()?)).ok()?;
    let word = has_head
        .then(|| read_u64_from_prefix(bytes.get(COMPACT_CONTROL_HEADER_SIZE..)?))
        .flatten();
    if has_head && word.is_none() {
        return None;
    }
    Some((env_len, has_head, word))
}

fn decode_gc_control_state_payload(bytes: &[u8]) -> Option<GcControlStateParts> {
    if bytes.first().copied()? != GC_CONTROL_STATE_TAG {
        return None;
    }
    let fields = bytes.get(8..GC_CONTROL_STATE_PAYLOAD_SIZE)?;
    let mut words = fields.chunks_exact(8).map(read_u64_from_prefix);
    Some(GcControlStateParts {
        handler_stack: YValue::from_raw(words.next()?? as usize),
        guard_stack: YValue::from_raw(words.next()?? as usize),
        return_frames: YValue::from_raw(words.next()?? as usize),
        active_blocked: YValue::from_raw(words.next()?? as usize),
    })
}

fn decode_gc_control_thunk_payload(bytes: &[u8]) -> Option<GcControlThunkParts> {
    if bytes.first().copied()? != GC_CONTROL_THUNK_TAG {
        return None;
    }
    let env_len = usize::try_from(read_u64_from_prefix(bytes.get(8..)?)?).ok()?;
    let code = read_u64_from_prefix(bytes.get(16..)?)? as usize;
    let context = YValue::from_raw(read_u64_from_prefix(bytes.get(24..)?)? as usize);
    let env_start = GC_CONTROL_THUNK_HEADER_SIZE;
    let _ = bytes.get(env_start..env_start + env_len * 8)?;
    let env_ptr = unsafe { bytes.as_ptr().add(env_start).cast::<i64>() };
    Some(GcControlThunkParts {
        code,
        context,
        env_ptr,
        env_len,
    })
}

fn decode_gc_control_guard_stack_payload(bytes: &[u8]) -> Option<GcControlGuardStackNode> {
    if bytes.first().copied()? != GC_CONTROL_GUARD_STACK_TAG {
        return None;
    }
    Some(GcControlGuardStackNode {
        parent: YValue::from_raw(read_u64_from_prefix(bytes.get(8..)?)? as usize),
        guard_id: read_u64_from_prefix(bytes.get(16..)?)? as i64,
    })
}

fn read_u64_from_prefix(bytes: &[u8]) -> Option<u64> {
    Some(u64::from_ne_bytes(bytes.get(..8)?.try_into().ok()?))
}

fn encode_compact_control_stack_payload(
    item_count: usize,
    raw_trace_word_count: usize,
    has_parent: bool,
) -> Vec<u8> {
    let mut payload =
        Vec::with_capacity(COMPACT_NODE_HEADER_SIZE + 2 * std::mem::size_of::<usize>());
    payload.push(COMPACT_CONTROL_STACK_TAG);
    payload.push(u8::from(has_parent));
    payload.extend_from_slice(&item_count.to_ne_bytes());
    payload.extend_from_slice(&raw_trace_word_count.to_ne_bytes());
    payload
}

pub fn register_mmtk_cps_jit_symbols(builder: &mut cranelift_jit::JITBuilder) {
    macro_rules! symbols {
        ($($symbol:ident),+ $(,)?) => {
            $(builder.symbol(stringify!($symbol), $symbol as *const u8);)+
        };
    }

    symbols!(
        yulang_mmtk_cps_reset_i64,
        yulang_mmtk_cps_dump_heap_stats_i64,
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
        yulang_mmtk_cps_debug_i64,
        yulang_mmtk_cps_out_write_i64,
        yulang_mmtk_cps_err_write_i64,
        yulang_mmtk_cps_warn_write_i64,
        yulang_mmtk_cps_die_i64,
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
        yulang_mmtk_gc_control_empty_state_i64,
        yulang_mmtk_gc_control_push_guard_i64,
        yulang_mmtk_gc_control_find_guard_i64,
        yulang_mmtk_gc_control_peek_guard_i64,
    );
    crate::mmtk_cps_control::register_mmtk_cps_control_jit_symbols(builder);
}

pub struct MmtkNativeRuntimeContext {
    context: GcRuntimeContext<MmtkHeap>,
}

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

    pub fn gc_control_empty_state(&mut self) -> YValue {
        self.context
            .heap_mut()
            .allocate_gc_control_state(GcControlStateParts {
                handler_stack: YValue::UNIT,
                guard_stack: YValue::UNIT,
                return_frames: YValue::UNIT,
                active_blocked: YValue::UNIT,
            })
    }

    pub fn gc_control_push_guard(&mut self, state: YValue, guard_id: i64) -> Option<YValue> {
        let mut parts = self.context.heap().gc_control_state_parts(state)?;
        parts.guard_stack = self
            .context
            .heap_mut()
            .allocate_gc_control_guard_stack_push(parts.guard_stack, guard_id);
        Some(self.context.heap_mut().allocate_gc_control_state(parts))
    }

    pub fn gc_control_find_guard(&self, state: YValue, guard_id: i64) -> Option<bool> {
        let parts = self.context.heap().gc_control_state_parts(state)?;
        Some(
            self.context
                .heap()
                .gc_control_guard_stack_contains(parts.guard_stack, guard_id),
        )
    }

    pub fn gc_control_peek_guard(&self, state: YValue) -> Option<i64> {
        let parts = self.context.heap().gc_control_state_parts(state)?;
        self.context
            .heap()
            .gc_control_guard_stack_peek(parts.guard_stack)
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
        if self.compact_tuple_len(tuple).is_some() {
            return self.context.heap().trace_child(tuple, index);
        }
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
        Some(self.context.heap_mut().allocate_compact_variant(tag, value))
    }

    pub fn variant_tag_eq(&self, variant: YValue, tag: &[u8]) -> Option<bool> {
        let expected = std::str::from_utf8(tag).ok()?;
        if let Some((tag, _)) = self.compact_variant_metadata(variant) {
            return Some(
                self.context
                    .symbol(tag)
                    .is_some_and(|symbol| symbol.path.display_name() == expected),
            );
        }
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
        if let Some((_, has_payload)) = self.compact_variant_metadata(variant) {
            return has_payload.then(|| self.context.heap().trace_child(variant, 0))?;
        }
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
        if let Some(storage) = self.compact_list_storage(list) {
            return Some(storage.len());
        }

        Some(self.list_items(list)?.len())
    }

    pub fn list_get(&self, list: YValue, index: usize) -> Option<YValue> {
        if let Some(storage) = self.compact_list_storage(list) {
            return self.compact_list_get_with_storage(list, index, storage);
        }

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
        if let Some(storage) = self.compact_list_storage(list) {
            return self.compact_list_view_raw(list, storage);
        }

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

    pub fn display_value(&self, value: YValue) -> String {
        if self.is_compact_string_tree(value) {
            return self
                .render_string(value)
                .unwrap_or_else(|| "<invalid compact string>".to_string());
        }
        self.debug_value(value)
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
        if self.is_compact_kind(value, YObjectKind::Record) {
            return self.debug_record(value);
        }
        if self.is_compact_kind(value, YObjectKind::Variant) {
            return self.debug_variant(value);
        }
        if self.is_compact_list_tree(value) {
            return self.debug_list(value);
        }
        self.context.debug_value(value)
    }

    fn alloc_compact_tuple(&mut self, items: &[YValue]) -> YValue {
        self.context.heap_mut().allocate_compact_tuple(items)
    }

    fn tuple_items(&self, value: YValue) -> Option<Vec<YValue>> {
        if let Some(len) = self.compact_tuple_len(value) {
            let mut items = Vec::with_capacity(len);
            for index in 0..len {
                items.push(self.context.heap().trace_child(value, index)?);
            }
            return Some(items);
        }

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
        self.context.heap_mut().allocate_compact_record(fields)
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
        match self.compact_string_storage(value)? {
            CompactStringTreeStorage::Leaf { .. } => {
                let text = self.render_string(value)?;
                let (start, end) = char_range_to_byte_range(&text, start, end)?;
                self.context
                    .heap_mut()
                    .allocate_string_leaf(text.get(start..end)?.as_bytes())
            }
            CompactStringTreeStorage::Node { .. } => {
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
        match self.compact_string_storage(value) {
            Some(CompactStringTreeStorage::Leaf { len_chars, .. })
            | Some(CompactStringTreeStorage::Node { len_chars, .. }) => Some(len_chars),
            None => {
                let object = self.context.object(value)?;
                let YObjectPayload::String(value) = object.payload() else {
                    return None;
                };
                Some(self.render_string_payload(value)?.chars().count())
            }
        }
    }

    fn string_tree_len_bytes(&self, value: YValue) -> Option<usize> {
        match self.compact_string_storage(value) {
            Some(CompactStringTreeStorage::Leaf { len_bytes, .. })
            | Some(CompactStringTreeStorage::Node { len_bytes, .. }) => Some(len_bytes),
            None => Some(self.render_string(value)?.len()),
        }
    }

    fn string_black_height(&self, value: YValue) -> Option<usize> {
        match self.compact_string_storage(value)? {
            CompactStringTreeStorage::Leaf { .. } => Some(0),
            CompactStringTreeStorage::Node { color, .. } => {
                let [left, _] = self.tree_binary_children(value)?;
                Some(self.string_black_height(left)? + usize::from(color == TreeColor::Black))
            }
        }
    }

    #[cfg(test)]
    fn string_red_black_status(&self, value: YValue) -> Option<usize> {
        match self.compact_string_storage(value)? {
            CompactStringTreeStorage::Leaf { .. } => Some(0),
            CompactStringTreeStorage::Node { color, .. } => {
                let [left, right] = self.tree_binary_children(value)?;
                let left_height = self.string_red_black_status(left)?;
                let right_height = self.string_red_black_status(right)?;
                if left_height != right_height {
                    return None;
                }
                if color == TreeColor::Red
                    && (self.string_node_color(left) == Some(TreeColor::Red)
                        || self.string_node_color(right) == Some(TreeColor::Red))
                {
                    return None;
                }
                Some(left_height + usize::from(color == TreeColor::Black))
            }
        }
    }

    fn string_node_color(&self, value: YValue) -> Option<TreeColor> {
        match self.compact_string_storage(value)? {
            CompactStringTreeStorage::Node { color, .. } => Some(color),
            _ => None,
        }
    }

    fn is_string_leaf(&self, value: YValue) -> bool {
        matches!(
            self.compact_string_storage(value),
            Some(CompactStringTreeStorage::Leaf { .. })
        )
    }

    fn is_string_node(&self, value: YValue) -> bool {
        matches!(
            self.compact_string_storage(value),
            Some(CompactStringTreeStorage::Node { .. })
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
        let left_storage = self.compact_list_storage(left)?;
        let left_len = left_storage.len();
        if left_len == 0 {
            return Some(right);
        }
        let right_storage = self.compact_list_storage(right)?;
        let right_len = right_storage.len();
        if right_len == 0 {
            return Some(left);
        }
        if left_storage.is_leaf()
            && right_storage.is_leaf()
            && left_len + right_len <= MAX_LIST_LEAF_ITEMS
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
        match self.compact_list_storage(value)? {
            CompactListTreeStorage::Leaf { .. } => {
                let items = self.list_leaf_items(value)?;
                let prefix = self.list_from_items(items.get(..index)?)?;
                let suffix = self.list_from_items(items.get(index..)?)?;
                Some((prefix, suffix))
            }
            CompactListTreeStorage::Node { .. } => {
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
        }
    }

    fn compact_list_view_raw(
        &mut self,
        list: YValue,
        storage: CompactListTreeStorage,
    ) -> Option<YValue> {
        match storage {
            CompactListTreeStorage::Leaf { len: 0 } => self.variant(b"empty", None),
            CompactListTreeStorage::Leaf { len: 1 } => {
                self.variant(b"leaf", self.list_get(list, 0))
            }
            CompactListTreeStorage::Leaf { len } => {
                let (left, right) = self.list_split_at_unchecked(list, len / 2)?;
                let payload = self.alloc_compact_tuple(&[left, right]);
                self.variant(b"node", Some(payload))
            }
            CompactListTreeStorage::Node { .. } => {
                let [left, right] = self.tree_binary_children(list)?;
                let payload = self.alloc_compact_tuple(&[left, right]);
                self.variant(b"node", Some(payload))
            }
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
        Some(self.compact_list_storage(value)?.len())
    }

    fn compact_list_get(&self, value: YValue, index: usize) -> Option<YValue> {
        let storage = self.compact_list_storage(value)?;
        self.compact_list_get_with_storage(value, index, storage)
    }

    fn compact_list_get_with_storage(
        &self,
        value: YValue,
        index: usize,
        storage: CompactListTreeStorage,
    ) -> Option<YValue> {
        match storage {
            CompactListTreeStorage::Leaf { len } => {
                if index >= len {
                    return None;
                }
                self.context.heap().trace_child(value, index)
            }
            CompactListTreeStorage::Node { len, .. } => {
                if index >= len {
                    return None;
                }
                let [left, right] = self.tree_binary_children(value)?;
                let left_len = self.list_tree_len(left)?;
                if index < left_len {
                    self.compact_list_get(left, index)
                } else {
                    self.compact_list_get(right, index - left_len)
                }
            }
        }
    }

    fn list_black_height(&self, value: YValue) -> Option<usize> {
        match self.compact_list_storage(value)? {
            CompactListTreeStorage::Leaf { .. } => Some(0),
            CompactListTreeStorage::Node { color, .. } => {
                let [left, _] = self.tree_binary_children(value)?;
                Some(self.list_black_height(left)? + usize::from(color == TreeColor::Black))
            }
        }
    }

    #[cfg(test)]
    fn list_red_black_status(&self, value: YValue) -> Option<usize> {
        match self.compact_list_storage(value)? {
            CompactListTreeStorage::Leaf { .. } => Some(0),
            CompactListTreeStorage::Node { color, .. } => {
                let [left, right] = self.tree_binary_children(value)?;
                let left_height = self.list_red_black_status(left)?;
                let right_height = self.list_red_black_status(right)?;
                if left_height != right_height {
                    return None;
                }
                if color == TreeColor::Red
                    && (self.list_node_color(left) == Some(TreeColor::Red)
                        || self.list_node_color(right) == Some(TreeColor::Red))
                {
                    return None;
                }
                Some(left_height + usize::from(color == TreeColor::Black))
            }
        }
    }

    fn list_node_color(&self, value: YValue) -> Option<TreeColor> {
        match self.compact_list_storage(value)? {
            CompactListTreeStorage::Node { color, .. } => Some(color),
            _ => None,
        }
    }

    fn is_list_node(&self, value: YValue) -> bool {
        matches!(
            self.compact_list_storage(value),
            Some(CompactListTreeStorage::Node { .. })
        )
    }

    fn record_fields(&self, value: YValue) -> Option<Vec<(Box<str>, YValue)>> {
        if let Some(names) = self.compact_record_field_names(value) {
            let mut fields = Vec::with_capacity(names.len());
            for (index, name) in names.into_iter().enumerate() {
                fields.push((name, self.context.heap().trace_child(value, index)?));
            }
            return Some(fields);
        }

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
        match kind {
            YObjectKind::Tuple if self.compact_tuple_len(value).is_some() => return true,
            YObjectKind::Variant if self.compact_variant_metadata(value).is_some() => return true,
            YObjectKind::Record if self.compact_record_field_names(value).is_some() => return true,
            _ => {}
        }
        self.is_compact_native_block_kind(value, kind)
    }

    fn is_compact_native_block_kind(&self, value: YValue, kind: YObjectKind) -> bool {
        self.context.object(value).is_none()
            && self
                .context
                .heap()
                .object_header(value)
                .is_some_and(|header| header.kind == kind)
            && self.context.heap().native_field_count(value).is_some()
    }

    fn compact_tuple_len(&self, value: YValue) -> Option<usize> {
        let header = self.context.heap().object_header(value)?;
        if header.kind != YObjectKind::Tuple {
            return None;
        }
        (self.context.heap().raw_payload_bytes(value)? == [COMPACT_TUPLE_TAG])
            .then_some(header.trace_slots)
    }

    fn compact_record_field_names(&self, value: YValue) -> Option<Vec<Box<str>>> {
        let header = self.context.heap().object_header(value)?;
        if header.kind != YObjectKind::Record {
            return None;
        }
        let names = decode_compact_record_payload(self.context.heap().raw_payload_bytes(value)?)?;
        (header.trace_slots == names.len()).then_some(names)
    }

    fn is_compact_string_tree(&self, value: YValue) -> bool {
        self.compact_string_storage(value).is_some()
    }

    fn is_compact_list_tree(&self, value: YValue) -> bool {
        self.compact_list_storage(value).is_some()
    }

    fn mmtk_storage(&self, value: YValue) -> Option<&MmtkPayloadStorage> {
        let raw = value.heap_reference_raw()?;
        self.context.heap().objects.get(&raw)
    }

    fn compact_string_storage(&self, value: YValue) -> Option<CompactStringTreeStorage> {
        let header = self.context.heap().object_header(value)?;
        if header.kind != YObjectKind::String {
            return None;
        }
        let raw = self.context.heap().raw_payload_bytes(value)?;
        match header.trace_slots {
            0 => {
                let text = std::str::from_utf8(raw).ok()?;
                Some(CompactStringTreeStorage::Leaf {
                    len_chars: text.chars().count(),
                    len_bytes: raw.len(),
                })
            }
            2 => {
                let (color, len_chars, len_bytes) = decode_compact_string_node_payload(raw)?;
                Some(CompactStringTreeStorage::Node {
                    color,
                    len_chars,
                    len_bytes,
                })
            }
            _ => None,
        }
    }

    fn compact_list_storage(&self, value: YValue) -> Option<CompactListTreeStorage> {
        let header = self.context.heap().object_header(value)?;
        if header.kind != YObjectKind::List {
            return None;
        }
        let raw = self.context.heap().raw_payload_bytes(value)?;
        if raw.is_empty() {
            return Some(CompactListTreeStorage::Leaf {
                len: header.trace_slots,
            });
        }
        let (color, len) = decode_compact_list_node_payload(raw)?;
        Some(CompactListTreeStorage::Node { color, len })
    }

    fn tree_binary_children(&self, value: YValue) -> Option<[YValue; 2]> {
        let heap = self.context.heap();
        Some([heap.trace_child(value, 0)?, heap.trace_child(value, 1)?])
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
        if let Some(storage) = self.compact_list_storage(value) {
            return self.debug_compact_list(value, storage);
        }

        let Some(items) = self.list_items(value) else {
            return "<invalid compact list>".to_string();
        };
        let rendered = items
            .into_iter()
            .map(|item| self.debug_value(item))
            .collect::<Vec<_>>();
        format!("[{}]", rendered.join(", "))
    }

    fn debug_compact_list(&self, value: YValue, storage: CompactListTreeStorage) -> String {
        let len = match storage {
            CompactListTreeStorage::Leaf { len } | CompactListTreeStorage::Node { len, .. } => len,
        };
        let mut out = String::with_capacity(len.saturating_mul(4).saturating_add(2));
        out.push('[');
        let mut first = true;
        if self
            .push_compact_list_debug_items(value, &mut out, &mut first)
            .is_none()
        {
            return "<invalid compact list>".to_string();
        }
        out.push(']');
        out
    }

    fn push_compact_list_debug_items(
        &self,
        value: YValue,
        out: &mut String,
        first: &mut bool,
    ) -> Option<()> {
        match self.compact_list_storage(value)? {
            CompactListTreeStorage::Leaf { len } => {
                for index in 0..len {
                    if !*first {
                        out.push_str(", ");
                    }
                    *first = false;
                    self.push_debug_value(out, self.context.heap().trace_child(value, index)?)?;
                }
            }
            CompactListTreeStorage::Node { .. } => {
                let [left, right] = self.tree_binary_children(value)?;
                self.push_compact_list_debug_items(left, out, first)?;
                self.push_compact_list_debug_items(right, out, first)?;
            }
        }
        Some(())
    }

    fn push_debug_value(&self, out: &mut String, value: YValue) -> Option<()> {
        if let Some(value) = value.as_i63() {
            write!(out, "{value}").ok()?;
            return Some(());
        }
        if let Some(value) = value.as_bool() {
            out.push_str(if value { "true" } else { "false" });
            return Some(());
        }
        if value.is_unit() {
            out.push_str("()");
            return Some(());
        }
        out.push_str(&self.debug_value(value));
        Some(())
    }

    fn debug_record(&self, value: YValue) -> String {
        let Some(fields) = self.record_fields(value) else {
            return "<invalid compact record>".to_string();
        };
        let rendered = fields
            .into_iter()
            .map(|(name, value)| format!("{name}: {}", self.debug_value(value)))
            .collect::<Vec<_>>();
        format!("{{{}}}", rendered.join(", "))
    }

    fn debug_variant(&self, value: YValue) -> String {
        let Some(tag) = self.variant_tag_name(value) else {
            return "<invalid compact variant>".to_string();
        };
        match self.variant_payload(value) {
            Some(payload) => format!("{tag} {}", self.debug_value(payload)),
            None => tag.to_string(),
        }
    }

    fn render_string(&self, value: YValue) -> Option<String> {
        if let Some(storage) = self.compact_string_storage(value) {
            let bytes = self.context.heap().raw_payload_bytes(value)?;
            return match storage {
                CompactStringTreeStorage::Leaf { .. } => {
                    std::str::from_utf8(bytes).map(str::to_string).ok()
                }
                CompactStringTreeStorage::Node { .. } => {
                    let [left, right] = self.tree_binary_children(value)?;
                    let mut out = self.render_string(left)?;
                    out.push_str(&self.render_string(right)?);
                    Some(out)
                }
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
        if let Some(storage) = self.compact_list_storage(value) {
            return self.compact_list_items(value, storage);
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

    fn compact_list_items(
        &self,
        value: YValue,
        storage: CompactListTreeStorage,
    ) -> Option<Vec<YValue>> {
        let len = match storage {
            CompactListTreeStorage::Leaf { len } | CompactListTreeStorage::Node { len, .. } => len,
        };
        let mut out = Vec::with_capacity(len);
        self.push_compact_list_items(value, &mut out)?;
        (out.len() == len).then_some(out)
    }

    fn push_compact_list_items(&self, value: YValue, out: &mut Vec<YValue>) -> Option<()> {
        match self.compact_list_storage(value)? {
            CompactListTreeStorage::Leaf { len } => {
                for index in 0..len {
                    out.push(self.context.heap().trace_child(value, index)?);
                }
            }
            CompactListTreeStorage::Node { .. } => {
                let [left, right] = self.tree_binary_children(value)?;
                self.push_compact_list_items(left, out)?;
                self.push_compact_list_items(right, out)?;
            }
        }
        Some(())
    }

    fn list_leaf_items(&self, value: YValue) -> Option<Vec<YValue>> {
        match self.compact_list_storage(value)? {
            CompactListTreeStorage::Leaf { len } => {
                let mut items = Vec::with_capacity(len);
                for index in 0..len {
                    items.push(self.context.heap().trace_child(value, index)?);
                }
                Some(items)
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
        if let Some((tag, _)) = self.compact_variant_metadata(value) {
            return self
                .context
                .symbol(tag)
                .map(|symbol| Box::<str>::from(symbol.path.display_name()));
        }

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

    fn compact_variant_metadata(&self, value: YValue) -> Option<(YSymbolId, bool)> {
        let header = self.context.heap().object_header(value)?;
        if header.kind != YObjectKind::Variant {
            return None;
        }
        let (tag, has_payload) =
            decode_compact_variant_payload(self.context.heap().raw_payload_bytes(value)?)?;
        if header.trace_slots != usize::from(has_payload) {
            return None;
        }
        Some((tag, has_payload))
    }
}

fn encode_yvalue(value: YValue) -> i64 {
    value.raw() as i64
}

fn decode_yvalue(value: i64) -> YValue {
    YValue::from_raw(value as usize)
}

const YVALUE_I63_TAG: i64 = 0b001;
const YVALUE_FALSE_BITS: i64 = 0b010;
const YVALUE_TRUE_BITS: i64 = 0b110;
const YVALUE_I63_MIN: i64 = -(1_i64 << 62);
const YVALUE_I63_MAX: i64 = (1_i64 << 62) - 1;

fn raw_i63(value: i64) -> Option<i64> {
    (value & YVALUE_I63_TAG == YVALUE_I63_TAG).then_some(value >> 1)
}

fn encode_raw_i63(value: i64) -> Option<i64> {
    (YVALUE_I63_MIN..=YVALUE_I63_MAX)
        .contains(&value)
        .then_some((value << 1) | YVALUE_I63_TAG)
}

fn encode_raw_bool(value: bool) -> i64 {
    if value {
        YVALUE_TRUE_BITS
    } else {
        YVALUE_FALSE_BITS
    }
}

fn context_int_from_i64(value: i64) -> Option<i64> {
    YValue::from_i63(value).map(encode_yvalue)
}

fn context_int_from_usize(value: usize) -> Option<i64> {
    i64::try_from(value).ok().and_then(context_int_from_i64)
}

fn bytes_from_raw<'a>(ptr: *const u8, len: usize) -> Option<&'a [u8]> {
    if ptr.is_null() && len != 0 {
        return None;
    }
    Some(unsafe { std::slice::from_raw_parts(ptr, len) })
}

fn mmtk_format_float(value: f64) -> String {
    let mut rendered = value.to_string();
    if !rendered.contains('.') && !rendered.contains('e') && !rendered.contains('E') {
        rendered.push_str(".0");
    }
    rendered
}

#[cfg(unix)]
fn path_buf_bytes(path: &std::path::PathBuf) -> Vec<u8> {
    use std::os::unix::ffi::OsStrExt;

    path.as_os_str().as_bytes().to_vec()
}

#[cfg(not(unix))]
fn path_buf_bytes(path: &std::path::PathBuf) -> Vec<u8> {
    path.to_string_lossy().as_bytes().to_vec()
}

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

fn char_index_to_byte_index(text: &str, index: usize) -> Option<usize> {
    if index == text.chars().count() {
        return Some(text.len());
    }
    text.char_indices().nth(index).map(|(byte, _)| byte)
}

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

thread_local! {
    static MMTK_CPS_CONTEXT: Cell<*mut MmtkNativeRuntimeContext> = const { Cell::new(std::ptr::null_mut()) };
    static MMTK_CPS_TAG_NAMES: RefCell<HashMap<i64, Box<str>>> = RefCell::new(HashMap::new());
    static MMTK_CPS_CONTROL_STACK_SNAPSHOTS_ENABLED: RefCell<bool> = const { RefCell::new(false) };
}

pub(crate) fn with_mmtk_cps_context<R>(
    f: impl FnOnce(&mut MmtkNativeRuntimeContext) -> R,
) -> Option<R> {
    let ptr = mmtk_cps_context_ptr()?;
    Some(f(unsafe { &mut *ptr }))
}

pub(crate) fn mmtk_cps_context_ptr() -> Option<*mut MmtkNativeRuntimeContext> {
    MMTK_CPS_CONTEXT.with(|slot| {
        let mut ptr = slot.get();
        if ptr.is_null() {
            ptr = Box::into_raw(Box::new(MmtkNativeRuntimeContext::new_no_gc().ok()?));
            slot.set(ptr);
        }
        Some(ptr)
    })
}

fn mmtk_cps_tag_name(tag: i64) -> String {
    MMTK_CPS_TAG_NAMES.with(|names| {
        names
            .borrow()
            .get(&tag)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{tag}"))
    })
}

fn mmtk_cps_register_tag_name(tag: i64, name: &str) {
    MMTK_CPS_TAG_NAMES.with(|names| {
        names
            .borrow_mut()
            .entry(tag)
            .or_insert_with(|| name.to_string().into_boxed_str());
    });
}

pub(crate) fn mmtk_cps_control_stack_snapshots_enabled() -> bool {
    MMTK_CPS_CONTROL_STACK_SNAPSHOTS_ENABLED.with(|enabled| *enabled.borrow())
}

pub(crate) fn allocate_mmtk_cps_control_stack_snapshot_i64(
    item_count: usize,
    raw_trace_words: &[i64],
) -> Option<i64> {
    allocate_mmtk_cps_control_stack_chunk_i64(item_count, 0, raw_trace_words)
}

pub(crate) fn allocate_mmtk_cps_control_stack_chunk_i64(
    item_count: usize,
    parent: i64,
    raw_trace_words: &[i64],
) -> Option<i64> {
    if !mmtk_cps_control_stack_snapshots_enabled() {
        return None;
    }
    with_mmtk_cps_context(|context| {
        let parent = if parent == 0 {
            None
        } else {
            let value = YValue::from_raw(parent as usize);
            let raw = value.heap_reference_raw()?;
            let heap = context.context().heap();
            if !heap.may_be_tracked_object_raw(raw) || !heap.objects.contains_key(&raw) {
                return None;
            }
            Some(value)
        };
        let trace_slots = context
            .context()
            .heap()
            .control_stack_trace_slots(parent, raw_trace_words);
        if trace_slots.is_empty() {
            return None;
        }
        if trace_slots.len() == usize::from(parent.is_some()) {
            return parent.map(|value| value.raw() as i64);
        }
        Some(
            context
                .context_mut()
                .heap_mut()
                .allocate_compact_control_stack_chunk_with_trace_slots(
                    item_count,
                    parent.is_some(),
                    raw_trace_words,
                    &trace_slots,
                )
                .raw() as i64,
        )
    })
    .flatten()
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_reset_i64() {
    crate::mmtk_cps_control::reset_mmtk_cps_control_state();
    MMTK_CPS_CONTEXT.with(|slot| {
        let ptr = slot.replace(std::ptr::null_mut());
        if !ptr.is_null() {
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }
    });
    MMTK_CPS_TAG_NAMES.with(|names| names.borrow_mut().clear());
    let snapshots_enabled = std::env::var_os("YULANG_MMTK_CPS_CONTROL_STACK_SNAPSHOTS")
        .is_some_and(|value| value == "1");
    MMTK_CPS_CONTROL_STACK_SNAPSHOTS_ENABLED
        .with(|enabled| *enabled.borrow_mut() = snapshots_enabled);
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_dump_heap_stats_i64() {
    if !std::env::var_os("YULANG_MMTK_CPS_HEAP_STATS").is_some_and(|value| value == "1") {
        return;
    }
    with_mmtk_cps_context(|context| {
        let profile = context.context().heap().allocation_profile();
        eprintln!(
            "[JIT-MMTK-STATS] heap objects={} trace_slots={} raw_payload_bytes={} total_object_bytes={} max_trace_slots={} max_raw_payload_bytes={}",
            profile.objects,
            profile.trace_slots,
            profile.raw_payload_bytes,
            profile.total_object_bytes,
            profile.max_trace_slots,
            profile.max_raw_payload_bytes,
        );
        let storage = profile.storage_summary();
        if !storage.is_empty() {
            eprintln!("[JIT-MMTK-STATS] storage {storage}");
        }
        let kinds = profile.kind_summary();
        if !kinds.is_empty() {
            eprintln!("[JIT-MMTK-STATS] kinds {kinds}");
        }
    });
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_enable_control_stack_i64() {
    MMTK_CPS_CONTROL_STACK_SNAPSHOTS_ENABLED.with(|enabled| *enabled.borrow_mut() = true);
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_disable_control_stack_i64() {
    MMTK_CPS_CONTROL_STACK_SNAPSHOTS_ENABLED.with(|enabled| *enabled.borrow_mut() = false);
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_unit_i64() -> i64 {
    encode_yvalue(YValue::UNIT)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_box_bool_i64(value: i64) -> i64 {
    encode_yvalue(YValue::from_bool(value != 0))
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_concat_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        context.string_concat(decode_yvalue(left), decode_yvalue(right))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_eq_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.string_eq(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(YValue::from_bool)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_len_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.string_len(decode_yvalue(value)))
        .flatten()
        .and_then(context_int_from_usize)
        .unwrap_or(0)
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_slice_range_i64(value: i64, range: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        context.string_slice_range(decode_yvalue(value), decode_yvalue(range))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_string_to_bytes_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.string_to_bytes(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_len_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_len(decode_yvalue(value)))
        .flatten()
        .and_then(context_int_from_usize)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_eq_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_eq(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(YValue::from_bool)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_concat_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_concat(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_slice_range_i64(value: i64, range: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        context.bytes_slice_range(decode_yvalue(value), decode_yvalue(range))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_to_utf8_raw_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_to_utf8_raw(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bytes_to_path_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bytes_to_path(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_path_to_bytes_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.path_to_bytes(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_0() -> i64 {
    with_mmtk_cps_context(MmtkNativeRuntimeContext::tuple_empty)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_1(a: i64) -> i64 {
    let tuple = yulang_mmtk_cps_tuple_i64_0();
    yulang_mmtk_cps_tuple_push_i64(tuple, a)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_2(a: i64, b: i64) -> i64 {
    let tuple = yulang_mmtk_cps_tuple_i64_1(a);
    yulang_mmtk_cps_tuple_push_i64(tuple, b)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_3(a: i64, b: i64, c: i64) -> i64 {
    let tuple = yulang_mmtk_cps_tuple_i64_2(a, b);
    yulang_mmtk_cps_tuple_push_i64(tuple, c)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_i64_4(a: i64, b: i64, c: i64, d: i64) -> i64 {
    let tuple = yulang_mmtk_cps_tuple_i64_3(a, b, c);
    yulang_mmtk_cps_tuple_push_i64(tuple, d)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_tuple_push_i64(tuple: i64, value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.tuple_push(decode_yvalue(tuple), decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_record_empty_i64() -> i64 {
    with_mmtk_cps_context(MmtkNativeRuntimeContext::record_empty)
        .map(encode_yvalue)
        .unwrap_or(0)
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_variant_i64_0(tag: i64) -> i64 {
    let tag = mmtk_cps_tag_name(tag);
    with_mmtk_cps_context(|context| context.variant(tag.as_bytes(), None))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_variant_i64_1(tag: i64, value: i64) -> i64 {
    let tag = mmtk_cps_tag_name(tag);
    with_mmtk_cps_context(|context| context.variant(tag.as_bytes(), Some(decode_yvalue(value))))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_variant_tag_eq_i64(value: i64, tag: i64) -> i64 {
    let tag = mmtk_cps_tag_name(tag);
    with_mmtk_cps_context(|context| context.variant_tag_eq(decode_yvalue(value), tag.as_bytes()))
        .flatten()
        .map(YValue::from_bool)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_variant_payload_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.variant_payload(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_empty_i64() -> i64 {
    with_mmtk_cps_context(MmtkNativeRuntimeContext::list_empty)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_singleton_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.list_singleton(decode_yvalue(value)))
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_merge_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.list_merge(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_len_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.list_len(decode_yvalue(value)))
        .flatten()
        .and_then(context_int_from_usize)
        .unwrap_or(0)
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_slice_range_i64(value: i64, range: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        context.list_slice_range(decode_yvalue(value), decode_yvalue(range))
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_list_view_raw_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.list_view_raw(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_to_string_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_to_string(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_to_hex_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_to_hex(decode_yvalue(value), false))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_to_upper_hex_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_to_hex(decode_yvalue(value), true))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bool_to_string_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| context.bool_to_string(decode_yvalue(value)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_debug_i64(value: i64) -> i64 {
    with_mmtk_cps_context(|context| {
        let text = context.debug_value(decode_yvalue(value));
        context.make_string(text.as_bytes())
    })
    .flatten()
    .map(encode_yvalue)
    .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_print_debug_i64(value: i64) {
    if mmtk_cps_value_needs_prototype_debug(value) {
        unsafe {
            yulang_cps_print_debug_i64(value);
        }
        return;
    }
    let text = with_mmtk_cps_context(|context| context.debug_value(decode_yvalue(value)))
        .unwrap_or_else(|| "<invalid mmtk value>".to_string());
    print!("{text}");
}

fn mmtk_cps_value_needs_prototype_debug(value: i64) -> bool {
    with_mmtk_cps_context(|context| {
        let value = decode_yvalue(value);
        let Some(raw) = value.heap_reference_raw() else {
            return false;
        };
        let heap = context.context().heap();
        !heap.may_be_tracked_object_raw(raw) || !heap.objects.contains_key(&raw)
    })
    .unwrap_or(false)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_out_write_i64(value: i64) -> i64 {
    let text = with_mmtk_cps_context(|context| context.display_value(decode_yvalue(value)))
        .unwrap_or_else(|| "<invalid mmtk value>".to_string());
    print!("{text}");
    let mut stdout = std::io::stdout();
    let _ = std::io::Write::flush(&mut stdout);
    encode_yvalue(YValue::UNIT)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_err_write_i64(value: i64) -> i64 {
    let text = with_mmtk_cps_context(|context| context.display_value(decode_yvalue(value)))
        .unwrap_or_else(|| "<invalid mmtk value>".to_string());
    eprint!("{text}");
    let mut stderr = std::io::stderr();
    let _ = std::io::Write::flush(&mut stderr);
    encode_yvalue(YValue::UNIT)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_warn_write_i64(value: i64) -> i64 {
    let text = with_mmtk_cps_context(|context| context.display_value(decode_yvalue(value)))
        .unwrap_or_else(|| "<invalid mmtk value>".to_string());
    eprintln!("warning: {text}");
    encode_yvalue(YValue::UNIT)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_die_i64(value: i64) -> i64 {
    let text = with_mmtk_cps_context(|context| context.display_value(decode_yvalue(value)))
        .unwrap_or_else(|| "<invalid mmtk value>".to_string());
    eprintln!("die: {text}");
    std::process::exit(1);
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_float_to_string_f64(value: f64) -> i64 {
    with_mmtk_cps_context(|context| context.float_to_string(value))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bool_not_i64(value: i64) -> i64 {
    let value = decode_yvalue(value).as_bool().map(|value| !value);
    value.map(YValue::from_bool).map(encode_yvalue).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bool_eq_i64(left: i64, right: i64) -> i64 {
    let value = decode_yvalue(left)
        .as_bool()
        .zip(decode_yvalue(right).as_bool())
        .map(|(left, right)| left == right);
    value.map(YValue::from_bool).map(encode_yvalue).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_bool_truthy_i64(value: i64) -> i64 {
    decode_yvalue(value).as_bool().map(i64::from).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_add_i64(left: i64, right: i64) -> i64 {
    if let Some(value) = raw_i63(left)
        .zip(raw_i63(right))
        .and_then(|(left, right)| left.checked_add(right))
        .and_then(encode_raw_i63)
    {
        return value;
    }
    with_mmtk_cps_context(|context| context.int_add(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_sub_i64(left: i64, right: i64) -> i64 {
    if let Some(value) = raw_i63(left)
        .zip(raw_i63(right))
        .and_then(|(left, right)| left.checked_sub(right))
        .and_then(encode_raw_i63)
    {
        return value;
    }
    with_mmtk_cps_context(|context| context.int_sub(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_mul_i64(left: i64, right: i64) -> i64 {
    if let Some(value) = raw_i63(left)
        .zip(raw_i63(right))
        .and_then(|(left, right)| {
            let value = i128::from(left) * i128::from(right);
            i64::try_from(value).ok()
        })
        .and_then(encode_raw_i63)
    {
        return value;
    }
    with_mmtk_cps_context(|context| context.int_mul(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_div_i64(left: i64, right: i64) -> i64 {
    with_mmtk_cps_context(|context| context.int_div(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_eq_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| {
        ordering == std::cmp::Ordering::Equal
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_lt_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| ordering == std::cmp::Ordering::Less)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_le_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| {
        ordering != std::cmp::Ordering::Greater
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_gt_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| {
        ordering == std::cmp::Ordering::Greater
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_int_ge_i64(left: i64, right: i64) -> i64 {
    mmtk_cps_int_compare_pred(left, right, |ordering| ordering != std::cmp::Ordering::Less)
}

fn mmtk_cps_int_compare_pred(
    left: i64,
    right: i64,
    pred: impl FnOnce(std::cmp::Ordering) -> bool,
) -> i64 {
    if let Some((left, right)) = raw_i63(left).zip(raw_i63(right)) {
        return encode_raw_bool(pred(left.cmp(&right)));
    }
    with_mmtk_cps_context(|context| context.int_compare(decode_yvalue(left), decode_yvalue(right)))
        .flatten()
        .map(pred)
        .map(YValue::from_bool)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_gc_control_empty_state_i64() -> i64 {
    with_mmtk_cps_context(MmtkNativeRuntimeContext::gc_control_empty_state)
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_gc_control_push_guard_i64(state: i64, guard_id: i64) -> i64 {
    with_mmtk_cps_context(|context| context.gc_control_push_guard(decode_yvalue(state), guard_id))
        .flatten()
        .map(encode_yvalue)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_gc_control_find_guard_i64(state: i64, guard_id: i64) -> i64 {
    with_mmtk_cps_context(|context| context.gc_control_find_guard(decode_yvalue(state), guard_id))
        .flatten()
        .map(encode_raw_bool)
        .unwrap_or(YVALUE_FALSE_BITS)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_gc_control_peek_guard_i64(state: i64) -> i64 {
    with_mmtk_cps_context(|context| context.gc_control_peek_guard(decode_yvalue(state)))
        .flatten()
        .and_then(context_int_from_i64)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_context_new() -> *mut MmtkNativeRuntimeContext {
    MmtkNativeRuntimeContext::new_no_gc()
        .map(Box::new)
        .map(Box::into_raw)
        .unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_context_free(context: *mut MmtkNativeRuntimeContext) {
    if !context.is_null() {
        unsafe {
            drop(Box::from_raw(context));
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_make_unit(context: *mut MmtkNativeRuntimeContext) -> i64 {
    let Some(context) = (unsafe { context.as_ref() }) else {
        return 0;
    };
    encode_yvalue(context.make_unit())
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_tuple_empty(context: *mut MmtkNativeRuntimeContext) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    encode_yvalue(context.tuple_empty())
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_record_empty(context: *mut MmtkNativeRuntimeContext) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    encode_yvalue(context.record_empty())
}

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

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_native_list_empty(context: *mut MmtkNativeRuntimeContext) -> i64 {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return 0;
    };
    encode_yvalue(context.list_empty())
}

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

#[cfg(test)]
pub(crate) fn mmtk_test_lock() -> std::sync::MutexGuard<'static, ()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    LOCK.lock().unwrap_or_else(|poison| poison.into_inner())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn encoded_i63(value: i64) -> i64 {
        encode_yvalue(YValue::from_i63(value).expect("test integer should fit i63"))
    }
    fn encoded_bool(value: bool) -> i64 {
        encode_yvalue(YValue::from_bool(value))
    }
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
    #[test]
    fn mmtk_runtime_boundary_builds_yulang_nogc_binding() {
        let _guard = mmtk_test_lock();
        let boundary = MmtkRuntimeBoundary::new(MmtkRuntimeConfig::prototype_no_gc());

        let _mmtk = boundary
            .build_yulang_mmtk()
            .expect("NoGC prototype config should build a Yulang MMTk binding");
    }
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
        let profile = context.heap().allocation_profile();
        assert_eq!(profile.objects, 4);
        assert_eq!(profile.trace_slots, 3);
        assert_eq!(
            profile.by_kind[&YObjectKind::String].objects,
            stats.allocated_by_kind[&YObjectKind::String]
        );
        assert_eq!(profile.by_kind[&YObjectKind::Tuple].trace_slots, 2);
        assert_eq!(profile.by_storage.get("semantic"), Some(&profile.objects));
        assert!(profile.raw_payload_bytes >= 4 * std::mem::size_of::<YObject>());
        assert!(profile.total_object_bytes >= profile.raw_payload_bytes);

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

    #[test]
    fn mmtk_heap_supports_control_stack_snapshots() {
        let _guard = mmtk_test_lock();
        use crate::gc_runtime::{GcRuntimeContext, YObjectKind};

        let heap = MmtkHeap::new_no_gc().expect("NoGC MMTk heap should initialize");
        let mut context = GcRuntimeContext::with_heap(heap);
        let captured = context.alloc_string("captured");
        let non_mmtk_pointer_shaped_word = 0x1000_i64;
        let stack = context.heap_mut().allocate_compact_control_stack_snapshot(
            3,
            &[captured.raw() as i64, 7, non_mmtk_pointer_shaped_word],
        );
        context.root_stack_mut().push(stack);

        assert!(context.object(stack).is_none());
        assert_eq!(
            context.heap().object_header(stack).map(|h| h.kind),
            Some(YObjectKind::ControlStack)
        );
        assert_eq!(context.heap().trace_children(stack), Some(vec![captured]));
        assert_eq!(
            context
                .heap()
                .raw_payload_bytes(stack)
                .and_then(|bytes| bytes.first().copied()),
            Some(COMPACT_CONTROL_STACK_TAG)
        );

        let next = context.heap_mut().allocate_compact_control_stack_chunk(
            4,
            Some(stack),
            &[captured.raw() as i64],
        );
        assert_eq!(
            context.heap().trace_children(next),
            Some(vec![stack, captured])
        );

        let stats = context.heap_stats();
        assert_eq!(stats.allocated_objects, 3);
        assert_eq!(stats.allocated_trace_slots, 3);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::ControlStack], 2);

        let trace = context.trace_roots();
        assert_eq!(
            trace
                .iter()
                .map(|edge| edge.object_kind)
                .collect::<Vec<_>>(),
            vec![YObjectKind::ControlStack, YObjectKind::String]
        );
    }

    #[test]
    fn mmtk_cps_control_stack_skips_chunks_without_new_heap_children() {
        let _guard = mmtk_test_lock();

        yulang_mmtk_cps_reset_i64();
        yulang_mmtk_cps_enable_control_stack_i64();
        assert_eq!(allocate_mmtk_cps_control_stack_chunk_i64(1, 0, &[7]), None);

        let captured = with_mmtk_cps_context(|context| {
            context
                .make_string(b"captured")
                .expect("string should allocate")
                .raw() as i64
        })
        .expect("MMTk context should initialize");
        let first = allocate_mmtk_cps_control_stack_chunk_i64(1, 0, &[captured])
            .expect("heap child should allocate a control stack chunk");
        let second = allocate_mmtk_cps_control_stack_chunk_i64(2, first, &[11])
            .expect("parent chunk should remain as the top GC root");

        assert_eq!(second, first);
    }

    #[test]
    fn mmtk_heap_supports_gc_control_state_and_thunk_payloads() {
        let _guard = mmtk_test_lock();
        use crate::gc_runtime::{GcRuntimeContext, YObjectKind, YValue};

        let heap = MmtkHeap::new_no_gc().expect("NoGC MMTk heap should initialize");
        let mut context = GcRuntimeContext::with_heap(heap);
        let captured = context.alloc_string("captured");
        let guards = context
            .heap_mut()
            .allocate_compact_control_stack_snapshot(2, &[7, 11]);
        let returns = context
            .heap_mut()
            .allocate_compact_control_stack_snapshot(1, &[captured.raw() as i64]);
        let state = context
            .heap_mut()
            .allocate_gc_control_state(GcControlStateParts {
                handler_stack: YValue::UNIT,
                guard_stack: guards,
                return_frames: returns,
                active_blocked: YValue::UNIT,
            });
        let thunk = context.heap_mut().allocate_gc_control_thunk_i64(
            0x1234,
            state,
            &[captured.raw() as i64, 99],
        );
        context.root_stack_mut().push(thunk);

        let state_parts = context
            .heap()
            .gc_control_state_parts(state)
            .expect("control state should decode");
        assert_eq!(state_parts.guard_stack, guards);
        assert_eq!(state_parts.return_frames, returns);

        let thunk_parts = context
            .heap()
            .gc_control_thunk_parts_i64(thunk)
            .expect("gc control thunk should decode");
        assert_eq!(thunk_parts.code, 0x1234);
        assert_eq!(thunk_parts.context, state);
        assert_eq!(thunk_parts.env_len, 2);
        let thunk_env = unsafe { std::slice::from_raw_parts(thunk_parts.env_ptr, 2) };
        assert_eq!(thunk_env, &[captured.raw() as i64, 99]);

        assert_eq!(
            context.heap().trace_children(state),
            Some(vec![guards, returns])
        );
        assert_eq!(
            context.heap().trace_children(thunk),
            Some(vec![state, captured])
        );

        let empty = context
            .heap_mut()
            .allocate_gc_control_state(GcControlStateParts {
                handler_stack: YValue::UNIT,
                guard_stack: YValue::UNIT,
                return_frames: YValue::UNIT,
                active_blocked: YValue::UNIT,
            });
        let empty_parts = context
            .heap()
            .gc_control_state_parts(empty)
            .expect("empty control state should decode");
        assert_eq!(
            context
                .heap()
                .gc_control_guard_stack_peek(empty_parts.guard_stack),
            None
        );
        assert!(
            !context
                .heap()
                .gc_control_guard_stack_contains(empty_parts.guard_stack, 7)
        );
        let first_guard = context
            .heap_mut()
            .allocate_gc_control_guard_stack_push(empty_parts.guard_stack, 7);
        let second_guard = context
            .heap_mut()
            .allocate_gc_control_guard_stack_push(first_guard, 11);
        assert_eq!(
            context.heap().gc_control_guard_stack_peek(second_guard),
            Some(11)
        );
        assert!(
            context
                .heap()
                .gc_control_guard_stack_contains(second_guard, 7)
        );
        assert!(
            !context
                .heap()
                .gc_control_guard_stack_contains(second_guard, 13)
        );

        let trace = context.trace_roots();
        assert_eq!(
            trace
                .iter()
                .map(|edge| edge.object_kind)
                .collect::<Vec<_>>(),
            vec![
                YObjectKind::Thunk,
                YObjectKind::ControlState,
                YObjectKind::ControlStack,
                YObjectKind::ControlStack,
                YObjectKind::String,
            ]
        );
    }

    #[test]
    fn mmtk_gc_control_guard_helpers_use_explicit_state() {
        let _guard = mmtk_test_lock();
        yulang_mmtk_cps_reset_i64();

        let empty = yulang_mmtk_gc_control_empty_state_i64();
        assert_ne!(empty, 0);
        assert_eq!(
            yulang_mmtk_gc_control_find_guard_i64(empty, 7),
            YVALUE_FALSE_BITS
        );
        assert_eq!(yulang_mmtk_gc_control_peek_guard_i64(empty), 0);

        let guarded = yulang_mmtk_gc_control_push_guard_i64(empty, 7);
        let guarded = yulang_mmtk_gc_control_push_guard_i64(guarded, 11);
        assert_ne!(guarded, 0);
        assert_eq!(
            yulang_mmtk_gc_control_find_guard_i64(guarded, 7),
            YVALUE_TRUE_BITS
        );
        assert_eq!(
            yulang_mmtk_gc_control_find_guard_i64(guarded, 13),
            YVALUE_FALSE_BITS
        );
        assert_eq!(
            yulang_mmtk_gc_control_peek_guard_i64(guarded),
            context_int_from_i64(11).expect("guard id should fit i63")
        );
    }

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
        assert_eq!(
            runtime
                .context()
                .heap()
                .raw_payload_bytes(tuple)
                .and_then(|bytes| bytes.first().copied()),
            Some(COMPACT_TUPLE_TAG)
        );
        assert_eq!(
            runtime.context().heap().trace_children(tuple),
            Some(vec![hello, forty_two])
        );
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
        assert_eq!(
            runtime
                .context()
                .heap()
                .raw_payload_bytes(record)
                .and_then(|bytes| bytes.first().copied()),
            Some(COMPACT_RECORD_TAG)
        );
        assert_eq!(
            runtime.context().heap().trace_children(record),
            Some(vec![greeting, forty_two])
        );
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
            runtime
                .context()
                .heap()
                .raw_payload_bytes(variant)
                .and_then(|bytes| bytes.first().copied()),
            Some(COMPACT_VARIANT_TAG)
        );
        assert_eq!(
            runtime.context().heap().trace_children(variant),
            Some(vec![record])
        );
        assert_eq!(runtime.variant_tag_eq(variant, b"some"), Some(true));
        assert_eq!(runtime.variant_payload(variant), Some(record));
        assert_eq!(runtime.debug_value(sum), "84");
        assert_eq!(runtime.debug_value(tuple), "(\"hello\", 42)");
        assert_eq!(runtime.debug_value(list), "[\"hello\", 42]");
        assert_eq!(runtime.context().heap_stats().allocated_objects, 38);
    }
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

    #[test]
    fn mmtk_gc_control_guard_helpers_can_be_called_from_jit() {
        use cranelift_codegen::ir::{AbiParam, InstBuilder, condcodes, types};
        use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
        use cranelift_jit::{JITBuilder, JITModule};
        use cranelift_module::{Linkage, Module};

        let _guard = mmtk_test_lock();

        let mut jit_builder =
            JITBuilder::new(cranelift_module::default_libcall_names()).expect("JIT builder");
        register_mmtk_cps_jit_symbols(&mut jit_builder);
        let mut module = JITModule::new(jit_builder);

        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));
        let root = module
            .declare_function("mmtk_gc_control_guard_smoke", Linkage::Export, &sig)
            .expect("declare guard smoke root");

        let mut ctx = module.make_context();
        ctx.func.signature = sig;

        let mut builder_context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
        let entry = builder.create_block();
        let found_block = builder.create_block();
        let missing_block = builder.create_block();
        builder.switch_to_block(entry);

        let reset = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_cps_reset_i64",
            &[],
            &[],
        );
        let empty_state = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_gc_control_empty_state_i64",
            &[],
            &[types::I64],
        );
        let push_guard = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_gc_control_push_guard_i64",
            &[types::I64, types::I64],
            &[types::I64],
        );
        let find_guard = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_gc_control_find_guard_i64",
            &[types::I64, types::I64],
            &[types::I64],
        );
        let peek_guard = declare_jit_import(
            &mut module,
            &mut builder,
            "yulang_mmtk_gc_control_peek_guard_i64",
            &[types::I64],
            &[types::I64],
        );

        builder.ins().call(reset, &[]);
        let state = call_jit_i64(&mut builder, empty_state, &[]);
        let guard_7 = builder.ins().iconst(types::I64, 7);
        let state = call_jit_i64(&mut builder, push_guard, &[state, guard_7]);
        let guard_11 = builder.ins().iconst(types::I64, 11);
        let state = call_jit_i64(&mut builder, push_guard, &[state, guard_11]);
        let found = call_jit_i64(&mut builder, find_guard, &[state, guard_7]);
        let true_bits = builder.ins().iconst(types::I64, YVALUE_TRUE_BITS);
        let is_found = builder
            .ins()
            .icmp(condcodes::IntCC::Equal, found, true_bits);
        builder
            .ins()
            .brif(is_found, found_block, &[], missing_block, &[]);

        builder.switch_to_block(found_block);
        let top_guard = call_jit_i64(&mut builder, peek_guard, &[state]);
        builder.ins().return_(&[top_guard]);

        builder.switch_to_block(missing_block);
        let missing = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[missing]);
        builder.seal_all_blocks();
        builder.finalize();

        module
            .define_function(root, &mut ctx)
            .expect("define guard smoke root");
        module.clear_context(&mut ctx);
        module.finalize_definitions().expect("finalize JIT module");

        let ptr = module.get_finalized_function(root);
        let run = unsafe { std::mem::transmute::<_, extern "C" fn() -> i64>(ptr) };

        assert_eq!(run(), encoded_i63(11));
    }
}
