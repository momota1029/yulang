//! Isolated native GC runtime model.
//!
//! This module is the pre-integration boundary for the post-prototype native
//! runtime. It does not replace the current `VmValue` helper path yet. Its job
//! is to pin down the value word, object header, tracing surface, and explicit
//! root discipline that the MMTk-backed runtime will use.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::ptr::NonNull;
use std::sync::Arc;

#[derive(Debug, Default)]
pub struct GcRuntimeContext<H: YHeap = SpikeHeap> {
    heap: H,
    layouts: NativeLayoutRegistry,
    symbols: YSymbolTable,
    roots: YRootStack,
    stress_collect_every_allocation: bool,
    stress_collections: usize,
}

impl GcRuntimeContext<SpikeHeap> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<H: YHeap> GcRuntimeContext<H> {
    pub fn with_heap(heap: H) -> Self {
        Self {
            heap,
            layouts: NativeLayoutRegistry::default(),
            symbols: YSymbolTable::default(),
            roots: YRootStack::default(),
            stress_collect_every_allocation: false,
            stress_collections: 0,
        }
    }

    pub fn enable_collect_every_allocation(&mut self) {
        self.stress_collect_every_allocation = true;
    }

    pub fn heap(&self) -> &H {
        &self.heap
    }

    pub fn heap_mut(&mut self) -> &mut H {
        &mut self.heap
    }

    pub fn heap_stats(&self) -> YHeapStats {
        self.heap.stats()
    }

    pub fn intern_native_layout(&mut self, layout: NativeLayout) -> NativeLayoutHandle {
        self.layouts.intern(layout)
    }

    pub fn native_layout_count(&self) -> usize {
        self.layouts.len()
    }

    pub fn intern_symbol_path(&mut self, path: impl Into<YSymbolPath>) -> YSymbolId {
        self.symbols.intern(path)
    }

    pub fn symbol(&self, id: YSymbolId) -> Option<&YSymbol> {
        self.symbols.symbol(id)
    }

    pub fn symbol_table(&self) -> &YSymbolTable {
        &self.symbols
    }

    pub fn stress_collection_count(&self) -> usize {
        self.stress_collections
    }

    pub fn root_stack(&self) -> &YRootStack {
        &self.roots
    }

    pub fn root_stack_mut(&mut self) -> &mut YRootStack {
        &mut self.roots
    }

    pub fn with_root_frame<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let frame = self.roots.push_frame();
        let result = f(self);
        self.roots
            .pop_frame(frame)
            .expect("root frame should remain valid while helper runs");
        result
    }

    pub fn with_temporary_roots<R>(
        &mut self,
        values: impl IntoIterator<Item = YValue>,
        f: impl FnOnce(&mut Self, &[YRoot]) -> R,
    ) -> R {
        let frame = self.roots.push_frame();
        let roots = values
            .into_iter()
            .map(|value| self.roots.push(value))
            .collect::<Vec<_>>();
        let result = f(self, &roots);
        self.roots
            .pop_frame(frame)
            .expect("temporary root frame should remain valid while helper runs");
        result
    }

    pub fn alloc_object(&mut self, payload: YObjectPayload) -> YValue {
        self.collect_if_requested();
        let object = Box::new(YObject::new(payload));
        let ptr = NonNull::from(object.as_ref());
        debug_assert!(YValue::heap_ptr_is_aligned(ptr.cast()));
        self.heap.allocate_boxed(object)
    }

    pub fn alloc_big_int(&mut self, decimal: impl Into<String>) -> YValue {
        self.alloc_object(YObjectPayload::BigInt(decimal.into()))
    }

    pub fn alloc_int_text(&mut self, decimal: impl AsRef<str>) -> Option<YValue> {
        let decimal = decimal.as_ref();
        if let Ok(value) = decimal.parse::<i64>() {
            if let Some(value) = YValue::from_i63(value) {
                return Some(value);
            }
        }
        decimal
            .parse::<i128>()
            .ok()
            .map(|_| self.alloc_big_int(decimal.to_string()))
    }

    pub fn alloc_string(&mut self, value: impl Into<String>) -> YValue {
        self.alloc_object(YObjectPayload::String(YString::flat(value)))
    }

    pub fn alloc_bytes(&mut self, value: impl Into<Box<[u8]>>) -> YValue {
        self.alloc_object(YObjectPayload::Bytes(value.into()))
    }

    pub fn alloc_path(&mut self, value: impl AsRef<Path>) -> YValue {
        self.alloc_object(YObjectPayload::Path(value.as_ref().to_path_buf()))
    }

    pub fn alloc_string_concat(&mut self, left: YValue, right: YValue) -> YValue {
        self.alloc_object(YObjectPayload::String(YString::Concat { left, right }))
    }

    pub fn alloc_string_slice(&mut self, source: YValue, start: usize, end: usize) -> YValue {
        self.alloc_object(YObjectPayload::String(YString::Slice {
            source,
            start,
            end,
        }))
    }

    pub fn alloc_tuple(&mut self, items: impl Into<Box<[YValue]>>) -> YValue {
        self.alloc_object(YObjectPayload::Tuple(items.into()))
    }

    pub fn alloc_native_block(
        &mut self,
        layout: NativeLayout,
        fields: impl Into<Box<[NativeFieldValue]>>,
    ) -> Result<YValue, NativeLayoutError> {
        let layout = self.intern_native_layout(layout);
        self.alloc_native_block_with_layout(layout, fields)
    }

    pub fn alloc_native_block_with_layout(
        &mut self,
        layout: NativeLayoutHandle,
        fields: impl Into<Box<[NativeFieldValue]>>,
    ) -> Result<YValue, NativeLayoutError> {
        let block = NativeHeapBlock::new(layout, fields)?;
        Ok(self.alloc_object(YObjectPayload::NativeHeapBlock(block)))
    }

    pub fn alloc_record(&mut self, fields: impl Into<Box<[(Box<str>, YValue)]>>) -> YValue {
        self.alloc_object(YObjectPayload::Record(fields.into()))
    }

    pub fn alloc_variant(&mut self, tag: impl Into<Box<str>>, value: Option<YValue>) -> YValue {
        self.alloc_object(YObjectPayload::Variant {
            tag: tag.into(),
            value,
        })
    }

    pub fn alloc_symbolic_variant(&mut self, tag: YSymbolId, value: Option<YValue>) -> YValue {
        self.alloc_object(YObjectPayload::SymbolicVariant { tag, value })
    }

    pub fn alloc_native_variant(
        &mut self,
        layout: NativeLayout,
        tag: YSymbolId,
        payload_fields: impl Into<Box<[NativeFieldValue]>>,
    ) -> Result<YValue, NativeLayoutError> {
        let layout = self.intern_native_layout(layout);
        self.alloc_native_variant_with_layout(layout, tag, payload_fields)
    }

    pub fn alloc_native_variant_with_layout(
        &mut self,
        layout: NativeLayoutHandle,
        tag: YSymbolId,
        payload_fields: impl Into<Box<[NativeFieldValue]>>,
    ) -> Result<YValue, NativeLayoutError> {
        let mut fields = Vec::with_capacity(layout.layout().fields.len());
        fields.push(NativeFieldValue::Symbol(tag));
        fields.extend(payload_fields.into());
        self.alloc_native_block_with_layout(layout, fields)
    }

    pub fn alloc_list(&mut self, items: impl Into<Box<[YValue]>>) -> YValue {
        self.alloc_object(YObjectPayload::List(YList::flat(items)))
    }

    pub fn alloc_list_concat(&mut self, left: YValue, right: YValue) -> YValue {
        self.alloc_object(YObjectPayload::List(YList::Concat { left, right }))
    }

    pub fn alloc_list_slice(&mut self, source: YValue, start: usize, end: usize) -> YValue {
        self.alloc_object(YObjectPayload::List(YList::Slice { source, start, end }))
    }

    pub fn alloc_closure(&mut self, code: usize, env: impl Into<Box<[YValue]>>) -> YValue {
        self.alloc_object(YObjectPayload::Closure {
            code,
            env: env.into(),
        })
    }

    pub fn alloc_thunk(&mut self, code: usize, env: impl Into<Box<[YValue]>>) -> YValue {
        self.alloc_object(YObjectPayload::Thunk {
            code,
            env: env.into(),
        })
    }

    pub fn alloc_resumption(&mut self, code: usize, env: impl Into<Box<[YValue]>>) -> YValue {
        self.alloc_object(YObjectPayload::Resumption {
            code,
            env: env.into(),
        })
    }

    pub fn alloc_continuation_env(&mut self, slots: impl Into<Box<[YValue]>>) -> YValue {
        self.alloc_object(YObjectPayload::ContinuationEnv(slots.into()))
    }

    pub fn alloc_handler_frame(&mut self, prompt: u64, env: impl Into<Box<[YValue]>>) -> YValue {
        self.alloc_object(YObjectPayload::HandlerFrame {
            prompt,
            env: env.into(),
        })
    }

    pub fn alloc_return_frame(
        &mut self,
        continuation: usize,
        env: impl Into<Box<[YValue]>>,
    ) -> YValue {
        self.alloc_object(YObjectPayload::ReturnFrame {
            continuation,
            env: env.into(),
        })
    }

    pub fn checked_add_int(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        let left = self.int_to_i128(left)?;
        let right = self.int_to_i128(right)?;
        Some(self.int_from_i128(left + right))
    }

    pub fn checked_sub_int(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        let left = self.int_to_i128(left)?;
        let right = self.int_to_i128(right)?;
        Some(self.int_from_i128(left - right))
    }

    pub fn checked_mul_int(&mut self, left: YValue, right: YValue) -> Option<YValue> {
        let left = self.int_to_i128(left)?;
        let right = self.int_to_i128(right)?;
        Some(self.int_from_i128(left * right))
    }

    pub fn compare_int(&self, left: YValue, right: YValue) -> Option<Ordering> {
        Some(self.int_to_i128(left)?.cmp(&self.int_to_i128(right)?))
    }

    pub fn object(&self, value: YValue) -> Option<&YObject> {
        self.heap.object(value)
    }

    pub fn trace_roots(&self) -> Vec<YTraceEdge> {
        self.heap.trace_roots(self.roots.values())
    }

    pub fn trace_root_report(&self) -> YTraceReport {
        let edges = self.trace_roots();
        YTraceReport::from_edges(self.roots.values().len(), edges, |value| {
            self.object(value)
                .map(|object| object.header().trace_slots)
                .unwrap_or(0)
        })
    }

    pub fn debug_value(&self, value: YValue) -> String {
        match value.kind() {
            YValueKind::I63 => value.as_i63().expect("i63 value should decode").to_string(),
            YValueKind::Bool => value
                .as_bool()
                .expect("bool value should decode")
                .to_string(),
            YValueKind::Unit => "()".to_string(),
            YValueKind::HeapRef => self
                .object(value)
                .map(|object| object.debug_value(self))
                .unwrap_or_else(|| "<dangling heap object>".to_string()),
        }
    }

    fn collect_if_requested(&mut self) {
        if !self.stress_collect_every_allocation {
            return;
        }
        self.stress_collections += 1;
        let _ = self.trace_roots();
    }

    fn int_from_i128(&mut self, value: i128) -> YValue {
        i64::try_from(value)
            .ok()
            .and_then(YValue::from_i63)
            .unwrap_or_else(|| self.alloc_big_int(value.to_string()))
    }

    fn int_to_i128(&self, value: YValue) -> Option<i128> {
        if let Some(value) = value.as_i63() {
            return Some(value as i128);
        }
        let object = self.object(value)?;
        let YObjectPayload::BigInt(value) = object.payload() else {
            return None;
        };
        value.parse().ok()
    }
}

pub trait YHeap: fmt::Debug {
    fn allocate_boxed(&mut self, object: Box<YObject>) -> YValue;
    fn object(&self, value: YValue) -> Option<&YObject>;
    fn stats(&self) -> YHeapStats;

    fn object_header(&self, value: YValue) -> Option<YObjectHeader> {
        self.object(value).map(YObject::header)
    }

    fn trace_children(&self, value: YValue) -> Option<Vec<YValue>> {
        self.object(value).map(YObject::trace_children)
    }

    fn trace_roots(&self, roots: &[YValue]) -> Vec<YTraceEdge> {
        let mut tracer = YTracer::default();
        for (slot, value) in roots.iter().copied().enumerate() {
            tracer.trace_value(YTraceOrigin::Root(slot), value, self);
        }
        tracer.finish()
    }
}

#[derive(Debug, Default)]
pub struct SpikeHeap {
    objects: Vec<Box<YObject>>,
}

impl SpikeHeap {
    pub fn object_count(&self) -> usize {
        self.objects.len()
    }
}

impl YHeap for SpikeHeap {
    fn allocate_boxed(&mut self, object: Box<YObject>) -> YValue {
        let ptr = NonNull::from(object.as_ref());
        debug_assert!(YValue::heap_ptr_is_aligned(ptr.cast()));
        self.objects.push(object);
        YValue::from_heap_ptr(ptr)
    }

    fn object(&self, value: YValue) -> Option<&YObject> {
        let ptr = value.as_heap_ptr()?;
        self.objects
            .iter()
            .map(Box::as_ref)
            .find(|object| std::ptr::eq(*object, ptr.as_ptr()))
    }

    fn stats(&self) -> YHeapStats {
        YHeapStats::from_objects(self.objects.iter().map(Box::as_ref))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YHeapStats {
    pub allocated_objects: usize,
    pub allocated_trace_slots: usize,
    pub allocated_by_kind: BTreeMap<YObjectKind, usize>,
}

impl YHeapStats {
    pub(crate) fn from_objects<'a>(objects: impl IntoIterator<Item = &'a YObject>) -> Self {
        Self::from_headers(objects.into_iter().map(YObject::header))
    }

    pub(crate) fn from_headers(headers: impl IntoIterator<Item = YObjectHeader>) -> Self {
        let mut stats = Self {
            allocated_objects: 0,
            allocated_trace_slots: 0,
            allocated_by_kind: BTreeMap::new(),
        };
        for header in headers {
            stats.allocated_objects += 1;
            stats.allocated_trace_slots += header.trace_slots;
            *stats.allocated_by_kind.entry(header.kind).or_default() += 1;
        }
        stats
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct YSymbolTable {
    symbols: Vec<YSymbol>,
    by_path: BTreeMap<YSymbolPath, YSymbolId>,
    by_hash: BTreeMap<u64, Vec<YSymbolId>>,
}

impl YSymbolTable {
    pub fn from_static_symbols(paths: impl IntoIterator<Item = YSymbolPath>) -> Self {
        Self::from_static_paths(paths)
    }

    pub fn from_static_paths(paths: impl IntoIterator<Item = YSymbolPath>) -> Self {
        let mut table = Self::default();
        for path in paths.into_iter().collect::<BTreeSet<_>>() {
            table.intern(path);
        }
        table
    }

    pub fn intern(&mut self, path: impl Into<YSymbolPath>) -> YSymbolId {
        let path = path.into();
        if let Some(id) = self.by_path.get(&path) {
            return *id;
        }

        let id = YSymbolId(
            u32::try_from(self.symbols.len()).expect("symbol table should fit in u32 ids"),
        );
        let hash = path.stable_hash();
        self.by_path.insert(path.clone(), id);
        self.by_hash.entry(hash).or_default().push(id);
        self.symbols.push(YSymbol { id, hash, path });
        id
    }

    pub fn symbol(&self, id: YSymbolId) -> Option<&YSymbol> {
        self.symbols.get(id.0 as usize)
    }

    pub fn id_for_path(&self, path: &YSymbolPath) -> Option<YSymbolId> {
        self.by_path.get(path).copied()
    }

    pub fn ids_for_hash(&self, hash: u64) -> &[YSymbolId] {
        self.by_hash.get(&hash).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn freeze_perfect_hash(&self) -> Result<YPerfectSymbolHash, YSymbolHashCollision> {
        let mut by_hash = BTreeMap::new();
        for (hash, ids) in &self.by_hash {
            match ids.as_slice() {
                [id] => {
                    by_hash.insert(*hash, *id);
                }
                [] => {}
                [first, second, ..] => {
                    let symbols = ids
                        .iter()
                        .filter_map(|id| self.symbol(*id))
                        .cloned()
                        .collect::<Vec<_>>();
                    return Err(YSymbolHashCollision {
                        hash: *hash,
                        first: *first,
                        second: *second,
                        symbols,
                    });
                }
            }
        }
        Ok(YPerfectSymbolHash { by_hash })
    }

    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YSymbol {
    pub id: YSymbolId,
    pub hash: u64,
    pub path: YSymbolPath,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YPerfectSymbolHash {
    by_hash: BTreeMap<u64, YSymbolId>,
}

impl YPerfectSymbolHash {
    pub fn lookup(&self, hash: u64) -> Option<YSymbolId> {
        self.by_hash.get(&hash).copied()
    }

    pub fn len(&self) -> usize {
        self.by_hash.len()
    }

    pub fn is_empty(&self) -> bool {
        self.by_hash.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YSymbolHashCollision {
    pub hash: u64,
    pub first: YSymbolId,
    pub second: YSymbolId,
    pub symbols: Vec<YSymbol>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct YSymbolPath {
    key: YSymbolKey,
}

impl YSymbolPath {
    pub fn new(segments: impl IntoIterator<Item = impl Into<Box<str>>>) -> Self {
        Self::path(segments)
    }

    pub fn path(segments: impl IntoIterator<Item = impl Into<Box<str>>>) -> Self {
        Self {
            key: YSymbolKey::Path(
                segments
                    .into_iter()
                    .map(Into::into)
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            ),
        }
    }

    pub fn atom(text: impl Into<Box<str>>) -> Self {
        Self {
            key: YSymbolKey::Atom(text.into()),
        }
    }

    pub fn from_name(name: impl Into<Box<str>>) -> Self {
        Self::atom(name)
    }

    pub fn path_segments(&self) -> Option<&[Box<str>]> {
        match &self.key {
            YSymbolKey::Path(segments) => Some(segments),
            YSymbolKey::Atom(_) => None,
        }
    }

    pub fn atom_text(&self) -> Option<&str> {
        match &self.key {
            YSymbolKey::Atom(text) => Some(text),
            YSymbolKey::Path(_) => None,
        }
    }

    pub fn display_name(&self) -> String {
        match &self.key {
            YSymbolKey::Atom(text) => text.to_string(),
            YSymbolKey::Path(segments) => segments
                .iter()
                .map(|segment| segment.as_ref())
                .collect::<Vec<_>>()
                .join("::"),
        }
    }

    pub fn stable_hash(&self) -> u64 {
        let mut hash = 0xcbf29ce484222325_u64;
        match &self.key {
            YSymbolKey::Atom(text) => {
                update_symbol_hash(&mut hash, 0xa1);
                for byte in text.as_bytes() {
                    update_symbol_hash(&mut hash, *byte);
                }
            }
            YSymbolKey::Path(segments) => {
                update_symbol_hash(&mut hash, 0xa2);
                for segment in segments {
                    for byte in segment.as_bytes() {
                        update_symbol_hash(&mut hash, *byte);
                    }
                    update_symbol_hash(&mut hash, 0xff);
                }
            }
        }
        hash
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum YSymbolKey {
    Atom(Box<str>),
    Path(Box<[Box<str>]>),
}

fn update_symbol_hash(hash: &mut u64, byte: u8) {
    *hash ^= u64::from(byte);
    *hash = hash.wrapping_mul(0x100000001b3);
}

impl From<&str> for YSymbolPath {
    fn from(text: &str) -> Self {
        Self::atom(text)
    }
}

impl From<String> for YSymbolPath {
    fn from(text: String) -> Self {
        Self::atom(text)
    }
}

impl From<Box<str>> for YSymbolPath {
    fn from(text: Box<str>) -> Self {
        Self::atom(text)
    }
}

impl From<Vec<String>> for YSymbolPath {
    fn from(segments: Vec<String>) -> Self {
        Self::path(segments)
    }
}

impl From<Vec<Box<str>>> for YSymbolPath {
    fn from(segments: Vec<Box<str>>) -> Self {
        Self::path(segments)
    }
}

impl From<Vec<&str>> for YSymbolPath {
    fn from(segments: Vec<&str>) -> Self {
        Self::path(segments)
    }
}

impl From<&[&str]> for YSymbolPath {
    fn from(segments: &[&str]) -> Self {
        Self::path(segments.iter().copied())
    }
}

impl From<&[String]> for YSymbolPath {
    fn from(segments: &[String]) -> Self {
        Self::path(segments.iter().cloned())
    }
}

impl From<&[Box<str>]> for YSymbolPath {
    fn from(segments: &[Box<str>]) -> Self {
        Self::path(segments.iter().cloned())
    }
}

impl<const N: usize> From<[&str; N]> for YSymbolPath {
    fn from(segments: [&str; N]) -> Self {
        Self::path(segments)
    }
}

impl From<yulang_typed_ir::Name> for YSymbolPath {
    fn from(name: yulang_typed_ir::Name) -> Self {
        Self::from_name(name.0)
    }
}

impl From<&yulang_typed_ir::Name> for YSymbolPath {
    fn from(name: &yulang_typed_ir::Name) -> Self {
        Self::from_name(name.0.clone())
    }
}

impl From<yulang_typed_ir::Path> for YSymbolPath {
    fn from(path: yulang_typed_ir::Path) -> Self {
        Self::new(path.segments.into_iter().map(|segment| segment.0))
    }
}

impl From<&yulang_typed_ir::Path> for YSymbolPath {
    fn from(path: &yulang_typed_ir::Path) -> Self {
        Self::new(path.segments.iter().map(|segment| segment.0.clone()))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct YSymbolId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeLayout {
    pub kind: NativeLayoutKind,
    pub fields: Box<[NativeFieldLayout]>,
    pub trace_bitmap: YTraceBitmap,
    pub footprint: NativeLayoutFootprint,
}

impl NativeLayout {
    pub fn new(kind: NativeLayoutKind, fields: impl Into<Box<[NativeFieldLayout]>>) -> Self {
        let fields = fields.into();
        let traced_fields = fields
            .iter()
            .enumerate()
            .filter_map(|(index, field)| field.lane.is_traced().then_some(index));
        let trace_bitmap = YTraceBitmap::from_traced_fields(fields.len(), traced_fields);
        let footprint = NativeLayoutFootprint::from_fields(&fields);
        Self {
            kind,
            fields,
            trace_bitmap,
            footprint,
        }
    }

    pub fn tuple(fields: impl Into<Box<[NativeFieldLayout]>>) -> Self {
        Self::new(NativeLayoutKind::Object(YObjectKind::Tuple), fields)
    }

    pub fn variant(payload_fields: impl Into<Box<[NativeFieldLayout]>>) -> Self {
        let payload_fields = payload_fields.into();
        let mut fields = Vec::with_capacity(payload_fields.len() + 1);
        fields.push(NativeFieldLayout::named("tag", NativeFieldLane::Symbol));
        fields.extend(payload_fields.into_vec());
        Self::new(NativeLayoutKind::Object(YObjectKind::Variant), fields)
    }

    pub fn closure_env(fields: impl Into<Box<[NativeFieldLayout]>>) -> Self {
        Self::new(NativeLayoutKind::Object(YObjectKind::Closure), fields)
    }

    pub fn continuation_env(fields: impl Into<Box<[NativeFieldLayout]>>) -> Self {
        Self::new(
            NativeLayoutKind::Object(YObjectKind::ContinuationEnv),
            fields,
        )
    }

    pub fn object_kind(&self) -> Option<YObjectKind> {
        self.kind.object_kind()
    }
}

#[derive(Debug, Default, Clone)]
pub struct NativeLayoutRegistry {
    layouts: Vec<Arc<NativeLayout>>,
}

impl NativeLayoutRegistry {
    pub fn intern(&mut self, layout: NativeLayout) -> NativeLayoutHandle {
        if let Some((index, existing)) = self
            .layouts
            .iter()
            .enumerate()
            .find(|(_, existing)| existing.as_ref() == &layout)
        {
            return NativeLayoutHandle {
                id: NativeLayoutId(index),
                layout: Arc::clone(existing),
            };
        }

        let id = NativeLayoutId(self.layouts.len());
        let layout = Arc::new(layout);
        self.layouts.push(Arc::clone(&layout));
        NativeLayoutHandle { id, layout }
    }

    pub fn len(&self) -> usize {
        self.layouts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.layouts.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeLayoutHandle {
    id: NativeLayoutId,
    layout: Arc<NativeLayout>,
}

impl NativeLayoutHandle {
    #[cfg(feature = "mmtk-runtime")]
    pub(crate) fn ephemeral(id: NativeLayoutId, layout: NativeLayout) -> Self {
        Self {
            id,
            layout: Arc::new(layout),
        }
    }

    pub fn id(&self) -> NativeLayoutId {
        self.id
    }

    pub fn layout(&self) -> &NativeLayout {
        &self.layout
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NativeLayoutId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeLayoutKind {
    Object(YObjectKind),
    StackFrame,
}

impl NativeLayoutKind {
    pub fn object_kind(self) -> Option<YObjectKind> {
        match self {
            Self::Object(kind) => Some(kind),
            Self::StackFrame => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeFieldLayout {
    pub name: Option<Box<str>>,
    pub lane: NativeFieldLane,
}

impl NativeFieldLayout {
    pub fn unnamed(lane: NativeFieldLane) -> Self {
        Self { name: None, lane }
    }

    pub fn named(name: impl Into<Box<str>>, lane: NativeFieldLane) -> Self {
        Self {
            name: Some(name.into()),
            lane,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeFieldLane {
    YValue,
    Symbol,
    I64,
    U64,
    F64,
    Bool,
}

impl NativeFieldLane {
    pub fn is_traced(self) -> bool {
        matches!(self, Self::YValue)
    }

    pub fn size_align(self) -> NativeFieldSizeAlign {
        match self {
            Self::YValue | Self::I64 | Self::U64 | Self::F64 => {
                NativeFieldSizeAlign { size: 8, align: 8 }
            }
            Self::Symbol => NativeFieldSizeAlign { size: 4, align: 4 },
            Self::Bool => NativeFieldSizeAlign { size: 1, align: 1 },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeLayoutFootprint {
    pub field_offsets: Box<[NativeFieldOffset]>,
    pub payload_size: usize,
    pub payload_align: usize,
}

impl NativeLayoutFootprint {
    fn from_fields(fields: &[NativeFieldLayout]) -> Self {
        let mut offset = 0;
        let mut payload_align = 1;
        let mut field_offsets = Vec::with_capacity(fields.len());
        for field in fields {
            let size_align = field.lane.size_align();
            payload_align = payload_align.max(size_align.align);
            offset = align_up(offset, size_align.align);
            field_offsets.push(NativeFieldOffset {
                offset,
                size: size_align.size,
                align: size_align.align,
            });
            offset += size_align.size;
        }
        Self {
            field_offsets: field_offsets.into_boxed_slice(),
            payload_size: align_up(offset, payload_align),
            payload_align,
        }
    }
}

fn align_up(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeFieldOffset {
    pub offset: usize,
    pub size: usize,
    pub align: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeFieldSizeAlign {
    pub size: usize,
    pub align: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeHeapBlock {
    layout: NativeLayoutHandle,
    payload: NativePayloadBuffer,
}

impl NativeHeapBlock {
    pub fn new(
        layout: NativeLayoutHandle,
        fields: impl Into<Box<[NativeFieldValue]>>,
    ) -> Result<Self, NativeLayoutError> {
        let fields = fields.into();
        let layout_ref = layout.layout();
        let Some(_) = layout_ref.object_kind() else {
            return Err(NativeLayoutError::StackFrameIsNotHeapObject);
        };
        if layout_ref.fields.len() != fields.len() {
            return Err(NativeLayoutError::FieldCountMismatch {
                expected: layout_ref.fields.len(),
                actual: fields.len(),
            });
        }
        for (index, (field_layout, value)) in
            layout_ref.fields.iter().zip(fields.iter()).enumerate()
        {
            if field_layout.lane != value.lane() {
                return Err(NativeLayoutError::FieldLaneMismatch {
                    index,
                    expected: field_layout.lane,
                    actual: value.lane(),
                });
            }
        }
        let payload = NativePayloadBuffer::from_fields(layout_ref, &fields);
        Ok(Self { layout, payload })
    }

    pub fn layout(&self) -> &NativeLayoutHandle {
        &self.layout
    }

    pub fn payload(&self) -> &NativePayloadBuffer {
        &self.payload
    }

    pub fn field_value(&self, index: usize) -> NativeFieldValue {
        self.payload
            .read_field(self.layout.layout(), index)
            .expect("native heap block field index should be in layout")
    }

    pub fn variant_tag(&self) -> Option<YSymbolId> {
        if self.object_kind() != YObjectKind::Variant {
            return None;
        }
        match self.field_value(0) {
            NativeFieldValue::Symbol(tag) => Some(tag),
            _ => None,
        }
    }

    pub fn object_kind(&self) -> YObjectKind {
        self.layout
            .layout()
            .object_kind()
            .expect("native heap block should have an object kind")
    }

    pub fn trace_slot_count(&self) -> usize {
        self.layout.layout().trace_bitmap.traced_fields().len()
    }

    pub fn trace_children(&self) -> Vec<YValue> {
        self.layout
            .layout()
            .trace_bitmap
            .traced_fields()
            .into_iter()
            .filter_map(|index| match self.field_value(index) {
                NativeFieldValue::YValue(value) => Some(value),
                _ => None,
            })
            .collect()
    }

    fn debug_value<H: YHeap>(&self, context: &GcRuntimeContext<H>) -> String {
        let fields = (0..self.layout.layout().fields.len())
            .map(|index| self.field_value(index))
            .map(|field| field.debug_value(context))
            .collect::<Vec<_>>();
        format!("<native {} [{}]>", self.object_kind(), fields.join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativePayloadBuffer {
    bytes: Box<[u8]>,
}

impl NativePayloadBuffer {
    fn from_fields(layout: &NativeLayout, fields: &[NativeFieldValue]) -> Self {
        let mut buffer = Self {
            bytes: vec![0; layout.footprint.payload_size].into_boxed_slice(),
        };
        for (index, field) in fields.iter().enumerate() {
            buffer.write_field(layout, index, field);
        }
        buffer
    }

    pub fn from_bytes(bytes: impl Into<Box<[u8]>>) -> Self {
        Self {
            bytes: bytes.into(),
        }
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn read_field(&self, layout: &NativeLayout, index: usize) -> Option<NativeFieldValue> {
        let field_layout = layout.fields.get(index)?;
        let field_offset = layout.footprint.field_offsets.get(index)?;
        let start = field_offset.offset;
        match field_layout.lane {
            NativeFieldLane::YValue => Some(NativeFieldValue::YValue(YValue(read_u64(
                &self.bytes[start..],
            )
                as usize))),
            NativeFieldLane::Symbol => Some(NativeFieldValue::Symbol(YSymbolId(read_u32(
                &self.bytes[start..],
            )))),
            NativeFieldLane::I64 => {
                Some(NativeFieldValue::I64(read_u64(&self.bytes[start..]) as i64))
            }
            NativeFieldLane::U64 => Some(NativeFieldValue::U64(read_u64(&self.bytes[start..]))),
            NativeFieldLane::F64 => Some(NativeFieldValue::F64Bits(read_u64(&self.bytes[start..]))),
            NativeFieldLane::Bool => Some(NativeFieldValue::Bool(self.bytes[start] != 0)),
        }
    }

    fn write_field(&mut self, layout: &NativeLayout, index: usize, field: &NativeFieldValue) {
        let field_offset = &layout.footprint.field_offsets[index];
        let start = field_offset.offset;
        match field {
            NativeFieldValue::YValue(value) => {
                write_u64(&mut self.bytes[start..], value.raw() as u64)
            }
            NativeFieldValue::Symbol(value) => write_u32(&mut self.bytes[start..], value.0),
            NativeFieldValue::I64(value) => write_u64(&mut self.bytes[start..], *value as u64),
            NativeFieldValue::U64(value) | NativeFieldValue::F64Bits(value) => {
                write_u64(&mut self.bytes[start..], *value)
            }
            NativeFieldValue::Bool(value) => self.bytes[start] = u8::from(*value),
        }
    }
}

fn read_u64(bytes: &[u8]) -> u64 {
    u64::from_ne_bytes(
        bytes[..8]
            .try_into()
            .expect("native payload field should have eight bytes"),
    )
}

fn read_u32(bytes: &[u8]) -> u32 {
    u32::from_ne_bytes(
        bytes[..4]
            .try_into()
            .expect("native payload field should have four bytes"),
    )
}

fn write_u64(bytes: &mut [u8], value: u64) {
    bytes[..8].copy_from_slice(&value.to_ne_bytes());
}

fn write_u32(bytes: &mut [u8], value: u32) {
    bytes[..4].copy_from_slice(&value.to_ne_bytes());
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeFieldValue {
    YValue(YValue),
    Symbol(YSymbolId),
    I64(i64),
    U64(u64),
    F64Bits(u64),
    Bool(bool),
}

impl NativeFieldValue {
    pub fn from_f64(value: f64) -> Self {
        Self::F64Bits(value.to_bits())
    }

    pub fn lane(&self) -> NativeFieldLane {
        match self {
            Self::YValue(_) => NativeFieldLane::YValue,
            Self::Symbol(_) => NativeFieldLane::Symbol,
            Self::I64(_) => NativeFieldLane::I64,
            Self::U64(_) => NativeFieldLane::U64,
            Self::F64Bits(_) => NativeFieldLane::F64,
            Self::Bool(_) => NativeFieldLane::Bool,
        }
    }

    fn debug_value<H: YHeap>(&self, context: &GcRuntimeContext<H>) -> String {
        match self {
            Self::YValue(value) => context.debug_value(*value),
            Self::Symbol(value) => context
                .symbol(*value)
                .map(|symbol| format!("'{}", symbol.path.display_name()))
                .unwrap_or_else(|| format!("'#{:?}", value)),
            Self::I64(value) => format!("{value}i64"),
            Self::U64(value) => format!("{value}u64"),
            Self::F64Bits(value) => format!("{}f64", f64::from_bits(*value)),
            Self::Bool(value) => value.to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeLayoutError {
    StackFrameIsNotHeapObject,
    FieldCountMismatch {
        expected: usize,
        actual: usize,
    },
    FieldLaneMismatch {
        index: usize,
        expected: NativeFieldLane,
        actual: NativeFieldLane,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YTraceBitmap {
    field_count: usize,
    words: Box<[u64]>,
}

impl YTraceBitmap {
    const WORD_BITS: usize = u64::BITS as usize;

    pub fn from_traced_fields(
        field_count: usize,
        traced_fields: impl IntoIterator<Item = usize>,
    ) -> Self {
        let mut words = vec![0_u64; field_count.div_ceil(Self::WORD_BITS)];
        for field in traced_fields {
            assert!(field < field_count);
            words[field / Self::WORD_BITS] |= 1_u64 << (field % Self::WORD_BITS);
        }
        Self {
            field_count,
            words: words.into_boxed_slice(),
        }
    }

    pub fn field_count(&self) -> usize {
        self.field_count
    }

    pub fn is_traced(&self, field: usize) -> bool {
        assert!(field < self.field_count);
        self.words[field / Self::WORD_BITS] & (1_u64 << (field % Self::WORD_BITS)) != 0
    }

    pub fn traced_fields(&self) -> Vec<usize> {
        (0..self.field_count)
            .filter(|field| self.is_traced(*field))
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct YValue(usize);

impl YValue {
    const INT_TAG: usize = 0b001;
    const TAG_MASK: usize = 0b111;
    const FALSE_BITS: usize = 0b010;
    const UNIT_BITS: usize = 0b100;
    const TRUE_BITS: usize = 0b110;
    const I63_MIN: i64 = -(1_i64 << 62);
    const I63_MAX: i64 = (1_i64 << 62) - 1;

    pub const UNIT: Self = Self(Self::UNIT_BITS);
    pub const FALSE: Self = Self(Self::FALSE_BITS);
    pub const TRUE: Self = Self(Self::TRUE_BITS);

    pub fn from_i63(value: i64) -> Option<Self> {
        if !(Self::I63_MIN..=Self::I63_MAX).contains(&value) {
            return None;
        }
        Some(Self(((value as isize as usize) << 1) | Self::INT_TAG))
    }

    pub fn from_bool(value: bool) -> Self {
        if value { Self::TRUE } else { Self::FALSE }
    }

    pub fn from_heap_ptr(ptr: NonNull<YObject>) -> Self {
        let raw = ptr.as_ptr() as usize;
        assert!(Self::heap_bits_are_valid(raw));
        Self(raw)
    }

    pub fn raw(self) -> usize {
        self.0
    }

    #[cfg(feature = "mmtk-runtime")]
    pub(crate) fn from_raw(raw: usize) -> Self {
        Self(raw)
    }

    pub fn heap_reference_raw(self) -> Option<usize> {
        Self::heap_reference_raw_bits(self.0)
    }

    pub fn heap_reference_raw_bits(raw: usize) -> Option<usize> {
        Self::heap_bits_are_valid(raw).then_some(raw)
    }

    pub fn from_heap_reference_raw(raw: usize) -> Option<Self> {
        Self::heap_reference_raw_bits(raw).map(Self)
    }

    pub fn kind(self) -> YValueKind {
        if self.is_i63() {
            YValueKind::I63
        } else if self.is_bool() {
            YValueKind::Bool
        } else if self == Self::UNIT {
            YValueKind::Unit
        } else {
            YValueKind::HeapRef
        }
    }

    pub fn is_i63(self) -> bool {
        self.0 & Self::INT_TAG == Self::INT_TAG
    }

    pub fn as_i63(self) -> Option<i64> {
        self.is_i63().then_some(((self.0 as isize) >> 1) as i64)
    }

    pub fn is_bool(self) -> bool {
        matches!(self, Self::FALSE | Self::TRUE)
    }

    pub fn as_bool(self) -> Option<bool> {
        match self {
            Self::FALSE => Some(false),
            Self::TRUE => Some(true),
            _ => None,
        }
    }

    pub fn is_unit(self) -> bool {
        self == Self::UNIT
    }

    pub fn as_heap_ptr(self) -> Option<NonNull<YObject>> {
        Self::heap_bits_are_valid(self.0)
            .then(|| NonZeroUsize::new(self.0))
            .flatten()
            .and_then(|raw| NonNull::new(raw.get() as *mut YObject))
    }

    fn heap_ptr_is_aligned(ptr: NonNull<YObject>) -> bool {
        Self::heap_bits_are_valid(ptr.as_ptr() as usize)
    }

    fn heap_bits_are_valid(raw: usize) -> bool {
        raw != 0 && raw & Self::TAG_MASK == 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum YValueKind {
    I63,
    Bool,
    Unit,
    HeapRef,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct YRootStack {
    values: Vec<YValue>,
}

impl YRootStack {
    pub fn push_frame(&self) -> YRootFrame {
        YRootFrame {
            base: self.values.len(),
        }
    }

    pub fn push(&mut self, value: YValue) -> YRoot {
        let slot = self.values.len();
        self.values.push(value);
        YRoot { slot }
    }

    pub fn set(&mut self, root: YRoot, value: YValue) {
        self.values[root.slot] = value;
    }

    pub fn get(&self, root: YRoot) -> YValue {
        self.values[root.slot]
    }

    pub fn pop(&mut self, root: YRoot) -> Option<YValue> {
        if root.slot + 1 != self.values.len() {
            return None;
        }
        self.values.pop()
    }

    pub fn pop_frame(&mut self, frame: YRootFrame) -> Option<Vec<YValue>> {
        if frame.base > self.values.len() {
            return None;
        }
        Some(self.values.split_off(frame.base))
    }

    pub fn values(&self) -> &[YValue] {
        &self.values
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct YRoot {
    slot: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct YRootFrame {
    base: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YObject {
    header: YObjectHeader,
    payload: YObjectPayload,
}

impl YObject {
    pub fn new(payload: YObjectPayload) -> Self {
        Self {
            header: YObjectHeader {
                kind: payload.kind(),
                trace_slots: payload.trace_slot_count(),
            },
            payload,
        }
    }

    pub fn header(&self) -> YObjectHeader {
        self.header
    }

    pub fn payload(&self) -> &YObjectPayload {
        &self.payload
    }

    pub fn trace_children(&self) -> Vec<YValue> {
        self.payload.trace_children()
    }

    fn debug_value<H: YHeap>(&self, context: &GcRuntimeContext<H>) -> String {
        match &self.payload {
            YObjectPayload::BigInt(value) => value.clone(),
            YObjectPayload::String(value) => format!("{:?}", value.render(context)),
            YObjectPayload::Bytes(value) => format!("{value:?}"),
            YObjectPayload::Path(value) => value.display().to_string(),
            YObjectPayload::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|value| context.debug_value(*value))
                    .collect::<Vec<_>>();
                format!("({})", items.join(", "))
            }
            YObjectPayload::NativeHeapBlock(block) => block.debug_value(context),
            YObjectPayload::Record(fields) => {
                let fields = fields
                    .iter()
                    .map(|(name, value)| format!("{name}: {}", context.debug_value(*value)))
                    .collect::<Vec<_>>();
                format!("{{{}}}", fields.join(", "))
            }
            YObjectPayload::Variant { tag, value } => match value {
                Some(value) => format!(":{tag} {}", context.debug_value(*value)),
                None => format!(":{tag}"),
            },
            YObjectPayload::SymbolicVariant { tag, value } => {
                let tag = context
                    .symbol(*tag)
                    .map(|symbol| symbol.path.display_name())
                    .unwrap_or_else(|| format!("#{tag:?}"));
                match value {
                    Some(value) => format!(":{tag} {}", context.debug_value(*value)),
                    None => format!(":{tag}"),
                }
            }
            YObjectPayload::List(items) => {
                let items = items.render(context);
                format!("[{}]", items.join(", "))
            }
            YObjectPayload::Closure { code, env }
            | YObjectPayload::Thunk { code, env }
            | YObjectPayload::Resumption { code, env } => {
                format!("<{} code={code} env={}>", self.header.kind, env.len())
            }
            YObjectPayload::ContinuationEnv(slots) => {
                format!("<continuation-env slots={}>", slots.len())
            }
            YObjectPayload::HandlerFrame { prompt, env } => {
                format!("<handler-frame prompt={prompt} env={}>", env.len())
            }
            YObjectPayload::ReturnFrame { continuation, env } => {
                format!(
                    "<return-frame continuation={continuation} env={}>",
                    env.len()
                )
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct YObjectHeader {
    pub kind: YObjectKind,
    pub trace_slots: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum YObjectKind {
    BigInt,
    String,
    Bytes,
    Path,
    Tuple,
    Record,
    Variant,
    List,
    Closure,
    Thunk,
    Resumption,
    ContinuationEnv,
    HandlerFrame,
    ReturnFrame,
}

impl fmt::Display for YObjectKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::BigInt => "bigint",
            Self::String => "string",
            Self::Bytes => "bytes",
            Self::Path => "path",
            Self::Tuple => "tuple",
            Self::Record => "record",
            Self::Variant => "variant",
            Self::List => "list",
            Self::Closure => "closure",
            Self::Thunk => "thunk",
            Self::Resumption => "resumption",
            Self::ContinuationEnv => "continuation-env",
            Self::HandlerFrame => "handler-frame",
            Self::ReturnFrame => "return-frame",
        };
        f.write_str(name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum YObjectPayload {
    BigInt(String),
    String(YString),
    Bytes(Box<[u8]>),
    Path(PathBuf),
    Tuple(Box<[YValue]>),
    NativeHeapBlock(NativeHeapBlock),
    Record(Box<[(Box<str>, YValue)]>),
    Variant {
        tag: Box<str>,
        value: Option<YValue>,
    },
    SymbolicVariant {
        tag: YSymbolId,
        value: Option<YValue>,
    },
    List(YList),
    Closure {
        code: usize,
        env: Box<[YValue]>,
    },
    Thunk {
        code: usize,
        env: Box<[YValue]>,
    },
    Resumption {
        code: usize,
        env: Box<[YValue]>,
    },
    ContinuationEnv(Box<[YValue]>),
    HandlerFrame {
        prompt: u64,
        env: Box<[YValue]>,
    },
    ReturnFrame {
        continuation: usize,
        env: Box<[YValue]>,
    },
}

impl YObjectPayload {
    pub fn kind(&self) -> YObjectKind {
        match self {
            Self::BigInt(_) => YObjectKind::BigInt,
            Self::String(_) => YObjectKind::String,
            Self::Bytes(_) => YObjectKind::Bytes,
            Self::Path(_) => YObjectKind::Path,
            Self::Tuple(_) => YObjectKind::Tuple,
            Self::NativeHeapBlock(block) => block.object_kind(),
            Self::Record(_) => YObjectKind::Record,
            Self::Variant { .. } | Self::SymbolicVariant { .. } => YObjectKind::Variant,
            Self::List(_) => YObjectKind::List,
            Self::Closure { .. } => YObjectKind::Closure,
            Self::Thunk { .. } => YObjectKind::Thunk,
            Self::Resumption { .. } => YObjectKind::Resumption,
            Self::ContinuationEnv(_) => YObjectKind::ContinuationEnv,
            Self::HandlerFrame { .. } => YObjectKind::HandlerFrame,
            Self::ReturnFrame { .. } => YObjectKind::ReturnFrame,
        }
    }

    pub fn trace_slot_count(&self) -> usize {
        match self {
            Self::BigInt(_) | Self::Bytes(_) | Self::Path(_) => 0,
            Self::String(value) => value.trace_slot_count(),
            Self::NativeHeapBlock(block) => block.trace_slot_count(),
            Self::Tuple(items)
            | Self::ContinuationEnv(items)
            | Self::Closure { env: items, .. }
            | Self::Thunk { env: items, .. }
            | Self::Resumption { env: items, .. }
            | Self::HandlerFrame { env: items, .. }
            | Self::ReturnFrame { env: items, .. } => items.len(),
            Self::List(value) => value.trace_slot_count(),
            Self::Record(fields) => fields.len(),
            Self::Variant { value, .. } | Self::SymbolicVariant { value, .. } => {
                usize::from(value.is_some())
            }
        }
    }

    pub fn trace_children(&self) -> Vec<YValue> {
        match self {
            Self::BigInt(_) | Self::Bytes(_) | Self::Path(_) => Vec::new(),
            Self::String(value) => value.trace_children(),
            Self::NativeHeapBlock(block) => block.trace_children(),
            Self::Tuple(items)
            | Self::ContinuationEnv(items)
            | Self::Closure { env: items, .. }
            | Self::Thunk { env: items, .. }
            | Self::Resumption { env: items, .. }
            | Self::HandlerFrame { env: items, .. }
            | Self::ReturnFrame { env: items, .. } => items.to_vec(),
            Self::List(value) => value.trace_children(),
            Self::Record(fields) => fields.iter().map(|(_, value)| *value).collect(),
            Self::Variant { value, .. } | Self::SymbolicVariant { value, .. } => {
                value.iter().copied().collect()
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum YString {
    Flat(Box<str>),
    Concat {
        left: YValue,
        right: YValue,
    },
    Slice {
        source: YValue,
        start: usize,
        end: usize,
    },
}

impl YString {
    pub fn flat(value: impl Into<String>) -> Self {
        Self::Flat(value.into().into_boxed_str())
    }

    pub fn trace_slot_count(&self) -> usize {
        match self {
            Self::Flat(_) => 0,
            Self::Concat { .. } => 2,
            Self::Slice { .. } => 1,
        }
    }

    pub fn trace_children(&self) -> Vec<YValue> {
        match self {
            Self::Flat(_) => Vec::new(),
            Self::Concat { left, right } => vec![*left, *right],
            Self::Slice { source, .. } => vec![*source],
        }
    }

    fn render<H: YHeap>(&self, context: &GcRuntimeContext<H>) -> String {
        match self {
            Self::Flat(value) => value.to_string(),
            Self::Concat { left, right } => {
                let mut out = render_string_value(context, *left);
                out.push_str(&render_string_value(context, *right));
                out
            }
            Self::Slice { source, start, end } => {
                let source = render_string_value(context, *source);
                source.get(*start..*end).unwrap_or("").to_string()
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum YList {
    Flat(Box<[YValue]>),
    Concat {
        left: YValue,
        right: YValue,
    },
    Slice {
        source: YValue,
        start: usize,
        end: usize,
    },
}

impl YList {
    pub fn flat(items: impl Into<Box<[YValue]>>) -> Self {
        Self::Flat(items.into())
    }

    pub fn trace_slot_count(&self) -> usize {
        match self {
            Self::Flat(items) => items.len(),
            Self::Concat { .. } => 2,
            Self::Slice { .. } => 1,
        }
    }

    pub fn trace_children(&self) -> Vec<YValue> {
        match self {
            Self::Flat(items) => items.to_vec(),
            Self::Concat { left, right } => vec![*left, *right],
            Self::Slice { source, .. } => vec![*source],
        }
    }

    fn render<H: YHeap>(&self, context: &GcRuntimeContext<H>) -> Vec<String> {
        match self {
            Self::Flat(items) => items
                .iter()
                .map(|value| context.debug_value(*value))
                .collect(),
            Self::Concat { left, right } => {
                let mut out = render_list_value(context, *left);
                out.extend(render_list_value(context, *right));
                out
            }
            Self::Slice { source, start, end } => {
                let source = render_list_value(context, *source);
                source
                    .get(*start..*end)
                    .map(<[String]>::to_vec)
                    .unwrap_or_default()
            }
        }
    }
}

fn render_string_value<H: YHeap>(context: &GcRuntimeContext<H>, value: YValue) -> String {
    let Some(object) = context.object(value) else {
        return String::new();
    };
    let YObjectPayload::String(value) = object.payload() else {
        return String::new();
    };
    value.render(context)
}

fn render_list_value<H: YHeap>(context: &GcRuntimeContext<H>, value: YValue) -> Vec<String> {
    let Some(object) = context.object(value) else {
        return Vec::new();
    };
    let YObjectPayload::List(value) = object.payload() else {
        return Vec::new();
    };
    value.render(context)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YTraceEdge {
    pub origin: YTraceOrigin,
    pub value: YValue,
    pub object_kind: YObjectKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YTraceReport {
    pub root_count: usize,
    pub live_objects: usize,
    pub live_trace_slots: usize,
    pub live_by_kind: BTreeMap<YObjectKind, usize>,
    pub edges: Vec<YTraceEdge>,
}

impl YTraceReport {
    fn from_edges(
        root_count: usize,
        edges: Vec<YTraceEdge>,
        trace_slots: impl Fn(YValue) -> usize,
    ) -> Self {
        let mut live_by_kind = BTreeMap::new();
        let mut live_trace_slots = 0;
        for edge in &edges {
            live_trace_slots += trace_slots(edge.value);
            *live_by_kind.entry(edge.object_kind).or_default() += 1;
        }
        Self {
            root_count,
            live_objects: edges.len(),
            live_trace_slots,
            live_by_kind,
            edges,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum YTraceOrigin {
    Root(usize),
    Object(YObjectKind),
}

#[derive(Default)]
struct YTracer {
    seen: BTreeSet<usize>,
    edges: Vec<YTraceEdge>,
}

impl YTracer {
    fn trace_value<H: YHeap + ?Sized>(&mut self, origin: YTraceOrigin, value: YValue, heap: &H) {
        let Some(raw) = value.heap_reference_raw() else {
            return;
        };
        if !self.seen.insert(raw) {
            return;
        }
        let Some(header) = heap.object_header(value) else {
            return;
        };
        self.edges.push(YTraceEdge {
            origin,
            value,
            object_kind: header.kind,
        });
        let Some(children) = heap.trace_children(value) else {
            return;
        };
        for child in children {
            self.trace_value(YTraceOrigin::Object(header.kind), child, heap);
        }
    }

    fn finish(self) -> Vec<YTraceEdge> {
        self.edges
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn yvalue_encodes_i63_bool_and_unit_without_heap_aliasing() {
        for value in [YValue::I63_MIN, -1, 0, 1, YValue::I63_MAX] {
            let encoded = YValue::from_i63(value).expect("in i63 range");
            assert_eq!(encoded.kind(), YValueKind::I63);
            assert_eq!(encoded.as_i63(), Some(value));
            assert!(encoded.as_heap_ptr().is_none());
        }
        assert!(YValue::from_i63(YValue::I63_MIN - 1).is_none());
        assert!(YValue::from_i63(YValue::I63_MAX + 1).is_none());
        assert_eq!(YValue::from_bool(false).as_bool(), Some(false));
        assert_eq!(YValue::from_bool(true).as_bool(), Some(true));
        assert!(YValue::UNIT.is_unit());
        assert!(YValue::UNIT.as_heap_ptr().is_none());
    }

    #[test]
    fn object_headers_record_kind_and_trace_slot_count() {
        let mut context = GcRuntimeContext::new();
        let one = YValue::from_i63(1).unwrap();
        let two = YValue::from_i63(2).unwrap();
        let tuple = context.alloc_tuple(vec![one, two]);
        let object = context.object(tuple).expect("tuple object");

        assert_eq!(
            object.header(),
            YObjectHeader {
                kind: YObjectKind::Tuple,
                trace_slots: 2,
            }
        );
        assert_eq!(object.trace_children(), vec![one, two]);
    }

    #[test]
    fn native_layout_traces_only_yvalue_fields_in_monomorphic_tuple() {
        let layout = NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::U64),
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
            NativeFieldLayout::unnamed(NativeFieldLane::I64),
            NativeFieldLayout::unnamed(NativeFieldLane::Bool),
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
        ]);

        assert_eq!(layout.kind, NativeLayoutKind::Object(YObjectKind::Tuple));
        assert_eq!(layout.trace_bitmap.field_count(), 5);
        assert_eq!(layout.trace_bitmap.traced_fields(), vec![1, 4]);
        assert!(!layout.trace_bitmap.is_traced(0));
        assert!(layout.trace_bitmap.is_traced(1));
        assert!(!layout.trace_bitmap.is_traced(2));
    }

    #[test]
    fn native_layout_keeps_unboxed_closure_captures_out_of_trace_bitmap() {
        let layout = NativeLayout::closure_env(vec![
            NativeFieldLayout::named("counter", NativeFieldLane::U64),
            NativeFieldLayout::named("label", NativeFieldLane::YValue),
            NativeFieldLayout::named("limit", NativeFieldLane::I64),
        ]);

        assert_eq!(layout.kind, NativeLayoutKind::Object(YObjectKind::Closure));
        assert_eq!(layout.trace_bitmap.traced_fields(), vec![1]);
    }

    #[test]
    fn native_layout_footprint_records_offsets_for_typed_fields() {
        let layout = NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::U64),
            NativeFieldLayout::unnamed(NativeFieldLane::Bool),
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
            NativeFieldLayout::unnamed(NativeFieldLane::I64),
        ]);

        assert_eq!(
            layout.footprint.field_offsets.as_ref(),
            [
                NativeFieldOffset {
                    offset: 0,
                    size: 8,
                    align: 8,
                },
                NativeFieldOffset {
                    offset: 8,
                    size: 1,
                    align: 1,
                },
                NativeFieldOffset {
                    offset: 16,
                    size: 8,
                    align: 8,
                },
                NativeFieldOffset {
                    offset: 24,
                    size: 8,
                    align: 8,
                },
            ]
        );
        assert_eq!(layout.footprint.payload_size, 32);
        assert_eq!(layout.footprint.payload_align, 8);
    }

    #[test]
    fn native_layout_footprint_packs_adjacent_bool_fields_before_word_lane() {
        let layout = NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::Bool),
            NativeFieldLayout::unnamed(NativeFieldLane::Bool),
            NativeFieldLayout::unnamed(NativeFieldLane::Bool),
            NativeFieldLayout::unnamed(NativeFieldLane::U64),
        ]);

        let offsets = layout
            .footprint
            .field_offsets
            .iter()
            .map(|field| field.offset)
            .collect::<Vec<_>>();

        assert_eq!(offsets, vec![0, 1, 2, 8]);
        assert_eq!(layout.footprint.payload_size, 16);
    }

    #[test]
    fn native_layout_registry_deduplicates_equal_monomorphic_layouts() {
        let mut context = GcRuntimeContext::new();
        let first = context.intern_native_layout(NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::U64),
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
        ]));
        let second = context.intern_native_layout(NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::U64),
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
        ]));
        let third = context.intern_native_layout(NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
            NativeFieldLayout::unnamed(NativeFieldLane::U64),
        ]));

        assert_eq!(first.id(), second.id());
        assert_ne!(first.id(), third.id());
        assert_eq!(context.native_layout_count(), 2);
        assert_eq!(first.layout().trace_bitmap.traced_fields(), vec![1]);
    }

    #[test]
    fn symbol_table_assigns_compact_ids_for_static_paths() {
        let table = YSymbolTable::from_static_paths([
            YSymbolPath::new(["std", "option", "some"]),
            YSymbolPath::new(["std", "option", "none"]),
            YSymbolPath::new(["std", "option", "some"]),
        ]);
        let none = YSymbolPath::new(["std", "option", "none"]);
        let some = YSymbolPath::new(["std", "option", "some"]);

        assert_eq!(table.len(), 2);
        assert_eq!(table.id_for_path(&none), Some(YSymbolId(0)));
        assert_eq!(table.id_for_path(&some), Some(YSymbolId(1)));
        assert_eq!(
            table
                .symbol(YSymbolId(1))
                .map(|symbol| symbol.path.display_name()),
            Some("std::option::some".to_string())
        );
        let hash = some.stable_hash();
        assert_eq!(table.ids_for_hash(hash), &[YSymbolId(1)]);
    }

    #[test]
    fn symbol_table_keeps_atom_symbols_distinct_from_path_symbols() {
        let atom = YSymbolPath::atom("std::option::some");
        let path = YSymbolPath::path(["std", "option", "some"]);
        let mut table = YSymbolTable::default();

        let atom_id = table.intern(atom.clone());
        let path_id = table.intern(path.clone());
        let spaced_id = table.intern("ruby style symbol with spaces");

        assert_ne!(atom, path);
        assert_ne!(atom.stable_hash(), path.stable_hash());
        assert_ne!(atom_id, path_id);
        assert_eq!(table.len(), 3);
        assert_eq!(
            table
                .symbol(atom_id)
                .and_then(|symbol| symbol.path.atom_text()),
            Some("std::option::some")
        );
        assert_eq!(
            table
                .symbol(path_id)
                .and_then(|symbol| symbol.path.path_segments())
                .map(|segments| segments.len()),
            Some(3)
        );
        assert_eq!(
            table
                .symbol(spaced_id)
                .map(|symbol| symbol.path.display_name()),
            Some("ruby style symbol with spaces".to_string())
        );
    }

    #[test]
    fn symbol_table_freezes_unique_hashes_into_perfect_lookup() {
        let table = YSymbolTable::from_static_symbols([
            YSymbolPath::atom("alpha"),
            YSymbolPath::path(["std", "option", "none"]),
            YSymbolPath::path(["std", "option", "some"]),
        ]);
        let alpha = YSymbolPath::atom("alpha");
        let some = YSymbolPath::path(["std", "option", "some"]);

        let perfect = table.freeze_perfect_hash().expect("unique hashes");

        assert_eq!(perfect.len(), 3);
        assert_eq!(
            perfect.lookup(alpha.stable_hash()),
            table.id_for_path(&alpha)
        );
        assert_eq!(perfect.lookup(some.stable_hash()), table.id_for_path(&some));
        assert_eq!(perfect.lookup(0), None);
    }

    #[test]
    fn symbol_table_freeze_reports_hash_collisions() {
        let first_path = YSymbolPath::atom("first");
        let second_path = YSymbolPath::atom("second");
        let first = YSymbol {
            id: YSymbolId(0),
            hash: 7,
            path: first_path.clone(),
        };
        let second = YSymbol {
            id: YSymbolId(1),
            hash: 7,
            path: second_path.clone(),
        };
        let table = YSymbolTable {
            symbols: vec![first.clone(), second.clone()],
            by_path: BTreeMap::from([(first_path, first.id), (second_path, second.id)]),
            by_hash: BTreeMap::from([(7, vec![first.id, second.id])]),
        };

        let error = table
            .freeze_perfect_hash()
            .expect_err("collision should reject perfect hash");

        assert_eq!(error.hash, 7);
        assert_eq!(error.first, first.id);
        assert_eq!(error.second, second.id);
        assert_eq!(error.symbols, vec![first, second]);
    }

    #[test]
    fn context_interns_typed_ir_paths_as_symbols() {
        let mut context = GcRuntimeContext::new();
        let path = yulang_typed_ir::Path::new(vec![
            yulang_typed_ir::Name("std".to_string()),
            yulang_typed_ir::Name("result".to_string()),
            yulang_typed_ir::Name("ok".to_string()),
        ]);

        let first = context.intern_symbol_path(&path);
        let second = context.intern_symbol_path(path);

        assert_eq!(first, second);
        assert_eq!(context.symbol_table().len(), 1);
        assert_eq!(
            context
                .symbol(first)
                .map(|symbol| symbol.path.display_name()),
            Some("std::result::ok".to_string())
        );
    }

    #[test]
    fn trace_bitmap_handles_layouts_wider_than_one_word() {
        let fields = (0..70)
            .map(|field| {
                let lane = if matches!(field, 0 | 63 | 64 | 69) {
                    NativeFieldLane::YValue
                } else {
                    NativeFieldLane::U64
                };
                NativeFieldLayout::unnamed(lane)
            })
            .collect::<Vec<_>>();

        let layout = NativeLayout::continuation_env(fields);

        assert_eq!(layout.trace_bitmap.field_count(), 70);
        assert_eq!(layout.trace_bitmap.traced_fields(), vec![0, 63, 64, 69]);
    }

    #[test]
    fn native_block_stores_unboxed_fields_and_traces_only_yvalue_fields() {
        let mut context = GcRuntimeContext::new();
        let label = context.alloc_string("label");
        let layout = NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::U64),
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
            NativeFieldLayout::unnamed(NativeFieldLane::I64),
            NativeFieldLayout::unnamed(NativeFieldLane::Bool),
        ]);

        let block = context
            .alloc_native_block(
                layout,
                vec![
                    NativeFieldValue::U64(u64::MAX),
                    NativeFieldValue::YValue(label),
                    NativeFieldValue::I64(-7),
                    NativeFieldValue::Bool(true),
                ],
            )
            .expect("native block");
        context.root_stack_mut().push(block);

        let object = context.object(block).expect("native block object");
        assert_eq!(object.header().kind, YObjectKind::Tuple);
        assert_eq!(object.header().trace_slots, 1);
        assert_eq!(object.trace_children(), vec![label]);
        assert_eq!(context.trace_root_report().live_objects, 2);
        let YObjectPayload::NativeHeapBlock(block_object) = object.payload() else {
            panic!("native heap block")
        };
        assert_eq!(block_object.field_value(0), NativeFieldValue::U64(u64::MAX));
        assert_eq!(block_object.field_value(1), NativeFieldValue::YValue(label));
        assert_eq!(block_object.field_value(2), NativeFieldValue::I64(-7));
        assert_eq!(block_object.field_value(3), NativeFieldValue::Bool(true));
        assert_eq!(
            context.debug_value(block),
            "<native tuple [18446744073709551615u64, \"label\", -7i64, true]>"
        );
    }

    #[test]
    fn native_block_payload_uses_layout_offsets_for_raw_fields() {
        let mut context = GcRuntimeContext::new();
        let label = context.alloc_string("payload");
        let layout = NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::Bool),
            NativeFieldLayout::unnamed(NativeFieldLane::U64),
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
        ]);
        let field_offsets = layout.footprint.field_offsets.clone();

        let block = context
            .alloc_native_block(
                layout,
                vec![
                    NativeFieldValue::Bool(true),
                    NativeFieldValue::U64(0x1122_3344_5566_7788),
                    NativeFieldValue::YValue(label),
                ],
            )
            .expect("native block");
        let object = context.object(block).expect("native block object");
        let YObjectPayload::NativeHeapBlock(block_object) = object.payload() else {
            panic!("native heap block")
        };

        assert_eq!(block_object.payload().bytes().len(), 24);
        assert_eq!(block_object.payload().bytes()[field_offsets[0].offset], 1);
        assert_eq!(
            read_u64(&block_object.payload().bytes()[field_offsets[1].offset..]),
            0x1122_3344_5566_7788
        );
        assert_eq!(
            read_u64(&block_object.payload().bytes()[field_offsets[2].offset..]) as usize,
            label.raw()
        );
    }

    #[test]
    fn native_block_symbol_lane_stores_compact_symbol_id_without_tracing() {
        let mut context = GcRuntimeContext::new();
        let tag = context.intern_symbol_path(YSymbolPath::new(["std", "option", "some"]));
        let label = context.alloc_string("payload");
        let layout = NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::Symbol),
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
        ]);
        let offsets = layout.footprint.field_offsets.clone();

        let block = context
            .alloc_native_block(
                layout,
                vec![
                    NativeFieldValue::Symbol(tag),
                    NativeFieldValue::YValue(label),
                ],
            )
            .expect("native block");
        context.root_stack_mut().push(block);

        let object = context.object(block).expect("native block object");
        let YObjectPayload::NativeHeapBlock(block_object) = object.payload() else {
            panic!("native heap block")
        };
        assert_eq!(object.header().trace_slots, 1);
        assert_eq!(block_object.field_value(0), NativeFieldValue::Symbol(tag));
        assert_eq!(
            read_u32(&block_object.payload().bytes()[offsets[0].offset..]),
            tag.0
        );
        assert_eq!(
            context.debug_value(block),
            "<native tuple ['std::option::some, \"payload\"]>"
        );
    }

    #[test]
    fn symbolic_variant_uses_symbol_id_for_tag_and_traces_payload_only() {
        let mut context = GcRuntimeContext::new();
        let tag = context.intern_symbol_path(YSymbolPath::new(["std", "option", "some"]));
        let payload = context.alloc_string("payload");

        let value = context.alloc_symbolic_variant(tag, Some(payload));
        context.root_stack_mut().push(value);

        let object = context.object(value).expect("variant object");
        assert_eq!(object.header().kind, YObjectKind::Variant);
        assert_eq!(object.header().trace_slots, 1);
        assert_eq!(object.trace_children(), vec![payload]);
        assert_eq!(context.debug_value(value), ":std::option::some \"payload\"");
    }

    #[test]
    fn native_variant_layout_puts_symbol_tag_in_raw_payload() {
        let mut context = GcRuntimeContext::new();
        let tag = context.intern_symbol_path(YSymbolPath::path(["std", "result", "ok"]));
        let payload = context.alloc_string("value");
        let layout = NativeLayout::variant(vec![NativeFieldLayout::named(
            "payload",
            NativeFieldLane::YValue,
        )]);
        let tag_offset = layout.footprint.field_offsets[0].offset;
        let payload_offset = layout.footprint.field_offsets[1].offset;

        let value = context
            .alloc_native_variant(layout, tag, vec![NativeFieldValue::YValue(payload)])
            .expect("native variant");
        context.root_stack_mut().push(value);

        let object = context.object(value).expect("variant object");
        assert_eq!(object.header().kind, YObjectKind::Variant);
        assert_eq!(object.header().trace_slots, 1);
        assert_eq!(object.trace_children(), vec![payload]);
        let YObjectPayload::NativeHeapBlock(block) = object.payload() else {
            panic!("native heap block")
        };
        assert_eq!(block.variant_tag(), Some(tag));
        assert_eq!(block.field_value(1), NativeFieldValue::YValue(payload));
        assert_eq!(read_u32(&block.payload().bytes()[tag_offset..]), tag.0);
        assert_eq!(
            read_u64(&block.payload().bytes()[payload_offset..]) as usize,
            payload.raw()
        );
        assert_eq!(
            context.debug_value(value),
            "<native variant ['std::result::ok, \"value\"]>"
        );
    }

    #[test]
    fn native_variant_layout_rejects_missing_payload_fields() {
        let mut context = GcRuntimeContext::new();
        let tag = context.intern_symbol_path(YSymbolPath::path(["std", "result", "ok"]));
        let layout = NativeLayout::variant(vec![NativeFieldLayout::named(
            "payload",
            NativeFieldLane::YValue,
        )]);

        let error = context
            .alloc_native_variant(layout, tag, Vec::<NativeFieldValue>::new())
            .expect_err("missing payload field");

        assert_eq!(
            error,
            NativeLayoutError::FieldCountMismatch {
                expected: 2,
                actual: 1,
            }
        );
    }

    #[test]
    fn native_heap_blocks_can_share_one_interned_layout_handle() {
        let mut context = GcRuntimeContext::new();
        let layout = context.intern_native_layout(NativeLayout::tuple(vec![
            NativeFieldLayout::unnamed(NativeFieldLane::U64),
            NativeFieldLayout::unnamed(NativeFieldLane::YValue),
        ]));
        let left_label = context.alloc_string("left");
        let right_label = context.alloc_string("right");

        let left = context
            .alloc_native_block_with_layout(
                layout.clone(),
                vec![
                    NativeFieldValue::U64(10),
                    NativeFieldValue::YValue(left_label),
                ],
            )
            .expect("left block");
        let right = context
            .alloc_native_block_with_layout(
                layout.clone(),
                vec![
                    NativeFieldValue::U64(20),
                    NativeFieldValue::YValue(right_label),
                ],
            )
            .expect("right block");

        context.root_stack_mut().push(left);
        context.root_stack_mut().push(right);

        assert_eq!(context.native_layout_count(), 1);
        assert_eq!(context.trace_root_report().live_objects, 4);
        let left_object = context.object(left).expect("left object");
        let YObjectPayload::NativeHeapBlock(left_block) = left_object.payload() else {
            panic!("native heap block")
        };
        assert_eq!(left_block.layout().id(), layout.id());
    }

    #[test]
    fn native_block_rejects_field_count_and_lane_mismatch() {
        let mut context = GcRuntimeContext::new();
        let layout = NativeLayout::tuple(vec![NativeFieldLayout::unnamed(NativeFieldLane::U64)]);

        let count_error = context
            .alloc_native_block(layout.clone(), Vec::<NativeFieldValue>::new())
            .expect_err("field count mismatch");
        assert_eq!(
            count_error,
            NativeLayoutError::FieldCountMismatch {
                expected: 1,
                actual: 0,
            }
        );

        let lane_error = context
            .alloc_native_block(layout, vec![NativeFieldValue::I64(1)])
            .expect_err("field lane mismatch");
        assert_eq!(
            lane_error,
            NativeLayoutError::FieldLaneMismatch {
                index: 0,
                expected: NativeFieldLane::U64,
                actual: NativeFieldLane::I64,
            }
        );
    }

    #[test]
    fn native_block_does_not_allocate_stack_frame_layout_as_heap_object() {
        let mut context = GcRuntimeContext::new();
        let layout = NativeLayout::new(
            NativeLayoutKind::StackFrame,
            vec![NativeFieldLayout::unnamed(NativeFieldLane::YValue)],
        );

        let error = context
            .alloc_native_block(layout, vec![NativeFieldValue::YValue(YValue::UNIT)])
            .expect_err("stack frame should not be a heap object");

        assert_eq!(error, NativeLayoutError::StackFrameIsNotHeapObject);
        assert_eq!(context.heap_stats().allocated_objects, 0);
    }

    #[test]
    fn context_allocates_every_first_milestone_object_kind() {
        let mut context = GcRuntimeContext::new();
        let child = context.alloc_string("child");
        let unit = YValue::UNIT;

        let values = vec![
            (
                context.alloc_big_int("4611686018427387904"),
                YObjectKind::BigInt,
                0,
            ),
            (context.alloc_string("text"), YObjectKind::String, 0),
            (
                context.alloc_bytes(b"bytes".to_vec()),
                YObjectKind::Bytes,
                0,
            ),
            (context.alloc_path("/tmp/yulang"), YObjectKind::Path, 0),
            (
                context.alloc_tuple(vec![child, unit]),
                YObjectKind::Tuple,
                2,
            ),
            (
                context.alloc_record(vec![(Box::<str>::from("name"), child)]),
                YObjectKind::Record,
                1,
            ),
            (
                context.alloc_variant("some", Some(child)),
                YObjectKind::Variant,
                1,
            ),
            (context.alloc_list(vec![child]), YObjectKind::List, 1),
            (
                context.alloc_closure(1, vec![child]),
                YObjectKind::Closure,
                1,
            ),
            (context.alloc_thunk(2, vec![child]), YObjectKind::Thunk, 1),
            (
                context.alloc_resumption(3, vec![child]),
                YObjectKind::Resumption,
                1,
            ),
            (
                context.alloc_continuation_env(vec![child]),
                YObjectKind::ContinuationEnv,
                1,
            ),
            (
                context.alloc_handler_frame(4, vec![child]),
                YObjectKind::HandlerFrame,
                1,
            ),
            (
                context.alloc_return_frame(5, vec![child]),
                YObjectKind::ReturnFrame,
                1,
            ),
        ];

        for (value, kind, trace_slots) in values {
            let object = context.object(value).expect("allocated object");
            assert_eq!(object.header().kind, kind);
            assert_eq!(object.header().trace_slots, trace_slots);
        }
    }

    #[test]
    fn root_stack_traces_nested_heap_objects() {
        let mut context = GcRuntimeContext::new();
        let label = context.alloc_string("x");
        let closure = context.alloc_closure(7, vec![label]);
        let tuple = context.alloc_tuple(vec![closure, YValue::UNIT]);
        context.root_stack_mut().push(tuple);

        let trace = context.trace_roots();
        let kinds = trace
            .iter()
            .map(|edge| edge.object_kind)
            .collect::<Vec<_>>();

        assert_eq!(
            kinds,
            vec![
                YObjectKind::Tuple,
                YObjectKind::Closure,
                YObjectKind::String
            ]
        );
        assert_eq!(trace[0].origin, YTraceOrigin::Root(0));
        assert_eq!(trace[1].origin, YTraceOrigin::Object(YObjectKind::Tuple));
    }

    #[test]
    fn heap_stats_report_allocated_objects_independent_of_roots() {
        let mut context = GcRuntimeContext::new();
        let orphan = context.alloc_string("orphan");
        let captured = context.alloc_string("captured");
        let closure = context.alloc_closure(7, vec![captured]);
        let tuple = context.alloc_tuple(vec![closure]);
        context.root_stack_mut().push(tuple);

        let stats = context.heap_stats();
        assert_eq!(stats.allocated_objects, 4);
        assert_eq!(stats.allocated_trace_slots, 2);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::String], 2);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::Closure], 1);
        assert_eq!(stats.allocated_by_kind[&YObjectKind::Tuple], 1);

        assert_eq!(context.debug_value(orphan), "\"orphan\"");
    }

    #[test]
    fn trace_root_report_summarizes_only_live_reachable_objects() {
        let mut context = GcRuntimeContext::new();
        let _orphan = context.alloc_string("orphan");
        let captured = context.alloc_string("captured");
        let closure = context.alloc_closure(7, vec![captured]);
        let tuple = context.alloc_tuple(vec![closure]);
        context.root_stack_mut().push(tuple);

        let report = context.trace_root_report();
        assert_eq!(report.root_count, 1);
        assert_eq!(report.live_objects, 3);
        assert_eq!(report.live_trace_slots, 2);
        assert_eq!(report.live_by_kind[&YObjectKind::String], 1);
        assert_eq!(report.live_by_kind[&YObjectKind::Closure], 1);
        assert_eq!(report.live_by_kind[&YObjectKind::Tuple], 1);
        assert_eq!(report.edges[0].object_kind, YObjectKind::Tuple);
    }

    #[test]
    fn string_rope_nodes_trace_children_and_render_debug_value() {
        let mut context = GcRuntimeContext::new();
        let left = context.alloc_string("hel");
        let right = context.alloc_string("lo");
        let concat = context.alloc_string_concat(left, right);
        let slice = context.alloc_string_slice(concat, 1, 4);
        context.root_stack_mut().push(slice);

        let concat_object = context.object(concat).expect("concat string");
        assert_eq!(concat_object.header().trace_slots, 2);
        assert_eq!(context.debug_value(concat), "\"hello\"");
        assert_eq!(context.debug_value(slice), "\"ell\"");

        let kinds = context
            .trace_roots()
            .iter()
            .map(|edge| edge.object_kind)
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            vec![
                YObjectKind::String,
                YObjectKind::String,
                YObjectKind::String,
                YObjectKind::String,
            ]
        );
    }

    #[test]
    fn list_rope_nodes_trace_children_and_render_debug_value() {
        let mut context = GcRuntimeContext::new();
        let left = context.alloc_list(vec![YValue::from_i63(1).unwrap()]);
        let right = context.alloc_list(vec![YValue::from_i63(2).unwrap(), YValue::UNIT]);
        let concat = context.alloc_list_concat(left, right);
        let slice = context.alloc_list_slice(concat, 1, 3);
        context.root_stack_mut().push(slice);

        let concat_object = context.object(concat).expect("concat list");
        assert_eq!(concat_object.header().trace_slots, 2);
        assert_eq!(context.debug_value(concat), "[1, 2, ()]");
        assert_eq!(context.debug_value(slice), "[2, ()]");

        let kinds = context
            .trace_roots()
            .iter()
            .map(|edge| edge.object_kind)
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            vec![
                YObjectKind::List,
                YObjectKind::List,
                YObjectKind::List,
                YObjectKind::List,
            ]
        );
    }

    #[test]
    fn stress_mode_traces_roots_before_each_allocation() {
        let mut context = GcRuntimeContext::new();
        context.enable_collect_every_allocation();
        let value = context.alloc_string("rooted");
        context.root_stack_mut().push(value);
        let _tuple = context.alloc_tuple(vec![value]);

        assert_eq!(context.stress_collection_count(), 2);
        assert_eq!(context.trace_roots().len(), 1);
    }

    #[test]
    fn root_frames_restore_temporary_helper_roots() {
        let mut context = GcRuntimeContext::new();
        let permanent = context.alloc_string("permanent");
        context.root_stack_mut().push(permanent);

        let frame = context.root_stack().push_frame();
        let temporary = context.alloc_string("temporary");
        context.root_stack_mut().push(temporary);

        assert_eq!(context.trace_roots().len(), 2);
        let popped = context
            .root_stack_mut()
            .pop_frame(frame)
            .expect("valid frame");
        assert_eq!(popped, vec![temporary]);
        assert_eq!(context.root_stack().values(), &[permanent]);
        assert_eq!(context.trace_roots().len(), 1);
    }

    #[test]
    fn temporary_root_helper_scope_roots_values_across_allocation() {
        let mut context = GcRuntimeContext::new();
        context.enable_collect_every_allocation();

        let captured = context.alloc_string("captured");
        let permanent = context.alloc_string("permanent");
        context.root_stack_mut().push(permanent);

        let rendered = context.with_temporary_roots([captured], |context, roots| {
            let captured = context.root_stack().get(roots[0]);
            let tuple = context.alloc_tuple(vec![captured, YValue::UNIT]);
            context.debug_value(tuple)
        });

        assert_eq!(rendered, "(\"captured\", ())");
        assert_eq!(context.root_stack().values(), &[permanent]);
        assert_eq!(context.trace_roots().len(), 1);
        assert_eq!(context.stress_collection_count(), 3);
    }

    #[test]
    fn context_can_use_an_injected_heap_boundary() {
        let heap = SpikeHeap::default();
        let mut context = GcRuntimeContext::with_heap(heap);
        let value = context.alloc_tuple(Vec::<YValue>::new());

        assert_eq!(context.heap().object_count(), 1);
        assert_eq!(
            context.object(value).map(|object| object.header().kind),
            Some(YObjectKind::Tuple)
        );
    }

    #[test]
    fn checked_i63_add_promotes_overflow_to_bigint_object() {
        let mut context = GcRuntimeContext::new();
        let left = YValue::from_i63(YValue::I63_MAX).unwrap();
        let right = YValue::from_i63(1).unwrap();

        let value = context.checked_add_int(left, right).expect("add result");

        let object = context.object(value).expect("bigint object");
        assert_eq!(object.header().kind, YObjectKind::BigInt);
        assert_eq!(
            context.debug_value(value),
            (YValue::I63_MAX as i128 + 1).to_string()
        );
    }

    #[test]
    fn int_helpers_cover_sub_mul_compare_and_bigint_spike_values() {
        let mut context = GcRuntimeContext::new();
        let one = YValue::from_i63(1).unwrap();
        let two = YValue::from_i63(2).unwrap();
        let max = YValue::from_i63(YValue::I63_MAX).unwrap();
        let min = YValue::from_i63(YValue::I63_MIN).unwrap();

        let small_mul = context.checked_mul_int(two, two).expect("mul result");
        assert_eq!(small_mul.as_i63(), Some(4));

        let underflow = context.checked_sub_int(min, one).expect("sub result");
        assert_eq!(
            context.debug_value(underflow),
            (YValue::I63_MIN as i128 - 1).to_string()
        );

        let overflow = context.checked_mul_int(max, two).expect("mul result");
        assert_eq!(
            context.debug_value(overflow),
            (YValue::I63_MAX as i128 * 2).to_string()
        );
        assert_eq!(context.compare_int(overflow, max), Some(Ordering::Greater));

        let back_inside_i63 = context.checked_sub_int(underflow, one).expect("sub result");
        assert_eq!(
            context.compare_int(back_inside_i63, underflow),
            Some(Ordering::Less)
        );
    }
}
