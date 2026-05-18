use std::cell::{OnceCell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use yulang_runtime::runtime::bytes_tree::BytesTree;
use yulang_runtime::runtime::list_tree::{ListTree, ListView};
use yulang_runtime::runtime::string_tree::StringTree;
use yulang_typed_ir as typed_ir;

use super::{CpsRootDisplayHint, tag_hash};

type NativeCpsI64Continuation = extern "C" fn(*const i64, i64) -> i64;
type NativeCpsI64ThunkEntry = extern "C" fn(*const i64) -> i64;
type NativeCpsI64ClosureEntry = extern "C" fn(*const i64, i64) -> i64;
type NativeCpsI64HandlerSnapshot = NativeCpsI64Snapshot<NativeCpsI64HandlerFrame>;
type NativeCpsI64ReturnFrameSnapshot = NativeCpsI64Snapshot<NativeCpsI64ReturnFrame>;
type NativeCpsI64I64Snapshot = NativeCpsI64Snapshot<i64>;
type NativeCpsI64HandlerEnvSnapshot = NativeCpsI64Snapshot<NativeCpsI64HandlerEnv>;

const CONTROL_CAPTURE_HANDLER_STACK: i64 = 1 << 0;
const CONTROL_CAPTURE_GUARD_STACK: i64 = 1 << 1;
const CONTROL_CAPTURE_ACTIVE_BLOCKED: i64 = 1 << 2;
const CONTROL_CAPTURE_PENDING_HANDLER_ENVS: i64 = 1 << 3;
const CONTROL_CAPTURE_PENDING_ESCAPE_TARGETS: i64 = 1 << 4;
const CONTROL_CAPTURE_RESUME_WITH_HANDLER_SIBLINGS: i64 = 1 << 5;
const CONTROL_CAPTURE_ABORT: i64 = 1 << 6;
const CONTROL_CAPTURE_SCOPE_RETURN: i64 = 1 << 7;

#[derive(Clone, Copy)]
enum NativeCpsI64StackKind {
    ReturnFrames,
    HandlerStack,
    GuardStack,
}

const NATIVE_CPS_I64_STACK_KIND_COUNT: usize = 3;
const NATIVE_CPS_I64_STATS_SITE_COUNT: usize = 12;

impl NativeCpsI64StackKind {
    fn for_item<T>() -> Option<Self> {
        let name = std::any::type_name::<T>();
        if name.ends_with("NativeCpsI64ReturnFrame") {
            Some(Self::ReturnFrames)
        } else if name.ends_with("NativeCpsI64HandlerFrame") {
            Some(Self::HandlerStack)
        } else if name == "i64" {
            Some(Self::GuardStack)
        } else {
            None
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::ReturnFrames => "return_frames",
            Self::HandlerStack => "handler_stack",
            Self::GuardStack => "guard_stack",
        }
    }

    fn index(self) -> usize {
        match self {
            Self::ReturnFrames => 0,
            Self::HandlerStack => 1,
            Self::GuardStack => 2,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum NativeCpsI64StatsSite {
    General,
    MakeResumption,
    MakeThunk,
    MakeClosure,
    PushReturnFrame,
    ContinueReturnFrame,
    ForceThunk,
    EffectfulApplyResumption,
    ResumeWithHandler,
    HandlerArm,
    RouteScopeReturn,
    RootResult,
}

impl NativeCpsI64StatsSite {
    fn label(self) -> &'static str {
        match self {
            Self::General => "general",
            Self::MakeResumption => "make_resumption",
            Self::MakeThunk => "make_thunk",
            Self::MakeClosure => "make_closure",
            Self::PushReturnFrame => "push_return_frame",
            Self::ContinueReturnFrame => "continue_return_frame",
            Self::ForceThunk => "force_thunk",
            Self::EffectfulApplyResumption => "effectful_apply_resumption",
            Self::ResumeWithHandler => "resume_with_handler",
            Self::HandlerArm => "handler_arm",
            Self::RouteScopeReturn => "route_scope_return",
            Self::RootResult => "root_result",
        }
    }

    fn index(self) -> usize {
        match self {
            Self::General => 0,
            Self::MakeResumption => 1,
            Self::MakeThunk => 2,
            Self::MakeClosure => 3,
            Self::PushReturnFrame => 4,
            Self::ContinueReturnFrame => 5,
            Self::ForceThunk => 6,
            Self::EffectfulApplyResumption => 7,
            Self::ResumeWithHandler => 8,
            Self::HandlerArm => 9,
            Self::RouteScopeReturn => 10,
            Self::RootResult => 11,
        }
    }

    fn all() -> [Self; NATIVE_CPS_I64_STATS_SITE_COUNT] {
        [
            Self::General,
            Self::MakeResumption,
            Self::MakeThunk,
            Self::MakeClosure,
            Self::PushReturnFrame,
            Self::ContinueReturnFrame,
            Self::ForceThunk,
            Self::EffectfulApplyResumption,
            Self::ResumeWithHandler,
            Self::HandlerArm,
            Self::RouteScopeReturn,
            Self::RootResult,
        ]
    }
}

#[derive(Clone, Default)]
struct NativeCpsI64StackStats {
    snapshot_calls: u64,
    snapshot_hits: u64,
    snapshot_misses: u64,
    snapshot_items_cloned: u64,
    snapshot_len_0: u64,
    snapshot_len_1_4: u64,
    snapshot_len_5_16: u64,
    snapshot_len_17_plus: u64,
    push_calls: u64,
    pop_calls: u64,
    pop_some: u64,
    replace_calls: u64,
    replace_items: u64,
    take_calls: u64,
    take_items: u64,
    clear_calls: u64,
    truncate_calls: u64,
    truncated_items: u64,
    max_len: usize,
}

#[derive(Clone, Copy, Default)]
struct NativeCpsI64StackSiteStats {
    snapshot_calls: u64,
    snapshot_misses: u64,
    snapshot_items_cloned: u64,
    replace_calls: u64,
    replace_items: u64,
    replace_empty: u64,
}

#[derive(Clone, Default)]
struct NativeCpsI64RuntimeStats {
    return_frames: NativeCpsI64StackStats,
    handler_stack: NativeCpsI64StackStats,
    guard_stack: NativeCpsI64StackStats,
    site_stacks: [[NativeCpsI64StackSiteStats; NATIVE_CPS_I64_STACK_KIND_COUNT];
        NATIVE_CPS_I64_STATS_SITE_COUNT],
    make_resumption_calls: u64,
    make_thunk_calls: u64,
    make_closure_calls: u64,
    add_thunk_boundary_calls: u64,
    force_thunk_calls: u64,
    continue_return_frame_calls: u64,
    return_i64_calls: u64,
    root_result_calls: u64,
}

impl NativeCpsI64RuntimeStats {
    fn stack_mut(&mut self, kind: NativeCpsI64StackKind) -> &mut NativeCpsI64StackStats {
        match kind {
            NativeCpsI64StackKind::ReturnFrames => &mut self.return_frames,
            NativeCpsI64StackKind::HandlerStack => &mut self.handler_stack,
            NativeCpsI64StackKind::GuardStack => &mut self.guard_stack,
        }
    }

    fn site_stack_mut(
        &mut self,
        site: NativeCpsI64StatsSite,
        kind: NativeCpsI64StackKind,
    ) -> &mut NativeCpsI64StackSiteStats {
        &mut self.site_stacks[site.index()][kind.index()]
    }
}

fn native_cps_i64_stats_enabled() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static STATE: AtomicU8 = AtomicU8::new(0);
    match STATE.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let on = std::env::var("YULANG_CPS_I64_STATS")
                .map(|value| value == "1")
                .unwrap_or(false);
            STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
    }
}

fn with_native_cps_i64_stats(update: impl FnOnce(&mut NativeCpsI64RuntimeStats)) {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    NATIVE_CPS_I64_STATS.with(|stats| update(&mut stats.borrow_mut()));
}

fn current_native_cps_i64_stats_site() -> NativeCpsI64StatsSite {
    NATIVE_CPS_I64_STATS_SITE.with(|site| *site.borrow())
}

struct NativeCpsI64StatsSiteGuard {
    previous: NativeCpsI64StatsSite,
}

impl Drop for NativeCpsI64StatsSiteGuard {
    fn drop(&mut self) {
        NATIVE_CPS_I64_STATS_SITE.with(|slot| *slot.borrow_mut() = self.previous);
    }
}

fn enter_native_cps_i64_stats_site(
    site: NativeCpsI64StatsSite,
) -> Option<NativeCpsI64StatsSiteGuard> {
    if !native_cps_i64_stats_enabled() {
        return None;
    }
    let previous = NATIVE_CPS_I64_STATS_SITE.with(|slot| {
        let previous = *slot.borrow();
        *slot.borrow_mut() = site;
        previous
    });
    Some(NativeCpsI64StatsSiteGuard { previous })
}

fn note_native_cps_i64_stack_snapshot<T>(len: usize, missed_cache: bool) {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    let Some(kind) = NativeCpsI64StackKind::for_item::<T>() else {
        return;
    };
    let site = current_native_cps_i64_stats_site();
    with_native_cps_i64_stats(|stats| {
        let stack = stats.stack_mut(kind);
        stack.snapshot_calls += 1;
        stack.max_len = stack.max_len.max(len);
        match len {
            0 => stack.snapshot_len_0 += 1,
            1..=4 => stack.snapshot_len_1_4 += 1,
            5..=16 => stack.snapshot_len_5_16 += 1,
            _ => stack.snapshot_len_17_plus += 1,
        }
        if missed_cache {
            stack.snapshot_misses += 1;
            stack.snapshot_items_cloned += len as u64;
        } else {
            stack.snapshot_hits += 1;
        }
        let site_stack = stats.site_stack_mut(site, kind);
        site_stack.snapshot_calls += 1;
        if missed_cache {
            site_stack.snapshot_misses += 1;
            site_stack.snapshot_items_cloned += len as u64;
        }
    });
}

fn note_native_cps_i64_stack_push<T>(len_after: usize) {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    let Some(kind) = NativeCpsI64StackKind::for_item::<T>() else {
        return;
    };
    with_native_cps_i64_stats(|stats| {
        let stack = stats.stack_mut(kind);
        stack.push_calls += 1;
        stack.max_len = stack.max_len.max(len_after);
    });
}

fn note_native_cps_i64_stack_pop<T>(had_value: bool, len_after: usize) {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    let Some(kind) = NativeCpsI64StackKind::for_item::<T>() else {
        return;
    };
    with_native_cps_i64_stats(|stats| {
        let stack = stats.stack_mut(kind);
        stack.pop_calls += 1;
        if had_value {
            stack.pop_some += 1;
        }
        stack.max_len = stack.max_len.max(len_after);
    });
}

fn note_native_cps_i64_stack_replace<T>(new_len: usize) {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    let Some(kind) = NativeCpsI64StackKind::for_item::<T>() else {
        return;
    };
    let site = current_native_cps_i64_stats_site();
    with_native_cps_i64_stats(|stats| {
        let stack = stats.stack_mut(kind);
        stack.replace_calls += 1;
        stack.replace_items += new_len as u64;
        stack.max_len = stack.max_len.max(new_len);
        let site_stack = stats.site_stack_mut(site, kind);
        site_stack.replace_calls += 1;
        site_stack.replace_items += new_len as u64;
        if new_len == 0 {
            site_stack.replace_empty += 1;
        }
    });
}

fn note_native_cps_i64_stack_take<T>(old_len: usize) {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    let Some(kind) = NativeCpsI64StackKind::for_item::<T>() else {
        return;
    };
    with_native_cps_i64_stats(|stats| {
        let stack = stats.stack_mut(kind);
        stack.take_calls += 1;
        stack.take_items += old_len as u64;
        stack.max_len = stack.max_len.max(old_len);
    });
}

fn note_native_cps_i64_stack_clear<T>(old_len: usize) {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    let Some(kind) = NativeCpsI64StackKind::for_item::<T>() else {
        return;
    };
    with_native_cps_i64_stats(|stats| {
        let stack = stats.stack_mut(kind);
        stack.clear_calls += 1;
        stack.max_len = stack.max_len.max(old_len);
    });
}

fn note_native_cps_i64_stack_truncate<T>(old_len: usize, new_len: usize) {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    let Some(kind) = NativeCpsI64StackKind::for_item::<T>() else {
        return;
    };
    with_native_cps_i64_stats(|stats| {
        let stack = stats.stack_mut(kind);
        stack.truncate_calls += 1;
        stack.truncated_items += old_len.saturating_sub(new_len) as u64;
        stack.max_len = stack.max_len.max(old_len);
    });
}

fn native_cps_i64_snapshot<T: NativeCpsI64SnapshotItem>(items: Vec<T>) -> NativeCpsI64Snapshot<T> {
    NativeCpsI64Snapshot::new(items)
}

fn native_cps_i64_empty_snapshot<T: NativeCpsI64SnapshotItem>() -> NativeCpsI64Snapshot<T> {
    NativeCpsI64Snapshot::new(Vec::new())
}

#[derive(Clone)]
struct NativeCpsI64Snapshot<T> {
    storage: NativeCpsI64SnapshotStorage<T>,
    mmtk_control_stack: Option<i64>,
}

#[derive(Clone)]
enum NativeCpsI64SnapshotStorage<T> {
    Flat(Rc<[T]>),
    Append(Rc<NativeCpsI64SnapshotAppend<T>>),
}

struct NativeCpsI64SnapshotAppend<T> {
    base: NativeCpsI64Snapshot<T>,
    item: T,
    len: usize,
    materialized: OnceCell<Rc<[T]>>,
}

impl<T: NativeCpsI64SnapshotItem> NativeCpsI64Snapshot<T> {
    fn new(items: Vec<T>) -> Self {
        let items = Rc::from(items.into_boxed_slice());
        let mmtk_control_stack = native_cps_i64_mmtk_control_stack_from_items(&items);
        Self {
            storage: NativeCpsI64SnapshotStorage::Flat(items),
            mmtk_control_stack: mmtk_control_stack.as_ref().map(|top| top.object),
        }
    }

    fn from_items_and_mmtk_top(items: Vec<T>, mmtk_control_stack: Option<i64>) -> Self {
        Self {
            storage: NativeCpsI64SnapshotStorage::Flat(Rc::from(items.into_boxed_slice())),
            mmtk_control_stack,
        }
    }

    fn to_vec(&self) -> Vec<T> {
        self.items().to_vec()
    }

    fn shares_storage_with(&self, other: &Self) -> bool {
        self.storage.shares_storage_with(&other.storage)
            && self.mmtk_control_stack == other.mmtk_control_stack
    }

    fn mmtk_top(&self) -> Option<Rc<NativeCpsI64MmtkStackTop>> {
        self.mmtk_control_stack.map(|object| {
            Rc::new(NativeCpsI64MmtkStackTop {
                object,
                len: self.len(),
            })
        })
    }

    fn appended(&self, item: T) -> Self {
        Self {
            storage: NativeCpsI64SnapshotStorage::Append(Rc::new(NativeCpsI64SnapshotAppend {
                base: self.clone(),
                item,
                len: self.len() + 1,
                materialized: OnceCell::new(),
            })),
            mmtk_control_stack: None,
        }
    }

    fn len(&self) -> usize {
        self.storage.len()
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn items(&self) -> &[T] {
        self.storage.items()
    }

    fn flatten(&mut self) {
        if matches!(self.storage, NativeCpsI64SnapshotStorage::Flat(_)) {
            return;
        }
        self.storage =
            NativeCpsI64SnapshotStorage::Flat(Rc::from(self.to_vec().into_boxed_slice()));
    }

    fn make_mut(&mut self) -> &mut [T] {
        self.mmtk_control_stack = None;
        self.flatten();
        match &mut self.storage {
            NativeCpsI64SnapshotStorage::Flat(items) => Rc::make_mut(items),
            NativeCpsI64SnapshotStorage::Append(_) => unreachable!("snapshot should be flat"),
        }
    }

    fn collect_mmtk_trace_words(&self, out: &mut Vec<i64>) {
        if let Some(control_stack) = self.mmtk_control_stack {
            out.push(control_stack);
        } else {
            self.storage.collect_mmtk_trace_words(out);
        }
    }
}

impl<T: NativeCpsI64SnapshotItem> NativeCpsI64SnapshotStorage<T> {
    fn len(&self) -> usize {
        match self {
            Self::Flat(items) => items.len(),
            Self::Append(node) => node.len,
        }
    }

    fn items(&self) -> &[T] {
        match self {
            Self::Flat(items) => items,
            Self::Append(node) => node
                .materialized
                .get_or_init(|| {
                    let mut items = node.base.to_vec();
                    items.push(node.item.clone());
                    Rc::from(items.into_boxed_slice())
                })
                .as_ref(),
        }
    }

    fn shares_storage_with(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Flat(left), Self::Flat(right)) => Rc::ptr_eq(left, right),
            (Self::Append(left), Self::Append(right)) => Rc::ptr_eq(left, right),
            _ => false,
        }
    }

    fn collect_mmtk_trace_words(&self, out: &mut Vec<i64>) {
        match self {
            Self::Flat(items) => {
                for item in items.iter() {
                    item.collect_mmtk_trace_words(out);
                }
            }
            Self::Append(node) => {
                node.base.collect_mmtk_trace_words(out);
                node.item.collect_mmtk_trace_words(out);
            }
        }
    }
}

impl<T: NativeCpsI64SnapshotItem> Default for NativeCpsI64Snapshot<T> {
    fn default() -> Self {
        Self::new(Vec::new())
    }
}

impl<T: NativeCpsI64SnapshotItem + std::fmt::Debug> std::fmt::Debug for NativeCpsI64Snapshot<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.items().fmt(f)
    }
}

impl<T: NativeCpsI64SnapshotItem> std::ops::Deref for NativeCpsI64Snapshot<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.items()
    }
}

trait NativeCpsI64SnapshotItem: Clone {
    fn collect_mmtk_trace_words(&self, out: &mut Vec<i64>);
}

#[derive(Clone)]
struct NativeCpsI64MmtkStackTop {
    object: i64,
    len: usize,
}

fn native_cps_i64_mmtk_control_stack_from_items<T: NativeCpsI64SnapshotItem>(
    items: &[T],
) -> Option<Rc<NativeCpsI64MmtkStackTop>> {
    if !crate::mmtk_runtime::mmtk_cps_control_stack_snapshots_enabled() {
        return None;
    }
    let mut trace_words = Vec::new();
    for item in items {
        item.collect_mmtk_trace_words(&mut trace_words);
    }
    let object = crate::mmtk_runtime::allocate_mmtk_cps_control_stack_snapshot_i64(
        items.len(),
        &trace_words,
    )?;
    Some(Rc::new(NativeCpsI64MmtkStackTop {
        object,
        len: items.len(),
    }))
}

fn native_cps_i64_mmtk_control_stack_snapshot<T: NativeCpsI64SnapshotItem>(
    items: &[T],
) -> Option<Rc<NativeCpsI64MmtkStackTop>> {
    if items.is_empty() {
        return None;
    }
    native_cps_i64_mmtk_control_stack_from_items(items)
}

#[derive(Clone)]
struct NativeCpsI64PersistentStack<T: NativeCpsI64SnapshotItem> {
    items: Vec<T>,
    snapshot: Option<NativeCpsI64Snapshot<T>>,
    mmtk_top: Option<Rc<NativeCpsI64MmtkStackTop>>,
}

impl<T: NativeCpsI64SnapshotItem> Default for NativeCpsI64PersistentStack<T> {
    fn default() -> Self {
        Self {
            items: Vec::new(),
            snapshot: None,
            mmtk_top: None,
        }
    }
}

impl<T: NativeCpsI64SnapshotItem> std::ops::Deref for NativeCpsI64PersistentStack<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.items
    }
}

impl<T: NativeCpsI64SnapshotItem> NativeCpsI64PersistentStack<T> {
    fn snapshot(&mut self) -> NativeCpsI64Snapshot<T> {
        let missed_cache = self.snapshot.is_none();
        if missed_cache {
            self.ensure_mmtk_top();
            let top = self.mmtk_top.as_ref().map(|top| top.object);
            self.snapshot = Some(NativeCpsI64Snapshot::from_items_and_mmtk_top(
                self.items.clone(),
                top,
            ));
        }
        note_native_cps_i64_stack_snapshot::<T>(self.items.len(), missed_cache);
        self.snapshot
            .as_ref()
            .expect("snapshot should be initialized")
            .clone()
    }

    fn to_vec(&self) -> Vec<T> {
        self.items.clone()
    }

    fn replace(&mut self, items: Vec<T>) -> Vec<T> {
        self.snapshot = None;
        self.mmtk_top = None;
        note_native_cps_i64_stack_replace::<T>(items.len());
        std::mem::replace(&mut self.items, items)
    }

    fn replace_snapshot(&mut self, snapshot: NativeCpsI64Snapshot<T>) -> Vec<T> {
        let items = snapshot.to_vec();
        let previous = std::mem::replace(&mut self.items, items);
        self.mmtk_top = snapshot.mmtk_top();
        self.snapshot = Some(snapshot);
        note_native_cps_i64_stack_replace::<T>(self.items.len());
        previous
    }

    fn restore_snapshot(&mut self, snapshot: NativeCpsI64Snapshot<T>) {
        if let Some(current) = self.snapshot.as_ref() {
            if current.shares_storage_with(&snapshot) {
                return;
            }
        }
        let _ = self.replace_snapshot(snapshot);
    }

    fn take(&mut self) -> Vec<T> {
        self.snapshot = None;
        self.mmtk_top = None;
        note_native_cps_i64_stack_take::<T>(self.items.len());
        std::mem::take(&mut self.items)
    }

    fn clear(&mut self) {
        self.snapshot = None;
        self.mmtk_top = None;
        note_native_cps_i64_stack_clear::<T>(self.items.len());
        self.items.clear();
    }

    fn push(&mut self, value: T) {
        self.snapshot = self
            .snapshot
            .as_ref()
            .map(|snapshot| snapshot.appended(value.clone()));
        self.mmtk_top = None;
        self.items.push(value);
        note_native_cps_i64_stack_push::<T>(self.items.len());
    }

    fn pop(&mut self) -> Option<T> {
        let popped = self.items.pop();
        if popped.is_some() {
            self.snapshot = None;
            self.mmtk_top = None;
        }
        note_native_cps_i64_stack_pop::<T>(popped.is_some(), self.items.len());
        popped
    }

    fn remove(&mut self, index: usize) -> T {
        self.snapshot = None;
        self.mmtk_top = None;
        self.items.remove(index)
    }

    fn truncate(&mut self, len: usize) {
        if len < self.items.len() {
            let old_len = self.items.len();
            self.snapshot = None;
            self.items.truncate(len);
            self.mmtk_top = None;
            note_native_cps_i64_stack_truncate::<T>(old_len, len);
        }
    }

    fn ensure_mmtk_top(&mut self) {
        let current_len = self.mmtk_top.as_ref().map(|top| top.len).unwrap_or(0);
        if current_len == self.items.len() {
            return;
        }
        self.mmtk_top = native_cps_i64_mmtk_control_stack_snapshot(&self.items);
    }
}

impl<T: NativeCpsI64SnapshotItem> FromIterator<T> for NativeCpsI64PersistentStack<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            items: iter.into_iter().collect(),
            snapshot: None,
            mmtk_top: None,
        }
    }
}

impl<T: NativeCpsI64SnapshotItem> IntoIterator for NativeCpsI64PersistentStack<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.into_iter()
    }
}

#[derive(Clone)]
struct NativeCpsI64GuardStack {
    base: NativeCpsI64I64Snapshot,
    tail: Vec<i64>,
    snapshot: Option<NativeCpsI64I64Snapshot>,
}

impl Default for NativeCpsI64GuardStack {
    fn default() -> Self {
        let base = native_cps_i64_empty_snapshot();
        Self {
            snapshot: Some(base.clone()),
            base,
            tail: Vec::new(),
        }
    }
}

impl NativeCpsI64GuardStack {
    fn len(&self) -> usize {
        self.base.len() + self.tail.len()
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn last(&self) -> Option<&i64> {
        self.tail.last().or_else(|| self.base.last())
    }

    fn contains(&self, value: &i64) -> bool {
        self.tail.contains(value) || self.base.contains(value)
    }

    fn to_vec(&self) -> Vec<i64> {
        let mut values = self.base.to_vec();
        values.extend(self.tail.iter().copied());
        values
    }

    fn snapshot(&mut self) -> NativeCpsI64I64Snapshot {
        let missed_cache = self.snapshot.is_none();
        if missed_cache {
            let mut snapshot = self.base.clone();
            for value in &self.tail {
                snapshot = snapshot.appended(*value);
            }
            self.snapshot = Some(snapshot);
        }
        note_native_cps_i64_stack_snapshot::<i64>(self.len(), missed_cache);
        self.snapshot
            .as_ref()
            .expect("guard snapshot should be initialized")
            .clone()
    }

    fn replace(&mut self, items: Vec<i64>) -> Vec<i64> {
        let previous = self.to_vec();
        self.base = native_cps_i64_snapshot(items);
        self.tail.clear();
        self.snapshot = Some(self.base.clone());
        note_native_cps_i64_stack_replace::<i64>(self.len());
        previous
    }

    fn replace_snapshot(&mut self, snapshot: NativeCpsI64I64Snapshot) -> NativeCpsI64I64Snapshot {
        let previous = self.snapshot();
        self.restore_snapshot(snapshot);
        previous
    }

    fn restore_snapshot(&mut self, snapshot: NativeCpsI64I64Snapshot) {
        if self.tail.is_empty() && self.base.shares_storage_with(&snapshot) {
            return;
        }
        self.base = snapshot;
        self.tail.clear();
        self.snapshot = Some(self.base.clone());
        note_native_cps_i64_stack_replace::<i64>(self.len());
    }

    fn clear(&mut self) {
        let old_len = self.len();
        self.base = native_cps_i64_empty_snapshot();
        self.tail.clear();
        self.snapshot = Some(self.base.clone());
        note_native_cps_i64_stack_clear::<i64>(old_len);
    }

    fn push(&mut self, value: i64) {
        self.tail.push(value);
        self.snapshot = self
            .snapshot
            .as_ref()
            .map(|snapshot| snapshot.appended(value));
        note_native_cps_i64_stack_push::<i64>(self.len());
    }
}

fn call_native_i64_continuation(continuation: usize, env: &[i64], value: i64) -> i64 {
    // Safety: continuation pointers are produced from finalized JIT functions
    // and always use the `NativeCpsI64Continuation` ABI.
    let cont: NativeCpsI64Continuation = unsafe { std::mem::transmute(continuation) };
    cont(env.as_ptr(), value)
}

/// write27-d d2: prompt anchor captured at a Perform site. Mirrors
/// `CpsReprHandlerAnchor` — identifies which `(prompt, install_eval_id)`
/// pair was the matched real handler, so `apply_resumption`'s anchor
/// merge can drop redundant frames between the inherited and captured
/// portions of the resumption's stack.
#[derive(Debug, Clone, Copy)]
struct NativeCpsI64HandlerAnchor {
    prompt: u64,
    install_eval_id: u64,
}

#[derive(Debug, Clone, Copy)]
struct NativeCpsI64BlockedEffect {
    guard_id: i64,
    allowed_mask: i64,
    active: bool,
}

#[repr(C)]
pub(super) struct NativeCpsI64Resumption {
    code: NativeCpsI64Continuation,
    env: Box<[i64]>,
    handlers: NativeCpsI64HandlerSnapshot,
    guard_stack: NativeCpsI64I64Snapshot,
    /// write27-d d2: return-frame stack captured at the Perform call
    /// site. `effectful_apply_resumption` merges these with the new
    /// caller's frames (post-anchor) to rebuild Layer 1/2's
    /// `combined_frames`.
    return_frames: NativeCpsI64ReturnFrameSnapshot,
    /// write27-d d2: anchor for the matched real handler at capture
    /// time. `None` when the Perform site only saw a synthetic frame
    /// (no merge needed).
    handled_anchor: Option<NativeCpsI64HandlerAnchor>,
    debug_id: u64,
}

#[repr(C)]
struct NativeCpsI64Thunk {
    code: NativeCpsI64ThunkEntry,
    env: Box<[i64]>,
    handlers: NativeCpsI64HandlerSnapshot,
    guard_stack: NativeCpsI64I64Snapshot,
    active_blocked: Box<[NativeCpsI64BlockedEffect]>,
}

struct NativeCpsI64ThunkContext {
    handlers: NativeCpsI64HandlerSnapshot,
    guard_stack: NativeCpsI64I64Snapshot,
    active_blocked: Box<[NativeCpsI64BlockedEffect]>,
}

#[repr(C)]
struct NativeCpsI64Closure {
    code: NativeCpsI64ClosureEntry,
    env: Box<[i64]>,
    handlers: NativeCpsI64HandlerSnapshot,
    guard_stack: NativeCpsI64I64Snapshot,
}

enum NativeCpsI64HeapValue {
    Tuple(Box<[i64]>),
    Record(Vec<(Box<str>, i64)>),
    Variant { tag: i64, value: Option<i64> },
    List(ListTree<i64>),
    Bool(bool),
    Unit,
    Float(f64),
    String(StringTree<Box<str>>),
    Bytes(BytesTree),
    Path(std::path::PathBuf),
}

/// write27-d d1: tag where a `NativeCpsI64HandlerFrame` came from so
/// the trace + future origin-priority `select_handler` can distinguish
/// e.g. real installs from pending-env synthetic frames.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeCpsI64HandlerFrameOrigin {
    /// Installed by an `InstallHandler` stmt through
    /// `install_handler_full_i64_N` (real prompt + escape).
    RealInstall,
    /// Installed by the legacy `yulang_cps_install_handler_i64` (no
    /// escape continuation, synthetic eval id).
    LegacyInstall,
    /// Built by `take_pending_native_i64_handler_frames` — a placeholder
    /// constructed from pending capture envs without scope info.
    PendingEnv,
    /// Pushed by `yulang_cps_resume_with_handler_i64` on top of a
    /// resumption's handler snapshot.
    ResumeWithHandler,
    /// Synthetic fallback inserted by
    /// `current_native_i64_handler_stack_with_fallback` when the active
    /// stack is empty.
    StaticFallback,
}

#[derive(Clone)]
struct NativeCpsI64HandlerFrame {
    handler: i64,
    consumes_mask: i64,
    guard_stack: NativeCpsI64I64Snapshot,
    envs: NativeCpsI64HandlerEnvSnapshot,
    /// write27-c c2: dynamic prompt identity. Distinguishes frame
    /// instances installed under the same `CpsHandlerId` so that
    /// `ScopeReturn` targets a specific scope.
    prompt: u64,
    /// write27-c c2: which eval frame this handler was installed in.
    /// `ScopeReturn` routing only resolves a handler when current eval
    /// matches the install eval (mirrors cps_eval's CpsEvalId check).
    install_eval_id: u64,
    /// Function that owns the escape continuation. Layer 1/2 check this
    /// by name; the JIT keeps a compact id so frame-walk routing cannot
    /// jump to a continuation through a frame owned by a different
    /// function that happens to share the same eval id.
    escape_owner_function_id: u64,
    /// Owner function of the return frame immediately below this handler's
    /// dynamic extent at install time. Scoped abort uses this to know whether
    /// reaching `return_frame_threshold` means "resume the caller frame" or
    /// "keep escaping inside the same owner".
    threshold_owner_function_id: u64,
    /// write27-c c2: whether this frame was inherited from a captured
    /// resumption's handler stack (i.e., not freshly installed by an
    /// `InstallHandler` stmt in the current eval).
    inherited: bool,
    /// write27-c c2: JIT function pointer for the escape continuation
    /// (reached when the handler scope completes / aborts). 0 means
    /// "synthetic / no escape" (legacy passthrough).
    escape_continuation: usize,
    /// write27-c c2: env slots for the escape continuation. Stored as
    /// `Box<[i64]>` so the pointer stays stable while the frame lives.
    escape_env: NativeCpsI64I64Snapshot,
    escape_env_targets: NativeCpsI64I64Snapshot,
    /// write27-c c2: `return_frame_len` observed at install time. When
    /// a `ScopeReturn` resolves to this frame, the return-frame stack
    /// is truncated back to this length.
    return_frame_threshold: usize,
    return_frame_prefix: NativeCpsI64ReturnFrameSnapshot,
    /// write27-d d1: provenance tag for diagnostics. Not load-bearing
    /// (yet); informs the JIT trace and lets future steps gate
    /// `select_handler` on real-vs-synthetic origin.
    origin: NativeCpsI64HandlerFrameOrigin,
}

#[derive(Clone)]
struct NativeCpsI64HandlerEnv {
    entry: i64,
    env: i64,
    slots: Vec<(i64, i64)>,
}

/// write27-a: prompt-targeted non-local return for Cranelift JIT.
/// Mirrors `cps_eval::CpsRuntimeValue::ScopeReturn` and
/// `cps_repr::CpsReprRuntimeValue::ScopeReturn`.
#[derive(Debug, Clone, Default)]
struct NativeCpsI64ScopeReturn {
    active: bool,
    prompt: u64,
    target: i64,
    value: i64,
}

/// Legacy non-local short-circuit slot used by paths that have not yet moved
/// to prompt-targeted `ScopeReturn`. Keeping the shape explicit makes the next
/// scoped-abort step local to this type instead of spreading more
/// `Option<i64>` checks through the JIT helpers.
#[derive(Clone, Default)]
enum NativeCpsI64Abort {
    #[default]
    None,
    Global(i64),
    #[allow(dead_code)]
    Scoped {
        value: i64,
        return_frame_threshold: usize,
        propagate_at_threshold: bool,
        restore_frames: NativeCpsI64ReturnFrameSnapshot,
    },
    RoutedJump {
        value: i64,
        return_frame_threshold: usize,
        continuation: usize,
        env: NativeCpsI64I64Snapshot,
        handlers: Vec<NativeCpsI64HandlerFrame>,
        guards: Vec<i64>,
        return_frames: NativeCpsI64ReturnFrameSnapshot,
        eval_context: NativeCpsI64EvalContext,
    },
}

impl NativeCpsI64Abort {
    fn is_active(&self) -> bool {
        !matches!(self, NativeCpsI64Abort::None)
    }

    fn value_or_zero(&self) -> i64 {
        match self {
            NativeCpsI64Abort::None => 0,
            NativeCpsI64Abort::Global(value) => *value,
            NativeCpsI64Abort::Scoped { value, .. } => *value,
            NativeCpsI64Abort::RoutedJump { value, .. } => *value,
        }
    }

    fn mode_at_frame_len(&self, frame_len: usize) -> i64 {
        match self {
            NativeCpsI64Abort::None => 0,
            NativeCpsI64Abort::Global(_) => 1,
            NativeCpsI64Abort::Scoped {
                return_frame_threshold,
                propagate_at_threshold,
                ..
            } => {
                if frame_len > *return_frame_threshold
                    || (*propagate_at_threshold && frame_len == *return_frame_threshold)
                {
                    1
                } else {
                    2
                }
            }
            NativeCpsI64Abort::RoutedJump {
                return_frame_threshold,
                ..
            } => {
                if frame_len > *return_frame_threshold {
                    1
                } else {
                    2
                }
            }
        }
    }

    fn is_unguarded_routed_jump(&self) -> bool {
        matches!(
            self,
            NativeCpsI64Abort::RoutedJump { guards, .. } if guards.is_empty()
        )
    }

    fn is_routed_jump(&self) -> bool {
        matches!(self, NativeCpsI64Abort::RoutedJump { .. })
    }

    fn routed_jump_should_return(&self) -> bool {
        matches!(
            self,
            NativeCpsI64Abort::RoutedJump {
                return_frame_threshold,
                return_frames,
                ..
            } if *return_frame_threshold > 0 && !return_frames.is_empty()
        )
    }
}

/// write27-a/b: suspended caller continuation captured at
/// `EffectfulCall / EffectfulApply / EffectfulForce`. Mirrors
/// `CpsReturnFrame` from cps_eval/cps_repr but with raw function-
/// pointer continuation instead of a `CpsContinuationId`.
#[derive(Clone)]
struct NativeCpsI64ReturnFrame {
    prompt_exit: Option<NativeCpsI64PromptExitFrame>,
    debug_id: u64,
    /// JIT continuation function pointer
    /// (`extern "C" fn(env: *const i64, arg: i64) -> i64`, matching
    /// `NativeCpsI64Continuation`).
    continuation: usize,
    /// Debug-only CPS continuation id. `0` means the frame was built
    /// by a runtime helper that does not currently know the source id.
    continuation_id: u32,
    /// Captured environment for the continuation. Each `i64` mirrors
    /// one entry in the resume continuation's `environment`. Stored as
    /// `Box<[i64]>` (matches `NativeCpsI64Resumption::env`) so the
    /// pointer passed to the JIT continuation is stable.
    env: NativeCpsI64I64Snapshot,
    /// Handler stack snapshot at push time.
    handlers: NativeCpsI64HandlerSnapshot,
    /// Guard stack snapshot at push time.
    guards: NativeCpsI64I64Snapshot,
    /// Owner eval's `initial_frame_count` at push time.
    owner_initial_frame_count: usize,
    /// Owner eval's identity. Restored as `current_eval_id` when this
    /// frame is consumed via `continue_return_frame_i64`.
    owner_eval_id: u64,
    /// Function that owns `continuation`.
    owner_function_id: u64,
    /// write27-b: whether the resume continuation's body begins by
    /// `ForceThunk`-ing its first parameter (mirrors
    /// `return_frame_immediately_forces_param` in cps_eval/cps_repr).
    /// Computed at codegen time and stored here so the JIT Return path
    /// can fire pre-force v2 without crossing back into Cranelift IR.
    immediately_forces_param: bool,
}

#[derive(Clone)]
struct NativeCpsI64PromptExitFrame {
    prompt: u64,
}

impl NativeCpsI64SnapshotItem for i64 {
    fn collect_mmtk_trace_words(&self, out: &mut Vec<i64>) {
        out.push(*self);
    }
}

impl NativeCpsI64SnapshotItem for NativeCpsI64HandlerEnv {
    fn collect_mmtk_trace_words(&self, out: &mut Vec<i64>) {
        out.push(self.entry);
        out.push(self.env);
        for (target, value) in &self.slots {
            out.push(*target);
            out.push(*value);
        }
    }
}

impl NativeCpsI64SnapshotItem for NativeCpsI64HandlerFrame {
    fn collect_mmtk_trace_words(&self, out: &mut Vec<i64>) {
        out.push(self.handler);
        self.guard_stack.collect_mmtk_trace_words(out);
        self.envs.collect_mmtk_trace_words(out);
        self.escape_env.collect_mmtk_trace_words(out);
        self.escape_env_targets.collect_mmtk_trace_words(out);
        self.return_frame_prefix.collect_mmtk_trace_words(out);
    }
}

impl NativeCpsI64SnapshotItem for NativeCpsI64ReturnFrame {
    fn collect_mmtk_trace_words(&self, out: &mut Vec<i64>) {
        self.env.collect_mmtk_trace_words(out);
        self.handlers.collect_mmtk_trace_words(out);
        self.guards.collect_mmtk_trace_words(out);
    }
}

#[derive(Default)]
struct NativeCpsI64HandlerArmReturnFrameSnapshot {
    frames: Vec<NativeCpsI64ReturnFrame>,
    consumed_start: usize,
}

/// write27-a: per-eval-frame context. Mirrors the `current_eval_id` +
/// `initial_frame_count` parameters threaded through cps_eval.
#[derive(Debug, Clone, Copy, Default)]
struct NativeCpsI64EvalContext {
    current_eval_id: u64,
    initial_frame_count: usize,
}

#[derive(Clone, Default)]
struct NativeCpsI64PendingRoutedReturnFrames {
    skip_initial_frame_count: usize,
    frames: NativeCpsI64ReturnFrameSnapshot,
}

impl NativeCpsI64PendingRoutedReturnFrames {
    fn new(skip_initial_frame_count: usize, frames: NativeCpsI64ReturnFrameSnapshot) -> Self {
        Self {
            skip_initial_frame_count,
            frames,
        }
    }

    fn should_restore_for_initial(&self, initial: usize) -> bool {
        self.skip_initial_frame_count != initial
    }
}

/// write27-a: synthetic eval-id sentinel (matches
/// `cps_eval::SYNTHETIC_EVAL_ID`). Used for fallback handler frames
/// that should never resolve a `ScopeReturn`.
const NATIVE_CPS_I64_SYNTHETIC_EVAL_ID: u64 = u64::MAX;

/// write27-a: sentinel target for `ResumeWithHandler`-installed frames
/// (matches `cps_eval::EXIT_RWH_TARGET`). Stored as `i64`.
#[allow(dead_code)]
const NATIVE_CPS_I64_EXIT_RWH_TARGET: i64 = -1;

/// write27-c c1: env-guarded JIT runtime trace. Set
/// `YULANG_CPS_JIT_TRACE=1` to see push/return/route events as the
/// JIT-compiled code runs. The check itself is cached in a static, so
/// hot paths only pay one atomic load per call when disabled.
pub(super) fn jit_trace_enabled() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static STATE: AtomicU8 = AtomicU8::new(0); // 0 = uninit, 1 = off, 2 = on
    match STATE.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let on = std::env::var("YULANG_CPS_JIT_TRACE")
                .map(|v| v == "1")
                .unwrap_or(false);
            STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
    }
}

/// write27-e e4: debug toggle to skip the current-handler match in
/// `route_scope_return_i64` and force the frame-walk path. Used to
/// verify whether the test failure on Layer 3 is caused by an
/// over-eager current-handler match.
fn jit_force_frame_walk_sr() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static STATE: AtomicU8 = AtomicU8::new(0);
    match STATE.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let on = std::env::var("YULANG_CPS_JIT_FORCE_FRAME_WALK_SR")
                .map(|v| v == "1")
                .unwrap_or(false);
            STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
    }
}

thread_local! {
    static NATIVE_CPS_I64_STATS: RefCell<NativeCpsI64RuntimeStats> =
        RefCell::new(NativeCpsI64RuntimeStats::default());
    static NATIVE_CPS_I64_STATS_SITE: RefCell<NativeCpsI64StatsSite> =
        const { RefCell::new(NativeCpsI64StatsSite::General) };
    static NATIVE_CPS_I64_HEAP_VALUES: RefCell<HashSet<i64>> = RefCell::new(HashSet::new());
    static NATIVE_CPS_I64_TAG_NAMES: RefCell<HashMap<i64, Box<str>>> = RefCell::new(HashMap::new());
    static NATIVE_CPS_I64_THUNKS: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    static NATIVE_CPS_I64_CLOSURES: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    /// write27-d d4: pointers known to be `NativeCpsI64Resumption`,
    /// inserted at `make_native_i64_resumption` time. EffectfulApply
    /// codegen queries this set at runtime to dispatch between the
    /// closure path and the anchor-merging resumption path.
    static NATIVE_CPS_I64_RESUMPTIONS: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    static NATIVE_CPS_I64_ROOT_FUNCTION_IDS: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_HANDLER_STACK: RefCell<NativeCpsI64PersistentStack<NativeCpsI64HandlerFrame>> =
        RefCell::new(NativeCpsI64PersistentStack::default());
    static NATIVE_CPS_I64_GUARD_STACK: RefCell<NativeCpsI64GuardStack> =
        RefCell::new(NativeCpsI64GuardStack::default());
    static NATIVE_CPS_I64_ACTIVE_BLOCKED: RefCell<Vec<NativeCpsI64BlockedEffect>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_NEXT_GUARD: RefCell<i64> = const { RefCell::new(0) };
    static NATIVE_CPS_I64_NEXT_RESUMPTION_DEBUG_ID: RefCell<u64> = const { RefCell::new(1) };
    static NATIVE_CPS_I64_NEXT_RETURN_FRAME_DEBUG_ID: RefCell<u64> = const { RefCell::new(1) };
    static NATIVE_CPS_I64_PENDING_HANDLER_ENVS: RefCell<Vec<(i64, NativeCpsI64HandlerEnv)>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_PENDING_ESCAPE_ENV_TARGETS: RefCell<Vec<i64>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_SELECTED_HANDLER_ENVS: RefCell<Vec<NativeCpsI64HandlerEnv>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_SELECTED_HANDLER_ID: RefCell<i64> = const { RefCell::new(-1) };
    static NATIVE_CPS_I64_SELECTED_HANDLER_OWNER_FUNCTION_ID: RefCell<u64> = const { RefCell::new(0) };
    static NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV: RefCell<bool> = const { RefCell::new(false) };
    // Layer 2 keeps ResumeWithHandler siblings in the local active handler
    // stack until the surrounding scope-return dispatch decides whether the
    // flow is local or non-local. The JIT rebuilds that stack from snapshots,
    // so the sibling frames need a small side table for later frame restores.
    static NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS: RefCell<Vec<NativeCpsI64HandlerFrame>> =
        const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_ABORT: RefCell<NativeCpsI64Abort> =
        const { RefCell::new(NativeCpsI64Abort::None) };
    static NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET: RefCell<usize> = const { RefCell::new(0) };
    // write27-a: ScopeReturn slot. Mirrors `cps_eval`/`cps_repr`'s
    // ScopeReturn variant. Set by the new `yulang_cps_scope_return_i64`
    // helper (called by Perform codegen once it migrates) and read by
    // the route_scope_return helper after every internal call.
    static NATIVE_CPS_I64_SCOPE_RETURN: RefCell<NativeCpsI64ScopeReturn> =
        const { RefCell::new(NativeCpsI64ScopeReturn {
            active: false,
            prompt: 0,
            target: 0,
            value: 0,
        }) };
    // write27-a: return-frame stack. Each EffectfulCall/Force/Apply
    // pushes a frame here; Return consumes them via the
    // continue_return_frames helper.
    static NATIVE_CPS_I64_RETURN_FRAMES: RefCell<NativeCpsI64PersistentStack<NativeCpsI64ReturnFrame>> =
        RefCell::new(NativeCpsI64PersistentStack::default());
    static NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES: RefCell<Option<NativeCpsI64PendingRoutedReturnFrames>> =
        const { RefCell::new(None) };
    static NATIVE_CPS_I64_RETURN_FRAMES_ROUTED: RefCell<bool> = const { RefCell::new(false) };
    static NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS: RefCell<Vec<u64>> =
        const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_HANDLER_ARM_RETURN_FRAME_SNAPSHOTS: RefCell<Vec<NativeCpsI64HandlerArmReturnFrameSnapshot>> =
        const { RefCell::new(Vec::new()) };
    // write27-a: per-eval context (current eval id + initial frame
    // count). Threaded explicitly in cps_eval/cps_repr; here we use
    // a thread-local because adding hidden params to every JIT
    // continuation would balloon the codegen.
    static NATIVE_CPS_I64_EVAL_CONTEXT: RefCell<NativeCpsI64EvalContext> =
        const { RefCell::new(NativeCpsI64EvalContext {
            current_eval_id: 0,
            initial_frame_count: 0,
        }) };
    // write27-a: monotonic counter for fresh eval ids. Mirrors
    // `cps_eval::EVAL_ID_COUNTER`.
    static NATIVE_CPS_I64_NEXT_EVAL_ID: RefCell<u64> = const { RefCell::new(0) };
    // write27-c c2: monotonic counter for fresh prompt ids. Each
    // `InstallHandler` stmt that uses the full helper gets a unique
    // prompt; `ScopeReturn` carries this prompt to disambiguate which
    // scope to dispatch to.
    static NATIVE_CPS_I64_NEXT_PROMPT: RefCell<u64> = const { RefCell::new(1) };
    // write27-c c3: snapshot of the handler stack saved when
    // `select_handler` truncates. The Perform arm body runs with the
    // truncated stack (matching Layer 1/2's `handler_body_stack`
    // semantics); `restore_outer_handler_stack` reinstates the
    // pre-truncation stack so the post-arm `route_scope_return` can
    // walk it. Stored as a stack to support nested Performs.
    static NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS: RefCell<Vec<Vec<NativeCpsI64HandlerFrame>>> =
        const { RefCell::new(Vec::new()) };
    // write27-c c3: metadata for the handler frame just selected by
    // `select_handler` (prompt, escape continuation, escape env,
    // return-frame threshold, install eval id, synthetic flag). The
    // Perform path uses this to wrap the arm's natural return as a
    // ScopeReturn pointing at the selected handler's escape.
    static NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK: RefCell<Vec<NativeCpsI64SelectedHandlerMeta>> =
        const { RefCell::new(Vec::new()) };
}

fn reset_native_i64_cps_stats() {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    NATIVE_CPS_I64_STATS.with(|stats| *stats.borrow_mut() = NativeCpsI64RuntimeStats::default());
}

fn dump_native_i64_stack_stats(kind: NativeCpsI64StackKind, stats: &NativeCpsI64StackStats) {
    eprintln!(
        "[JIT-CPS-STATS] stack={} snapshot_calls={} snapshot_hits={} snapshot_misses={} snapshot_items_cloned={} snapshot_len_0={} snapshot_len_1_4={} snapshot_len_5_16={} snapshot_len_17_plus={} push={} pop={} pop_some={} replace={} replace_items={} take={} take_items={} clear={} truncate={} truncated_items={} max_len={}",
        kind.label(),
        stats.snapshot_calls,
        stats.snapshot_hits,
        stats.snapshot_misses,
        stats.snapshot_items_cloned,
        stats.snapshot_len_0,
        stats.snapshot_len_1_4,
        stats.snapshot_len_5_16,
        stats.snapshot_len_17_plus,
        stats.push_calls,
        stats.pop_calls,
        stats.pop_some,
        stats.replace_calls,
        stats.replace_items,
        stats.take_calls,
        stats.take_items,
        stats.clear_calls,
        stats.truncate_calls,
        stats.truncated_items,
        stats.max_len,
    );
}

fn dump_native_i64_site_stack_stats(
    site: NativeCpsI64StatsSite,
    kind: NativeCpsI64StackKind,
    stats: &NativeCpsI64StackSiteStats,
) {
    if stats.snapshot_calls == 0 && stats.replace_calls == 0 {
        return;
    }
    eprintln!(
        "[JIT-CPS-STATS] site={} stack={} snapshot_calls={} snapshot_misses={} snapshot_items_cloned={} replace={} replace_items={} replace_empty={}",
        site.label(),
        kind.label(),
        stats.snapshot_calls,
        stats.snapshot_misses,
        stats.snapshot_items_cloned,
        stats.replace_calls,
        stats.replace_items,
        stats.replace_empty,
    );
}

fn dump_native_i64_cps_stats() {
    if !native_cps_i64_stats_enabled() {
        return;
    }
    NATIVE_CPS_I64_STATS.with(|stats| {
        let stats = stats.borrow().clone();
        eprintln!(
            "[JIT-CPS-STATS] control make_resumption={} make_thunk={} make_closure={} add_thunk_boundary={} force_thunk={} continue_return_frame={} return_i64={} root_result={}",
            stats.make_resumption_calls,
            stats.make_thunk_calls,
            stats.make_closure_calls,
            stats.add_thunk_boundary_calls,
            stats.force_thunk_calls,
            stats.continue_return_frame_calls,
            stats.return_i64_calls,
            stats.root_result_calls,
        );
        dump_native_i64_stack_stats(NativeCpsI64StackKind::ReturnFrames, &stats.return_frames);
        dump_native_i64_stack_stats(NativeCpsI64StackKind::HandlerStack, &stats.handler_stack);
        dump_native_i64_stack_stats(NativeCpsI64StackKind::GuardStack, &stats.guard_stack);
        for site in NativeCpsI64StatsSite::all() {
            dump_native_i64_site_stack_stats(
                site,
                NativeCpsI64StackKind::ReturnFrames,
                &stats.site_stacks[site.index()][NativeCpsI64StackKind::ReturnFrames.index()],
            );
            dump_native_i64_site_stack_stats(
                site,
                NativeCpsI64StackKind::HandlerStack,
                &stats.site_stacks[site.index()][NativeCpsI64StackKind::HandlerStack.index()],
            );
            dump_native_i64_site_stack_stats(
                site,
                NativeCpsI64StackKind::GuardStack,
                &stats.site_stacks[site.index()][NativeCpsI64StackKind::GuardStack.index()],
            );
        }
    });
}

/// write27-c c3: meta captured at `select_handler` time about the
/// selected frame, so the Perform post-arm path can synthesize a
/// `ScopeReturn` targeting its escape without re-walking the stack.
#[derive(Clone)]
#[allow(dead_code)]
struct NativeCpsI64SelectedHandlerMeta {
    prompt: u64,
    escape_continuation: usize,
    escape_env: NativeCpsI64I64Snapshot,
    return_frame_threshold: usize,
    install_eval_id: u64,
    synthetic: bool,
}

#[derive(Clone)]
struct NativeCpsI64CurrentScopeHandlerMatch {
    handler_index: usize,
    handler: NativeCpsI64HandlerFrame,
}

#[derive(Clone)]
struct NativeCpsI64ReturnFrameScopeHandlerMatch {
    return_frame_index: usize,
    handler_index: usize,
    return_frame: NativeCpsI64ReturnFrame,
    handler: NativeCpsI64HandlerFrame,
}

pub(super) fn reset_native_i64_cps_state() {
    reset_native_i64_cps_stats();
    NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow_mut().clear());
    NATIVE_CPS_I64_TAG_NAMES.with(|names| names.borrow_mut().clear());
    NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow_mut().clear());
    NATIVE_CPS_I64_CLOSURES.with(|closures| closures.borrow_mut().clear());
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow_mut().clear());
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow_mut().clear());
    NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| stack.borrow_mut().clear());
    NATIVE_CPS_I64_NEXT_GUARD.with(|next| *next.borrow_mut() = 0);
    NATIVE_CPS_I64_NEXT_RESUMPTION_DEBUG_ID.with(|next| *next.borrow_mut() = 1);
    NATIVE_CPS_I64_NEXT_RETURN_FRAME_DEBUG_ID.with(|next| *next.borrow_mut() = 1);
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
    NATIVE_CPS_I64_PENDING_ESCAPE_ENV_TARGETS.with(|targets| targets.borrow_mut().clear());
    NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
    NATIVE_CPS_I64_SELECTED_HANDLER_ID.with(|handler| *handler.borrow_mut() = -1);
    NATIVE_CPS_I64_SELECTED_HANDLER_OWNER_FUNCTION_ID.with(|owner| *owner.borrow_mut() = 0);
    NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow_mut() = false);
    NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|handlers| handlers.borrow_mut().clear());
    NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::None);
    NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET.with(|slot| *slot.borrow_mut() = 0);
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64ScopeReturn::default();
    });
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().clear());
    clear_pending_native_i64_routed_return_frames();
    NATIVE_CPS_I64_RETURN_FRAMES_ROUTED.with(|routed| *routed.borrow_mut() = false);
    NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| ids.borrow_mut().clear());
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = NativeCpsI64EvalContext::default();
    });
    NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| *next.borrow_mut() = 0);
    NATIVE_CPS_I64_NEXT_PROMPT.with(|next| *next.borrow_mut() = 1);
    NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| snaps.borrow_mut().clear());
    NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|meta| meta.borrow_mut().clear());
    NATIVE_CPS_I64_RESUMPTIONS.with(|s| s.borrow_mut().clear());
    NATIVE_CPS_I64_ROOT_FUNCTION_IDS.with(|ids| ids.borrow_mut().clear());
}

pub(super) fn set_native_i64_root_function_ids(ids: &[u64]) {
    NATIVE_CPS_I64_ROOT_FUNCTION_IDS.with(|slot| {
        *slot.borrow_mut() = ids.to_vec();
    });
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_reset_i64() {
    reset_native_i64_cps_state();
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_dump_stats_i64() {
    dump_native_i64_cps_stats();
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_set_root_function_ids_i64(ids: *const u64, len: usize) {
    if ids.is_null() {
        if len == 0 {
            set_native_i64_root_function_ids(&[]);
        }
        return;
    }
    let ids = unsafe { std::slice::from_raw_parts(ids, len) };
    set_native_i64_root_function_ids(ids);
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_take_root_result_i64(value: i64) -> i64 {
    take_native_i64_root_result(value)
}

pub(super) fn take_native_i64_root_result(value: i64) -> i64 {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::RootResult);
    with_native_cps_i64_stats(|stats| stats.root_result_calls += 1);
    let mode = yulang_cps_abort_mode_i64();
    if mode == 0 {
        return value;
    }
    let abort = if mode == 2 {
        yulang_cps_consume_abort_i64()
    } else {
        let value = yulang_cps_abort_value_i64();
        let _ = yulang_cps_clear_abort_i64();
        value
    };
    let _ = yulang_cps_clear_scope_return_i64();
    // The root boundary owns abort extraction. Leftover prompt-exit frames came
    // from skipped native callers and would re-apply handler value arms if a
    // thunk payload had to be forced for display.
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().clear());
    force_native_i64_root_result(abort)
}

fn force_native_i64_root_result(value: i64) -> i64 {
    let is_thunk = usize::try_from(value)
        .ok()
        .is_some_and(|value| NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value)));
    if is_thunk {
        yulang_cps_force_thunk_i64(value as usize)
    } else {
        value
    }
}

fn native_i64_abort_is_routed_jump() -> bool {
    NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().is_routed_jump())
}

fn native_i64_abort_is_unguarded_routed_jump() -> bool {
    NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().is_unguarded_routed_jump())
}

fn native_i64_abort_should_consume_after_thunk_force() -> bool {
    native_i64_abort_is_unguarded_routed_jump() && yulang_cps_abort_mode_i64() == 2
}

fn current_native_i64_guard_snapshot() -> NativeCpsI64I64Snapshot {
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow_mut().snapshot())
}

fn current_native_i64_handler_snapshot_with_pending() -> NativeCpsI64HandlerSnapshot {
    let pending = take_pending_native_i64_handler_frames();
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        if pending.is_empty() {
            stack.snapshot()
        } else {
            let mut handlers = stack.to_vec();
            handlers.extend(pending);
            native_cps_i64_snapshot(handlers)
        }
    })
}

fn current_native_i64_handler_stack_with_fallback(
    fallback: i64,
    effect_mask: i64,
) -> Vec<NativeCpsI64HandlerFrame> {
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let stack = stack.borrow();
        if stack.is_empty() && fallback >= 0 {
            vec![NativeCpsI64HandlerFrame {
                handler: fallback,
                consumes_mask: effect_mask,
                guard_stack: current_native_i64_guard_snapshot(),
                envs: native_cps_i64_empty_snapshot(),
                prompt: 0,
                install_eval_id: NATIVE_CPS_I64_SYNTHETIC_EVAL_ID,
                escape_owner_function_id: 0,
                threshold_owner_function_id: 0,
                inherited: false,
                escape_continuation: 0,
                escape_env: native_cps_i64_empty_snapshot(),
                escape_env_targets: native_cps_i64_empty_snapshot(),
                return_frame_threshold: 0,
                return_frame_prefix: native_cps_i64_snapshot(Vec::new()),
                origin: NativeCpsI64HandlerFrameOrigin::StaticFallback,
            }]
        } else {
            stack.to_vec()
        }
    })
}

fn take_pending_native_i64_handler_frames() -> Vec<NativeCpsI64HandlerFrame> {
    let pending =
        NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| std::mem::take(&mut *envs.borrow_mut()));
    let mut frames: Vec<NativeCpsI64HandlerFrame> = Vec::new();
    for (handler, env) in pending {
        if let Some(frame) = frames.iter_mut().find(|frame| frame.handler == handler) {
            let mut envs = frame.envs.to_vec();
            envs.push(env);
            frame.envs = native_cps_i64_snapshot(envs);
        } else {
            frames.push(NativeCpsI64HandlerFrame {
                handler,
                consumes_mask: -1,
                guard_stack: current_native_i64_guard_snapshot(),
                envs: native_cps_i64_snapshot(vec![env]),
                prompt: 0,
                install_eval_id: NATIVE_CPS_I64_SYNTHETIC_EVAL_ID,
                escape_owner_function_id: 0,
                threshold_owner_function_id: 0,
                inherited: false,
                escape_continuation: 0,
                escape_env: native_cps_i64_empty_snapshot(),
                escape_env_targets: native_cps_i64_empty_snapshot(),
                return_frame_threshold: 0,
                return_frame_prefix: native_cps_i64_snapshot(Vec::new()),
                origin: NativeCpsI64HandlerFrameOrigin::PendingEnv,
            });
        }
    }
    frames
}

fn take_pending_native_i64_handler_envs(handler: i64) -> Vec<NativeCpsI64HandlerEnv> {
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| {
        let mut envs = envs.borrow_mut();
        let mut selected = Vec::new();
        let mut index = 0;
        while index < envs.len() {
            if envs[index].0 == handler {
                selected.push(envs.remove(index).1);
            } else {
                index += 1;
            }
        }
        selected
    })
}

fn take_pending_native_i64_escape_env_targets() -> Vec<i64> {
    NATIVE_CPS_I64_PENDING_ESCAPE_ENV_TARGETS
        .with(|targets| std::mem::take(&mut *targets.borrow_mut()))
}

fn with_native_i64_cps_state_guard_snapshot<T>(
    handlers: Vec<NativeCpsI64HandlerFrame>,
    guard_stack: NativeCpsI64I64Snapshot,
    run: impl FnOnce() -> T,
) -> T {
    let previous_handlers =
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow_mut().replace(handlers));
    let previous_guards =
        NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow_mut().replace_snapshot(guard_stack));
    let result = run();
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        stack.borrow_mut().replace(previous_handlers);
    });
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
        stack.borrow_mut().restore_snapshot(previous_guards);
    });
    result
}

fn with_native_i64_cps_state_override_guard_snapshot<T>(
    handlers: Option<Vec<NativeCpsI64HandlerFrame>>,
    guard_stack: Option<NativeCpsI64I64Snapshot>,
    active_blocked: Vec<NativeCpsI64BlockedEffect>,
    run: impl FnOnce() -> T,
) -> T {
    let previous_handlers = handlers.map(|handlers| {
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow_mut().replace(handlers))
    });
    let previous_guards = guard_stack.map(|guard_stack| {
        NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow_mut().replace_snapshot(guard_stack))
    });
    let previous_active = NATIVE_CPS_I64_ACTIVE_BLOCKED
        .with(|stack| std::mem::replace(&mut *stack.borrow_mut(), active_blocked));
    let result = run();
    if let Some(previous_handlers) = previous_handlers {
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
            stack.borrow_mut().replace(previous_handlers);
        });
    }
    if let Some(previous_guards) = previous_guards {
        NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
            stack.borrow_mut().restore_snapshot(previous_guards);
        });
    }
    NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| *stack.borrow_mut() = previous_active);
    result
}

#[allow(dead_code)]
fn native_i64_handler_stack_with_captured(
    captured: &[NativeCpsI64HandlerFrame],
) -> Vec<NativeCpsI64HandlerFrame> {
    let mut handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().to_vec());
    handlers.extend(captured.iter().cloned());
    handlers
}

#[allow(dead_code)]
fn native_i64_handler_stack_for_force(
    captured: &[NativeCpsI64HandlerFrame],
) -> Vec<NativeCpsI64HandlerFrame> {
    let mut handlers = native_i64_handler_stack_with_captured(captured);
    handlers.extend(take_pending_native_i64_handler_frames());
    handlers
}

fn next_native_i64_resumption_debug_id() -> u64 {
    NATIVE_CPS_I64_NEXT_RESUMPTION_DEBUG_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    })
}

fn next_native_i64_return_frame_debug_id() -> u64 {
    NATIVE_CPS_I64_NEXT_RETURN_FRAME_DEBUG_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    })
}

fn make_native_i64_resumption(
    code: usize,
    fallback_handler: i64,
    env: Vec<i64>,
) -> *mut NativeCpsI64Resumption {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::MakeResumption);
    with_native_cps_i64_stats(|stats| stats.make_resumption_calls += 1);
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64Continuation>(code) };
    // write27-d d2: capture the full Layer 1/2 resumption state.
    // `handled_anchor` is filled in later by
    // `yulang_cps_set_resumption_anchor_from_selected_i64` once
    // `select_handler` has decided which real handler was matched.
    let return_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().snapshot());
    let handlers = current_native_i64_handler_stack_with_fallback(fallback_handler, -1);
    let debug_id = next_native_i64_resumption_debug_id();
    let trace_handlers = jit_trace_enabled().then(|| handlers.clone());
    let ptr = Box::into_raw(Box::new(NativeCpsI64Resumption {
        code,
        env: env.into_boxed_slice(),
        handlers: native_cps_i64_snapshot(handlers),
        guard_stack: current_native_i64_guard_snapshot(),
        return_frames,
        handled_anchor: None,
        debug_id,
    }));
    NATIVE_CPS_I64_RESUMPTIONS.with(|s| {
        s.borrow_mut().insert(ptr as usize);
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] make_resumption: id={} ptr={:#x} handlers={} frames={}",
            debug_id,
            ptr as usize,
            format_handler_stack(trace_handlers.as_deref().unwrap_or(&[])),
            format_return_frames(unsafe { &(*ptr).return_frames }),
        );
    }
    ptr
}

/// write27-d d2: after `select_handler` records meta about the chosen
/// real handler, write that `(prompt, install_eval_id)` as the
/// resumption's `handled_anchor`. Called from the Perform codegen
/// immediately after `select_handler_i64` and before the arm call.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_set_resumption_anchor_from_selected_i64(
    resumption: *mut NativeCpsI64Resumption,
) -> i64 {
    let meta = NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|m| m.borrow().last().cloned());
    if let Some(meta) = meta {
        if !meta.synthetic && meta.escape_continuation != 0 {
            unsafe {
                (*resumption).handled_anchor = Some(NativeCpsI64HandlerAnchor {
                    prompt: meta.prompt,
                    install_eval_id: meta.install_eval_id,
                });
                let start = native_i64_prompt_frame_start(
                    &(*resumption).return_frames,
                    meta.prompt,
                    meta.return_frame_threshold,
                );
                (*resumption).return_frames = capture_native_i64_return_frames_from_start(
                    &(*resumption).return_frames,
                    start,
                    meta.install_eval_id,
                );
                rebase_native_i64_captured_handlers(
                    (*resumption).handlers.make_mut(),
                    start,
                    meta.install_eval_id,
                );
                // Inherited handlers (install_eval < anchor's install_eval) keep
                // their original absolute threshold after the shared rebase. When
                // the resumption is replayed inside an unrelated outer eval, the
                // slice frame layout no longer matches the original install
                // position, so re-derive the threshold from the prompt-exit
                // marker actually present in the slice. Apply the same fix to
                // each frame's handler snapshot.
                recalibrate_inherited_handler_thresholds(
                    (*resumption).handlers.make_mut(),
                    &(*resumption).return_frames,
                    meta.install_eval_id,
                );
                let slice_snapshot = (*resumption).return_frames.clone();
                for frame in (*resumption).return_frames.make_mut() {
                    recalibrate_inherited_handler_thresholds(
                        frame.handlers.make_mut(),
                        &slice_snapshot,
                        meta.install_eval_id,
                    );
                }
            }
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] resumption_anchor: prompt={} install_eval={} frames={}",
                    meta.prompt,
                    meta.install_eval_id,
                    unsafe { format_return_frames(&(*resumption).return_frames) }
                );
            }
        }
    }
    0
}

fn make_native_i64_thunk(code: usize, env: Vec<i64>) -> usize {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::MakeThunk);
    with_native_cps_i64_stats(|stats| stats.make_thunk_calls += 1);
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64ThunkEntry>(code) };
    make_native_i64_thunk_from_parts(
        code,
        env,
        current_native_i64_handler_snapshot_with_pending(),
        current_native_i64_guard_snapshot(),
        Vec::new(),
    )
}

fn make_native_i64_thunk_from_parts(
    code: NativeCpsI64ThunkEntry,
    env: Vec<i64>,
    handlers: NativeCpsI64HandlerSnapshot,
    guard_stack: NativeCpsI64I64Snapshot,
    active_blocked: Vec<NativeCpsI64BlockedEffect>,
) -> usize {
    let ptr = Box::into_raw(Box::new(NativeCpsI64Thunk {
        code,
        env: env.into_boxed_slice(),
        handlers,
        guard_stack,
        active_blocked: active_blocked.into_boxed_slice(),
    })) as usize;
    NATIVE_CPS_I64_THUNKS.with(|thunks| {
        thunks.borrow_mut().insert(ptr);
    });
    ptr
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_capture_thunk_context_i64() -> usize {
    let context = NativeCpsI64ThunkContext {
        handlers: current_native_i64_handler_snapshot_with_pending(),
        guard_stack: current_native_i64_guard_snapshot(),
        active_blocked: Vec::new().into_boxed_slice(),
    };
    Box::into_raw(Box::new(context)) as usize
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_thunk_context_add_boundary_i64(
    context: usize,
    guard_id: i64,
    allowed_mask: i64,
    active: i64,
) -> usize {
    let context = unsafe { &*(context as *const NativeCpsI64ThunkContext) };
    let mut active_blocked = context.active_blocked.to_vec();
    active_blocked.push(NativeCpsI64BlockedEffect {
        guard_id,
        allowed_mask,
        active: active != 0,
    });
    Box::into_raw(Box::new(NativeCpsI64ThunkContext {
        handlers: context.handlers.clone(),
        guard_stack: context.guard_stack.clone(),
        active_blocked: active_blocked.into_boxed_slice(),
    })) as usize
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_add_thunk_boundary_i64(
    value: usize,
    guard_id: i64,
    allowed_mask: i64,
    active: i64,
) -> usize {
    with_native_cps_i64_stats(|stats| stats.add_thunk_boundary_calls += 1);
    let is_thunk = NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value));
    if !is_thunk {
        return value;
    }
    let thunk = unsafe { &*(value as *const NativeCpsI64Thunk) };
    let mut active_blocked = thunk.active_blocked.to_vec();
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] add_thunk_boundary: thunk={:#x} guard={} allowed_mask={} active={} existing={}",
            value,
            guard_id,
            allowed_mask,
            active,
            thunk.active_blocked.len(),
        );
    }
    active_blocked.push(NativeCpsI64BlockedEffect {
        guard_id,
        allowed_mask,
        active: active != 0,
    });
    let ptr = Box::into_raw(Box::new(NativeCpsI64Thunk {
        code: thunk.code,
        env: thunk.env.clone(),
        handlers: thunk.handlers.clone(),
        guard_stack: thunk.guard_stack.clone(),
        active_blocked: active_blocked.into_boxed_slice(),
    })) as usize;
    NATIVE_CPS_I64_THUNKS.with(|thunks| {
        thunks.borrow_mut().insert(ptr);
    });
    ptr
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_add_empty_context_thunk_boundary_i64(
    code: usize,
    env_ptr: *const i64,
    env_len: i64,
    guard_id: i64,
    allowed_mask: i64,
    active: i64,
) -> usize {
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64ThunkEntry>(code) };
    let value = make_native_i64_thunk_from_parts(
        code,
        unsafe { native_i64_slice(env_ptr, env_len) },
        native_cps_i64_empty_snapshot(),
        native_cps_i64_empty_snapshot(),
        Vec::new(),
    );
    yulang_cps_add_thunk_boundary_i64(value, guard_id, allowed_mask, active)
}

fn make_native_i64_closure(code: usize, env: Vec<i64>) -> usize {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::MakeClosure);
    with_native_cps_i64_stats(|stats| stats.make_closure_calls += 1);
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64ClosureEntry>(code) };
    let handlers = current_native_i64_handler_snapshot_with_pending();
    let ptr = Box::into_raw(Box::new(NativeCpsI64Closure {
        code,
        env: env.into_boxed_slice(),
        handlers,
        guard_stack: current_native_i64_guard_snapshot(),
    })) as usize;
    NATIVE_CPS_I64_CLOSURES.with(|closures| {
        closures.borrow_mut().insert(ptr);
    });
    ptr
}

fn make_native_i64_recursive_closure(code: usize, self_slot: usize, mut env: Vec<i64>) -> usize {
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64ClosureEntry>(code) };
    let closure = Box::into_raw(Box::new(NativeCpsI64Closure {
        code,
        env: Vec::new().into_boxed_slice(),
        handlers: native_cps_i64_snapshot(Vec::new()),
        guard_stack: native_cps_i64_snapshot(Vec::new()),
    }));
    let ptr = closure as usize;
    if self_slot < env.len() {
        env[self_slot] = ptr as i64;
    }
    unsafe {
        (*closure).env = env.into_boxed_slice();
        (*closure).handlers = current_native_i64_handler_snapshot_with_pending();
        (*closure).guard_stack = current_native_i64_guard_snapshot();
    }
    NATIVE_CPS_I64_CLOSURES.with(|closures| {
        closures.borrow_mut().insert(ptr);
    });
    ptr
}

fn make_native_i64_env(env: Vec<i64>) -> *const i64 {
    Box::leak(env.into_boxed_slice()).as_ptr()
}

unsafe fn native_i64_slice(ptr: *const i64, len: i64) -> Vec<i64> {
    let Ok(len) = usize::try_from(len) else {
        return Vec::new();
    };
    if len == 0 {
        return Vec::new();
    }
    if ptr.is_null() {
        return Vec::new();
    }
    unsafe { std::slice::from_raw_parts(ptr, len) }.to_vec()
}

fn native_cps_i64_heap(value: NativeCpsI64HeapValue) -> i64 {
    let pointer = Box::into_raw(Box::new(value)) as i64;
    NATIVE_CPS_I64_HEAP_VALUES.with(|values| {
        values.borrow_mut().insert(pointer);
    });
    pointer
}

fn native_cps_i64_variant(tag: &str, value: Option<i64>) -> i64 {
    let hash = tag_hash(&typed_ir::Name(tag.to_string()));
    register_native_i64_tag_name(hash, tag);
    native_cps_i64_heap(NativeCpsI64HeapValue::Variant { tag: hash, value })
}

fn register_native_i64_tag_name(tag: i64, name: &str) {
    NATIVE_CPS_I64_TAG_NAMES.with(|names| {
        names
            .borrow_mut()
            .entry(tag)
            .or_insert_with(|| name.to_string().into_boxed_str());
    });
}

fn native_i64_tag_name(tag: i64) -> String {
    NATIVE_CPS_I64_TAG_NAMES.with(|names| {
        names
            .borrow()
            .get(&tag)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{tag}"))
    })
}

fn native_cps_i64_string_from_raw(ptr: *const u8, len: i64) -> Option<String> {
    if ptr.is_null() || len < 0 {
        return None;
    }
    let len = usize::try_from(len).ok()?;
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    std::str::from_utf8(bytes).ok().map(str::to_string)
}

pub(super) fn describe_cps_repr_i64_value(value: i64) -> String {
    describe_native_i64_value(value)
}

pub(super) fn describe_cps_repr_i64_value_with_hint(
    value: i64,
    hint: &CpsRootDisplayHint,
) -> String {
    match hint {
        CpsRootDisplayHint::Unit if value == 0 => "()".to_string(),
        CpsRootDisplayHint::Bool => {
            if value == 0 {
                "false".to_string()
            } else {
                "true".to_string()
            }
        }
        CpsRootDisplayHint::Tuple(item_hints) => {
            describe_native_i64_tuple_with_hints(value, item_hints)
                .unwrap_or_else(|| describe_cps_repr_i64_value(value))
        }
        CpsRootDisplayHint::List(item_hint) => describe_native_i64_list_with_hint(value, item_hint)
            .unwrap_or_else(|| describe_cps_repr_i64_value(value)),
        _ => describe_cps_repr_i64_value(value),
    }
}

fn describe_native_i64_tuple_with_hints(
    value: i64,
    item_hints: &[CpsRootDisplayHint],
) -> Option<String> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return None;
    }
    let heap = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Tuple(items) = heap else {
        return None;
    };
    let rendered = items
        .iter()
        .enumerate()
        .map(|(index, item)| match item_hints.get(index) {
            Some(hint) => describe_cps_repr_i64_value_with_hint(*item, hint),
            None => describe_native_i64_value_with_depth(*item, 1),
        })
        .collect::<Vec<_>>();
    Some(match rendered.as_slice() {
        [] => "()".to_string(),
        [single] => format!("({single},)"),
        _ => format!("({})", rendered.join(", ")),
    })
}

fn describe_native_i64_list_with_hint(
    value: i64,
    item_hint: &CpsRootDisplayHint,
) -> Option<String> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return None;
    }
    let heap = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::List(items) = heap else {
        return None;
    };
    Some(format!(
        "[{}]",
        items
            .to_vec()
            .iter()
            .map(|item| describe_cps_repr_i64_value_with_hint(*item, item_hint))
            .collect::<Vec<_>>()
            .join(", ")
    ))
}

pub(super) fn describe_native_i64_value(value: i64) -> String {
    describe_native_i64_value_with_depth(value, 0)
}

fn describe_native_i64_debug_value(value: i64) -> String {
    describe_native_i64_debug_value_with_depth(value, 0)
}

fn describe_native_i64_value_with_depth(value: i64, depth: usize) -> String {
    if depth > 32 {
        return "...".to_string();
    }
    let resumption_id = NATIVE_CPS_I64_RESUMPTIONS.with(|resumptions| {
        if resumptions.borrow().contains(&(value as usize)) {
            Some(unsafe { (*(value as *const NativeCpsI64Resumption)).debug_id })
        } else {
            None
        }
    });
    if let Some(id) = resumption_id {
        return format!("resumption#{id}@{value:#x}");
    }

    let is_thunk = NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&(value as usize)));
    if is_thunk {
        return format!("thunk@{value:#x}");
    }

    let is_closure =
        NATIVE_CPS_I64_CLOSURES.with(|closures| closures.borrow().contains(&(value as usize)));
    if is_closure {
        return format!("closure@{value:#x}");
    }

    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return value.to_string();
    }

    let heap = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match heap {
        NativeCpsI64HeapValue::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| describe_native_i64_value_with_depth(*item, depth + 1))
                .collect::<Vec<_>>();
            match items.as_slice() {
                [] => "()".to_string(),
                [single] => format!("({single},)"),
                _ => format!("({})", items.join(", ")),
            }
        }
        NativeCpsI64HeapValue::Record(fields) => format!(
            "{{ {} }}",
            fields
                .iter()
                .map(|(name, value)| format!(
                    "{name}: {}",
                    describe_native_i64_value_with_depth(*value, depth + 1)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        NativeCpsI64HeapValue::Variant { tag, value: None } => {
            format!(":{}", native_i64_tag_name(*tag))
        }
        NativeCpsI64HeapValue::Variant {
            tag,
            value: Some(payload),
        } => format!(
            ":{} {}",
            native_i64_tag_name(*tag),
            describe_native_i64_value_with_depth(*payload, depth + 1)
        ),
        NativeCpsI64HeapValue::List(items) => format!(
            "[{}]",
            items
                .to_vec()
                .iter()
                .map(|item| describe_native_i64_value_with_depth(*item, depth + 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        NativeCpsI64HeapValue::Bool(value) => value.to_string(),
        NativeCpsI64HeapValue::Unit => "()".to_string(),
        NativeCpsI64HeapValue::Float(value) => native_cps_format_float(*value),
        NativeCpsI64HeapValue::String(text) => text.to_flat_string(),
        NativeCpsI64HeapValue::Bytes(value) => format!("<bytes len={}>", value.len()),
        NativeCpsI64HeapValue::Path(value) => value.display().to_string(),
    }
}

fn describe_native_i64_debug_value_with_depth(value: i64, depth: usize) -> String {
    if depth > 32 {
        return "...".to_string();
    }

    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return value.to_string();
    }

    let heap = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match heap {
        NativeCpsI64HeapValue::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| describe_native_i64_debug_value_with_depth(*item, depth + 1))
                .collect::<Vec<_>>();
            match items.as_slice() {
                [] => "()".to_string(),
                [single] => format!("({single},)"),
                _ => format!("({})", items.join(", ")),
            }
        }
        NativeCpsI64HeapValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, value)| format!(
                    "{name}: {}",
                    describe_native_i64_debug_value_with_depth(*value, depth + 1)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        NativeCpsI64HeapValue::Variant { tag, value: None } => native_i64_tag_name(*tag),
        NativeCpsI64HeapValue::Variant {
            tag,
            value: Some(payload),
        } => format!(
            "{} {}",
            native_i64_tag_name(*tag),
            describe_native_i64_debug_value_with_depth(*payload, depth + 1)
        ),
        NativeCpsI64HeapValue::List(items) => format!(
            "[{}]",
            items
                .to_vec()
                .iter()
                .map(|item| describe_native_i64_debug_value_with_depth(*item, depth + 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        NativeCpsI64HeapValue::Bool(value) => value.to_string(),
        NativeCpsI64HeapValue::Unit => "()".to_string(),
        NativeCpsI64HeapValue::Float(value) => native_cps_format_float(*value),
        NativeCpsI64HeapValue::String(text) => format!("{:?}", text.to_flat_string()),
        NativeCpsI64HeapValue::Bytes(value) => format!("<bytes len={}>", value.len()),
        NativeCpsI64HeapValue::Path(value) => format!("{:?}", value.display().to_string()),
    }
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_resumption_i64_0(
    code: usize,
    handler: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, Vec::new())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_resumption_i64_1(
    code: usize,
    handler: i64,
    a: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_resumption_i64_2(
    code: usize,
    handler: i64,
    a: i64,
    b: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a, b])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_resumption_i64_3(
    code: usize,
    handler: i64,
    a: i64,
    b: i64,
    c: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a, b, c])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_resumption_i64_4(
    code: usize,
    handler: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a, b, c, d])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_resumption_i64_many(
    code: usize,
    handler: i64,
    ptr: *const i64,
    len: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, unsafe { native_i64_slice(ptr, len) })
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_env_i64_0() -> *const i64 {
    make_native_i64_env(Vec::new())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_env_i64_1(a: i64) -> *const i64 {
    make_native_i64_env(vec![a])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_env_i64_2(a: i64, b: i64) -> *const i64 {
    make_native_i64_env(vec![a, b])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_env_i64_3(a: i64, b: i64, c: i64) -> *const i64 {
    make_native_i64_env(vec![a, b, c])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_env_i64_4(a: i64, b: i64, c: i64, d: i64) -> *const i64 {
    make_native_i64_env(vec![a, b, c, d])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_env_i64_many(ptr: *const i64, len: i64) -> *const i64 {
    make_native_i64_env(unsafe { native_i64_slice(ptr, len) })
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_closure_i64_0(code: usize) -> usize {
    make_native_i64_closure(code, Vec::new())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_closure_i64_1(code: usize, a: i64) -> usize {
    make_native_i64_closure(code, vec![a])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_closure_i64_2(code: usize, a: i64, b: i64) -> usize {
    make_native_i64_closure(code, vec![a, b])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_closure_i64_3(
    code: usize,
    a: i64,
    b: i64,
    c: i64,
) -> usize {
    make_native_i64_closure(code, vec![a, b, c])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_closure_i64_4(
    code: usize,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> usize {
    make_native_i64_closure(code, vec![a, b, c, d])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_closure_i64_many(
    code: usize,
    ptr: *const i64,
    len: i64,
) -> usize {
    make_native_i64_closure(code, unsafe { native_i64_slice(ptr, len) })
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_recursive_closure_i64_0(
    code: usize,
    self_slot: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, Vec::new())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_recursive_closure_i64_1(
    code: usize,
    self_slot: i64,
    a: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, vec![a])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_recursive_closure_i64_2(
    code: usize,
    self_slot: i64,
    a: i64,
    b: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, vec![a, b])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_recursive_closure_i64_3(
    code: usize,
    self_slot: i64,
    a: i64,
    b: i64,
    c: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, vec![a, b, c])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_recursive_closure_i64_4(
    code: usize,
    self_slot: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, vec![a, b, c, d])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_recursive_closure_i64_many(
    code: usize,
    self_slot: i64,
    ptr: *const i64,
    len: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, unsafe {
        native_i64_slice(ptr, len)
    })
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_apply_closure_i64(value: usize, arg: i64) -> i64 {
    let is_resumption = NATIVE_CPS_I64_RESUMPTIONS.with(|s| s.borrow().contains(&value));
    if is_resumption {
        let result = yulang_cps_resume_i64(value as *const NativeCpsI64Resumption, arg);
        return yulang_cps_force_thunk_i64(result as usize);
    }
    // write27-e: Layer 2 calls a closure with the **caller**'s active
    // handlers and guards (eval_continuations(..., active_handlers,
    // guard_stack, ...) at cps_repr.rs:2247). The previous JIT impl
    // appended `closure.handlers` to the thread-local stack, which
    // caused exponential growth: every nested apply_closure stacked
    // another copy of the handler chain on top, and a captured
    // resumption then re-inherited those duplicates. Use the
    // caller's thread-local state as-is and ignore `closure.handlers`
    // / `closure.guard_stack` at call time.
    let closure = unsafe { &*(value as *const NativeCpsI64Closure) };
    if jit_trace_enabled() {
        let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().to_vec());
        let eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
        eprintln!(
            "[JIT-CPS] apply_closure: closure={:#x} arg={} eval={} initial={} frames={}",
            value,
            describe_native_i64_value(arg),
            eval.current_eval_id,
            eval.initial_frame_count,
            format_return_frames(&frames),
        );
    }
    let result = (closure.code)(closure.env.as_ptr(), arg);
    if jit_trace_enabled() {
        let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().to_vec());
        let eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
        eprintln!(
            "[JIT-CPS] apply_closure.out: closure={:#x} result={} eval={} initial={} frames={}",
            value,
            describe_native_i64_value(result),
            eval.current_eval_id,
            eval.initial_frame_count,
            format_return_frames(&frames),
        );
    }
    // make_closure points closure.code at the entry continuation directly,
    // bypassing the wrapper that would normally invoke
    // force_function_result_if_thunk. Without this force the callee may
    // hand back an unevaluated thunk (e.g. a handler-arm body that ended
    // in scope_return) that the caller then treats as a heap value handle
    // and dereferences as garbage. force_thunk is idempotent for
    // non-thunk values, so callers that already returned a concrete value
    // are unaffected.
    yulang_cps_force_thunk_i64(result as usize)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_is_applicable_i64(value: usize) -> i64 {
    let is_resumption = NATIVE_CPS_I64_RESUMPTIONS.with(|s| s.borrow().contains(&value));
    if is_resumption {
        return 1;
    }
    NATIVE_CPS_I64_CLOSURES
        .with(|closures| closures.borrow().contains(&value))
        .into()
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_control_capture_context_is_empty_i64() -> i64 {
    i64::from(native_i64_control_capture_context_flags() == 0)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_control_capture_context_flags_i64() -> i64 {
    native_i64_control_capture_context_flags()
}

fn native_i64_control_capture_context_flags() -> i64 {
    let mut flags = 0;
    if NATIVE_CPS_I64_HANDLER_STACK.with(|stack| !stack.borrow().is_empty()) {
        flags |= CONTROL_CAPTURE_HANDLER_STACK;
    }
    if NATIVE_CPS_I64_GUARD_STACK.with(|stack| !stack.borrow().is_empty()) {
        flags |= CONTROL_CAPTURE_GUARD_STACK;
    }
    if NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| !stack.borrow().is_empty()) {
        flags |= CONTROL_CAPTURE_ACTIVE_BLOCKED;
    }
    if NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| !envs.borrow().is_empty()) {
        flags |= CONTROL_CAPTURE_PENDING_HANDLER_ENVS;
    }
    if NATIVE_CPS_I64_PENDING_ESCAPE_ENV_TARGETS.with(|targets| !targets.borrow().is_empty()) {
        flags |= CONTROL_CAPTURE_PENDING_ESCAPE_TARGETS;
    }
    if NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| !siblings.borrow().is_empty()) {
        flags |= CONTROL_CAPTURE_RESUME_WITH_HANDLER_SIBLINGS;
    }
    if NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().is_active()) {
        flags |= CONTROL_CAPTURE_ABORT;
    }
    if NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active) {
        flags |= CONTROL_CAPTURE_SCOPE_RETURN;
    }
    flags
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_tuple_i64_0() -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(Vec::new().into_boxed_slice()))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_tuple_i64_1(a: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(vec![a].into_boxed_slice()))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_tuple_i64_2(a: i64, b: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(vec![a, b].into_boxed_slice()))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_tuple_i64_3(a: i64, b: i64, c: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(
        vec![a, b, c].into_boxed_slice(),
    ))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_tuple_i64_4(a: i64, b: i64, c: i64, d: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(
        vec![a, b, c, d].into_boxed_slice(),
    ))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_tuple_get_i64(value: i64, index: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Tuple(items) = value else {
        return 0;
    };
    items.get(index as usize).copied().unwrap_or(0)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_record_empty_i64() -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Record(Vec::new()))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_record_insert_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
    value: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return record;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return yulang_cps_record_empty_i64();
    };
    let mut fields = fields.clone();
    if let Some((_, slot)) = fields
        .iter_mut()
        .find(|(existing, _)| existing.as_ref() == field.as_str())
    {
        *slot = value;
    } else {
        fields.push((field.into_boxed_str(), value));
    }
    native_cps_i64_heap(NativeCpsI64HeapValue::Record(fields))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_record_select_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return 0;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return 0;
    };
    fields
        .iter()
        .find_map(|(name, value)| (name.as_ref() == field.as_str()).then_some(*value))
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_record_select_or_default_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
    default: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return default;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return default;
    };
    fields
        .iter()
        .find_map(|(name, value)| (name.as_ref() == field.as_str()).then_some(*value))
        .unwrap_or(default)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_record_has_field_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return 0;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return 0;
    };
    fields
        .iter()
        .any(|(name, _)| name.as_ref() == field.as_str()) as i64
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_record_without_field_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return record;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return yulang_cps_record_empty_i64();
    };
    let fields = fields
        .iter()
        .filter(|(name, _)| name.as_ref() != field.as_str())
        .cloned()
        .collect();
    native_cps_i64_heap(NativeCpsI64HeapValue::Record(fields))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_variant_i64_0(tag: i64) -> i64 {
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::Variant { tag, value: None });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] variant_new: tag={} payload=none result={}",
            native_i64_tag_name(tag),
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_variant_i64_1(tag: i64, value: i64) -> i64 {
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::Variant {
        tag,
        value: Some(value),
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] variant_new: tag={} payload={} result={}",
            native_i64_tag_name(tag),
            describe_native_i64_value(value),
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_variant_tag_eq_i64(value: i64, tag: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let result = match value {
        NativeCpsI64HeapValue::Variant { tag: actual, .. } => i64::from(*actual == tag),
        _ => 0,
    };
    if jit_trace_enabled() {
        let actual = match value {
            NativeCpsI64HeapValue::Variant { tag: actual, .. } => native_i64_tag_name(*actual),
            _ => "non_variant".to_string(),
        };
        eprintln!(
            "[JIT-CPS] variant_tag_eq: expected={} actual={} result={}",
            native_i64_tag_name(tag),
            actual,
            result
        );
    }
    result
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_variant_payload_i64(value: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let result = match value {
        NativeCpsI64HeapValue::Variant {
            value: Some(value), ..
        } => *value,
        _ => 0,
    };
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] variant_payload: payload={}",
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_register_tag_i64(tag: i64, ptr: *const u8, len: i64) -> i64 {
    if ptr.is_null() || len < 0 {
        return 0;
    }
    let Ok(len) = usize::try_from(len) else {
        return 0;
    };
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    let Ok(name) = std::str::from_utf8(bytes) else {
        return 0;
    };
    register_native_i64_tag_name(tag, name);
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_print_i64(value: i64) {
    print!("{}", describe_native_i64_value(value));
    let mut stdout = std::io::stdout();
    let _ = std::io::Write::flush(&mut stdout);
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_print_debug_i64(value: i64) {
    print!("{}", describe_native_i64_debug_value(value));
    let mut stdout = std::io::stdout();
    let _ = std::io::Write::flush(&mut stdout);
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_debug_i64(value: i64) -> i64 {
    native_cps_i64_string_heap(&describe_native_i64_debug_value(value))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_out_write_i64(value: i64) -> i64 {
    print!("{}", describe_native_i64_value(value));
    let mut stdout = std::io::stdout();
    let _ = std::io::Write::flush(&mut stdout);
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_err_write_i64(value: i64) -> i64 {
    eprint!("{}", describe_native_i64_value(value));
    let mut stderr = std::io::stderr();
    let _ = std::io::Write::flush(&mut stderr);
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_warn_write_i64(value: i64) -> i64 {
    eprintln!("warning: {}", describe_native_i64_value(value));
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_die_i64(value: i64) -> i64 {
    eprintln!("die: {}", describe_native_i64_value(value));
    std::process::exit(1);
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_empty_i64() -> i64 {
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::List(ListTree::empty()));
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] list_empty: result={}",
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_singleton_i64(value: i64) -> i64 {
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::List(ListTree::singleton(value)));
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] list_singleton: item={} result={}",
            describe_native_i64_value(value),
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_merge_i64(left: i64, right: i64) -> i64 {
    let left = unsafe { &*(left as *const NativeCpsI64HeapValue) };
    let right = unsafe { &*(right as *const NativeCpsI64HeapValue) };
    let (NativeCpsI64HeapValue::List(left), NativeCpsI64HeapValue::List(right)) = (left, right)
    else {
        return yulang_cps_list_empty_i64();
    };
    let merged = ListTree::concat(left.clone(), right.clone());
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::List(merged));
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] list_merge: left_len={} right_len={} result={}",
            left.len(),
            right.len(),
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_len_i64(value: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match value {
        NativeCpsI64HeapValue::List(items) => items.len() as i64,
        _ => 0,
    }
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_index_i64(value: i64, index: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::List(items) = value else {
        return 0;
    };
    let Ok(index) = usize::try_from(index) else {
        return 0;
    };
    items.index(index).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_index_range_raw_i64(
    value: i64,
    start: i64,
    end: i64,
) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::List(items) = value else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(start) = usize::try_from(start) else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(end) = usize::try_from(end) else {
        return yulang_cps_list_empty_i64();
    };
    if start > end || end > items.len() {
        return yulang_cps_list_empty_i64();
    }
    let Some(range) = items.index_range(start, end) else {
        return yulang_cps_list_empty_i64();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::List(range))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_index_range_i64(value: i64, range: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::List(items) = value else {
        return yulang_cps_list_empty_i64();
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, items.len()) else {
        return yulang_cps_list_empty_i64();
    };
    let Some(range) = items.index_range(start, end) else {
        return yulang_cps_list_empty_i64();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::List(range))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_splice_raw_i64(
    value: i64,
    start: i64,
    end: i64,
    insert: i64,
) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let insert = unsafe { &*(insert as *const NativeCpsI64HeapValue) };
    let (NativeCpsI64HeapValue::List(items), NativeCpsI64HeapValue::List(insert)) = (value, insert)
    else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(start) = usize::try_from(start) else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(end) = usize::try_from(end) else {
        return yulang_cps_list_empty_i64();
    };
    if start > end || end > items.len() {
        return yulang_cps_list_empty_i64();
    }
    let Some(result) = items.splice(start, end, insert.clone()) else {
        return yulang_cps_list_empty_i64();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::List(result))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_splice_i64(value: i64, range: i64, insert: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let insert = unsafe { &*(insert as *const NativeCpsI64HeapValue) };
    let (NativeCpsI64HeapValue::List(items), NativeCpsI64HeapValue::List(insert)) = (value, insert)
    else {
        return yulang_cps_list_empty_i64();
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, items.len()) else {
        return yulang_cps_list_empty_i64();
    };
    let Some(result) = items.splice(start, end, insert.clone()) else {
        return yulang_cps_list_empty_i64();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::List(result))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_list_view_raw_i64(value: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::List(items) = value else {
        return native_cps_i64_variant("empty", None);
    };
    match items.view() {
        ListView::Empty => {
            let result = native_cps_i64_variant("empty", None);
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] list_view: len=0 result={}",
                    describe_native_i64_value(result)
                );
            }
            result
        }
        ListView::Leaf(head) => {
            let result = native_cps_i64_variant("leaf", Some(head));
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] list_view: len=1 head={} result={}",
                    describe_native_i64_value(head),
                    describe_native_i64_value(result)
                );
            }
            result
        }
        ListView::Node {
            len, left, right, ..
        } => {
            let left = native_cps_i64_heap(NativeCpsI64HeapValue::List(left));
            let right = native_cps_i64_heap(NativeCpsI64HeapValue::List(right));
            let tuple = native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(
                vec![left, right].into_boxed_slice(),
            ));
            let result = native_cps_i64_variant("node", Some(tuple));
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] list_view: len={} left={} right={} result={}",
                    len,
                    describe_native_i64_value(left),
                    describe_native_i64_value(right),
                    describe_native_i64_value(result)
                );
            }
            result
        }
    }
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_int_to_string_i64(value: i64) -> i64 {
    native_cps_i64_string_heap(&value.to_string())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_int_to_hex_i64(value: i64) -> i64 {
    native_cps_i64_string_heap(&format!("{value:x}"))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_int_to_upper_hex_i64(value: i64) -> i64 {
    native_cps_i64_string_heap(&format!("{value:X}"))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_bool_to_string_i64(value: i64) -> i64 {
    let text = if value == 0 { "false" } else { "true" };
    native_cps_i64_string_heap(text)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_box_bool_i64(value: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Bool(value != 0))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_unit_i64() -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Unit)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_float_to_string_f64(value: f64) -> i64 {
    native_cps_i64_string_heap(&native_cps_format_float(value))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_box_float_f64(value: f64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Float(value))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_unbox_float_i64(value: i64) -> f64 {
    let Some(NativeCpsI64HeapValue::Float(value)) = native_cps_i64_heap_value(value) else {
        return value as f64;
    };
    *value
}

fn native_cps_format_float(value: f64) -> String {
    let mut rendered = value.to_string();
    if !rendered.contains('.') && !rendered.contains('e') && !rendered.contains('E') {
        rendered.push_str(".0");
    }
    rendered
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_literal_i64(ptr: *const u8, len: i64) -> i64 {
    let Some(text) = native_cps_i64_string_from_bytes(ptr, len) else {
        return native_cps_i64_string_empty();
    };
    native_cps_i64_string_heap(&text)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_concat_i64(left: i64, right: i64) -> i64 {
    let Some(left) = native_cps_i64_string_value(left) else {
        return native_cps_i64_string_empty();
    };
    let Some(right) = native_cps_i64_string_value(right) else {
        return native_cps_i64_string_empty();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(StringTree::concat(
        left.clone(),
        right.clone(),
    )))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_eq_i64(left: i64, right: i64) -> i64 {
    let Some(left) = native_cps_i64_string_value(left) else {
        return 0;
    };
    let Some(right) = native_cps_i64_string_value(right) else {
        return 0;
    };
    i64::from(left.to_flat_string() == right.to_flat_string())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_len_i64(value: i64) -> i64 {
    native_cps_i64_string_value(value)
        .map(|text| text.len() as i64)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_index_i64(value: i64, index: i64) -> i64 {
    let Some(text) = native_cps_i64_string_value(value) else {
        return native_cps_i64_string_empty();
    };
    let Ok(index) = usize::try_from(index) else {
        return native_cps_i64_string_empty();
    };
    let Some(ch) = text.index(index) else {
        return native_cps_i64_string_empty();
    };
    native_cps_i64_string_heap(&ch.to_string())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_index_range_raw_i64(
    value: i64,
    start: i64,
    end: i64,
) -> i64 {
    let Some(text) = native_cps_i64_string_value(value) else {
        return native_cps_i64_string_empty();
    };
    let Some((start, end)) = native_cps_i64_string_index_range(text, start, end) else {
        return native_cps_i64_string_empty();
    };
    let Some(slice) = text.index_range(start, end) else {
        return native_cps_i64_string_empty();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(slice))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_index_range_i64(value: i64, range: i64) -> i64 {
    let Some(text) = native_cps_i64_string_value(value) else {
        return native_cps_i64_string_empty();
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, text.len()) else {
        return native_cps_i64_string_empty();
    };
    let Some(slice) = text.index_range(start, end) else {
        return native_cps_i64_string_empty();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(slice))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_splice_raw_i64(
    value: i64,
    start: i64,
    end: i64,
    insert: i64,
) -> i64 {
    let Some(text) = native_cps_i64_string_value(value) else {
        return native_cps_i64_string_empty();
    };
    let Some(insert) = native_cps_i64_string_value(insert) else {
        return native_cps_i64_string_empty();
    };
    let Some((start, end)) = native_cps_i64_string_index_range(text, start, end) else {
        return native_cps_i64_string_empty();
    };
    let Some(result) = text.splice(start, end, insert.clone()) else {
        return native_cps_i64_string_empty();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(result))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_splice_i64(value: i64, range: i64, insert: i64) -> i64 {
    let Some(text) = native_cps_i64_string_value(value) else {
        return native_cps_i64_string_empty();
    };
    let Some(insert) = native_cps_i64_string_value(insert) else {
        return native_cps_i64_string_empty();
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, text.len()) else {
        return native_cps_i64_string_empty();
    };
    let Some(result) = text.splice(start, end, insert.clone()) else {
        return native_cps_i64_string_empty();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(result))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_string_to_bytes_i64(value: i64) -> i64 {
    let Some(text) = native_cps_i64_string_value(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::from_bytes(
        text.to_flat_string().as_bytes(),
    )))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_bytes_len_i64(value: i64) -> i64 {
    native_cps_i64_bytes_value(value)
        .map(|value| value.len() as i64)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_bytes_eq_i64(left: i64, right: i64) -> i64 {
    let Some(left) = native_cps_i64_bytes_value(left) else {
        return 0;
    };
    let Some(right) = native_cps_i64_bytes_value(right) else {
        return 0;
    };
    i64::from(left.to_flat_vec() == right.to_flat_vec())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_bytes_concat_i64(left: i64, right: i64) -> i64 {
    let Some(left) = native_cps_i64_bytes_value(left) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    let Some(right) = native_cps_i64_bytes_value(right) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::concat(
        left.clone(),
        right.clone(),
    )))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_bytes_index_i64(value: i64, index: i64) -> i64 {
    let Some(value) = native_cps_i64_bytes_value(value) else {
        return 0;
    };
    let Ok(index) = usize::try_from(index) else {
        return 0;
    };
    value.index(index).map(i64::from).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_bytes_index_range_i64(value: i64, range: i64) -> i64 {
    let Some(value) = native_cps_i64_bytes_value(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, value.len()) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(
        value
            .index_range(start, end)
            .unwrap_or_else(BytesTree::empty),
    ))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_bytes_to_utf8_raw_i64(value: i64) -> i64 {
    let Some(value) = native_cps_i64_bytes_value(value) else {
        return native_cps_i64_utf8_raw_result("", 0);
    };
    let bytes = value.to_flat_vec();
    match std::str::from_utf8(&bytes) {
        Ok(text) => native_cps_i64_utf8_raw_result(text, bytes.len()),
        Err(error) => {
            let valid = error.valid_up_to();
            let text = std::str::from_utf8(&bytes[..valid]).unwrap_or("");
            native_cps_i64_utf8_raw_result(text, valid)
        }
    }
}

fn native_cps_i64_utf8_raw_result(text: &str, valid: usize) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(Box::new([
        native_cps_i64_string_heap(text),
        valid as i64,
    ])))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_bytes_to_path_i64(value: i64) -> i64 {
    let Some(value) = native_cps_i64_bytes_value(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Path(path_buf_from_bytes(&[])));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Path(path_buf_from_bytes(
        &value.to_flat_vec(),
    )))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_path_to_bytes_i64(value: i64) -> i64 {
    let Some(value) = native_cps_i64_path_value(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::from_bytes(
        &path_buf_bytes(value),
    )))
}

fn native_cps_i64_string_from_bytes(ptr: *const u8, len: i64) -> Option<String> {
    if ptr.is_null() || len < 0 {
        return None;
    }
    let len = usize::try_from(len).ok()?;
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    std::str::from_utf8(bytes).ok().map(str::to_string)
}

fn native_cps_i64_string_heap(text: &str) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::String(StringTree::from_str(text)))
}

fn native_cps_i64_string_empty() -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::String(StringTree::empty()))
}

fn native_cps_i64_string_value(value: i64) -> Option<&'static StringTree<Box<str>>> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return None;
    }
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match value {
        NativeCpsI64HeapValue::String(text) => Some(text),
        _ => None,
    }
}

fn native_cps_i64_bytes_value(value: i64) -> Option<&'static BytesTree> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return None;
    }
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match value {
        NativeCpsI64HeapValue::Bytes(value) => Some(value),
        _ => None,
    }
}

fn native_cps_i64_path_value(value: i64) -> Option<&'static std::path::PathBuf> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return None;
    }
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match value {
        NativeCpsI64HeapValue::Path(value) => Some(value),
        _ => None,
    }
}

#[cfg(unix)]
fn path_buf_from_bytes(bytes: &[u8]) -> std::path::PathBuf {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    std::path::PathBuf::from(OsString::from_vec(bytes.to_vec()))
}

#[cfg(not(unix))]
fn path_buf_from_bytes(bytes: &[u8]) -> std::path::PathBuf {
    std::path::PathBuf::from(String::from_utf8_lossy(bytes).into_owned())
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

fn native_cps_i64_string_index_range(
    text: &StringTree<Box<str>>,
    start: i64,
    end: i64,
) -> Option<(usize, usize)> {
    let start = usize::try_from(start).ok()?;
    let end = usize::try_from(end).ok()?;
    if start > end || end > text.len() {
        return None;
    }
    Some((start, end))
}

fn native_cps_i64_normalized_int_range(value: i64, len: usize) -> Option<(usize, usize)> {
    let value = native_cps_i64_heap_value(value)?;
    let NativeCpsI64HeapValue::Variant {
        tag,
        value: Some(payload),
    } = value
    else {
        return None;
    };
    if *tag != tag_hash(&typed_ir::Name("within".to_string())) {
        return None;
    }
    let NativeCpsI64HeapValue::Tuple(items) = native_cps_i64_heap_value(*payload)? else {
        return None;
    };
    let [start, end] = items.as_ref() else {
        return None;
    };
    let start = native_cps_i64_normalized_start_bound(*start)?;
    let end = native_cps_i64_normalized_end_bound(*end, len)?;
    (start <= end && end <= len).then_some((start, end))
}

fn native_cps_i64_normalized_start_bound(value: i64) -> Option<usize> {
    let NativeCpsI64HeapValue::Variant { tag, value } = native_cps_i64_heap_value(value)? else {
        return None;
    };
    let tag = native_i64_tag_name(*tag);
    match tag.as_str() {
        "unbounded" => Some(0),
        "included" => usize::try_from(value.as_ref().copied()?).ok(),
        "excluded" => usize::try_from(value.as_ref().copied()? + 1).ok(),
        _ => None,
    }
}

fn native_cps_i64_normalized_end_bound(value: i64, len: usize) -> Option<usize> {
    let NativeCpsI64HeapValue::Variant { tag, value } = native_cps_i64_heap_value(value)? else {
        return None;
    };
    let tag = native_i64_tag_name(*tag);
    match tag.as_str() {
        "unbounded" => Some(len),
        "included" => usize::try_from(value.as_ref().copied()? + 1).ok(),
        "excluded" => usize::try_from(value.as_ref().copied()?).ok(),
        _ => None,
    }
}

fn native_cps_i64_heap_value(value: i64) -> Option<&'static NativeCpsI64HeapValue> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    is_heap.then(|| unsafe { &*(value as *const NativeCpsI64HeapValue) })
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_resume_i64(
    resumption: *const NativeCpsI64Resumption,
    arg: i64,
) -> i64 {
    let resumption = unsafe { &*resumption };
    // write27-e: mirror Layer 2's `CpsStmt::Resume` (cps_repr.rs:1879).
    //   resumed_handlers  = merge_resumption_handlers(captured, current, anchor)
    //   adjusted_frames   = merge_extras_into_frames(captured_frames, current, anchor)
    //   eval_continuations(..., resumed_handlers, ..., adjusted_frames, initial=0)
    // The JIT version save/restores thread-local return_frames + eval
    // context around the call so the caller's outer frames stay
    // hidden during the resumed eval (matches Layer 2 where eval_continuations
    // gets its own local state).
    let current_handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().to_vec());
    let anchor = resumption.handled_anchor;
    let resumed_handlers =
        merge_resumption_handlers_native(&resumption.handlers, &current_handlers, anchor);
    let adjusted_frames =
        merge_extras_into_frames_native(&resumption.return_frames, &current_handlers, anchor);
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] resume: anchor={:?} captured={} current={} resumed={} adjusted_frames={}",
            anchor,
            format_handler_stack(&resumption.handlers),
            format_handler_stack(&current_handlers),
            format_handler_stack(&resumed_handlers),
            adjusted_frames.len(),
        );
    }
    // Swap state.
    let saved_frames =
        NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow_mut().replace(adjusted_frames));
    let fresh_eval = NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    });
    let saved_eval_ctx = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        std::mem::replace(
            &mut *ctx.borrow_mut(),
            NativeCpsI64EvalContext {
                current_eval_id: fresh_eval,
                initial_frame_count: 0,
            },
        )
    });
    let mut result = with_native_i64_cps_state_guard_snapshot(
        resumed_handlers,
        resumption.guard_stack.clone(),
        || (resumption.code)(resumption.env.as_ptr(), arg),
    );
    if yulang_cps_scope_return_active_i64() != 0 {
        result = yulang_cps_route_scope_return_i64(result);
    }
    // Restore state only for ordinary value flow. If a ScopeReturn / abort is
    // still propagating, the resumed eval may have updated captured return
    // frame snapshots (notably ResumeWithHandler hygiene); restoring the old
    // caller snapshot here would resurrect stale handlers.
    restore_native_i64_return_frames_after_resume(saved_frames, &resumption.return_frames);
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = saved_eval_ctx);
    result
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_resume_with_handler_i64(
    resumption: *const NativeCpsI64Resumption,
    arg: i64,
    handler: i64,
    consumes_mask: i64,
    owner_function: i64,
    updates_existing_handler_env: i64,
) -> i64 {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::ResumeWithHandler);
    let resumption = unsafe { &*resumption };
    let prompt = yulang_cps_fresh_prompt_i64() as u64;
    let install_eval_id = yulang_cps_current_eval_id_i64() as u64;
    let return_frame_threshold = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    let updates_existing_handler_env = updates_existing_handler_env != 0;
    let rebases_existing_handler = updates_existing_handler_env
        && resumption
            .handlers
            .iter()
            .any(|frame| frame.handler == handler);
    let guard_stack = if updates_existing_handler_env || rebases_existing_handler {
        native_cps_i64_snapshot(Vec::new())
    } else {
        current_native_i64_guard_snapshot()
    };
    let outer_handler = NativeCpsI64HandlerFrame {
        handler,
        consumes_mask,
        guard_stack,
        envs: native_cps_i64_snapshot(take_pending_native_i64_handler_envs(handler)),
        prompt,
        install_eval_id,
        escape_owner_function_id: owner_function.max(0) as u64,
        threshold_owner_function_id: owner_function.max(0) as u64,
        inherited: false,
        escape_continuation: 0,
        escape_env: native_cps_i64_empty_snapshot(),
        escape_env_targets: native_cps_i64_empty_snapshot(),
        return_frame_threshold,
        return_frame_prefix: native_cps_i64_snapshot(Vec::new()),
        origin: NativeCpsI64HandlerFrameOrigin::ResumeWithHandler,
    };
    let mut inherited_handler = outer_handler.clone();
    inherited_handler.inherited = true;
    push_resume_with_handler_sibling(outer_handler.clone());
    let mut handlers = resumption.handlers.to_vec();
    if !rebases_existing_handler {
        handlers.push(inherited_handler.clone());
    }
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] resume_with_handler: rid={} handler={} rebased={} envs={} captured_frames={} handlers={}",
            resumption.debug_id,
            handler,
            rebases_existing_handler,
            format_handler_envs(&outer_handler.envs),
            format_return_frames(&resumption.return_frames),
            format_handler_stack(&handlers),
        );
    }
    let mut resumed_frames = resumption.return_frames.to_vec();
    if rebases_existing_handler {
        own_native_i64_captured_return_frames(&mut resumed_frames);
    } else {
        for frame in &mut resumed_frames {
            if !frame
                .handlers
                .iter()
                .any(|existing| same_handler_frame_native(existing, &inherited_handler))
            {
                let mut handlers = frame.handlers.to_vec();
                handlers.push(inherited_handler.clone());
                frame.handlers = native_cps_i64_snapshot(handlers);
            }
        }
    }
    let mut saved_frames =
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().replace(resumed_frames));
    let mut previous_handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let previous = stack.borrow().to_vec();
        stack.borrow_mut().replace(handlers);
        previous
    });
    let previous_guards = NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
        stack
            .borrow_mut()
            .replace_snapshot(resumption.guard_stack.clone())
    });
    let fresh_eval = NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    });
    let saved_eval_ctx = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        std::mem::replace(
            &mut *ctx.borrow_mut(),
            NativeCpsI64EvalContext {
                current_eval_id: fresh_eval,
                initial_frame_count: 0,
            },
        )
    });
    let result = (resumption.code)(resumption.env.as_ptr(), arg);
    let scope_return_active = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active);
    let abort_active = NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().is_active());
    if !rebases_existing_handler {
        append_resume_handler_to_frames(&mut saved_frames, &outer_handler);
        append_resume_handler_to_handler_prefixes(&mut previous_handlers, &outer_handler);
    }
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let mut outer = previous_handlers;
        if !rebases_existing_handler {
            outer.push(outer_handler);
        }
        stack.borrow_mut().replace(outer);
    });
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
        stack.borrow_mut().restore_snapshot(previous_guards);
    });
    if abort_active && !scope_return_active {
        restore_native_i64_return_frames_after_resume(saved_frames, &resumption.return_frames);
    } else {
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            frames.borrow_mut().replace(saved_frames);
        });
    }
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = saved_eval_ctx);
    result
}

// =====================================================================
// write27-d d4: EffectfulApply Resumption helper (c6 of write27).
// =====================================================================

/// `same_handler_frame` port: equality on (prompt, install_eval_id).
/// Synthetic frames (install_eval == MAX) compare equal only to other
/// synthetic frames with the same prompt; in practice that's almost
/// always false, so synthetic frames are treated as distinct.
fn same_handler_frame_native(a: &NativeCpsI64HandlerFrame, b: &NativeCpsI64HandlerFrame) -> bool {
    a.prompt == b.prompt && a.install_eval_id == b.install_eval_id
}

/// `merge_resumption_handlers` port. Place resume-site siblings
/// between the captured prefix-through-anchor and the captured tail.
fn merge_resumption_handlers_native(
    captured: &[NativeCpsI64HandlerFrame],
    current: &[NativeCpsI64HandlerFrame],
    anchor: Option<NativeCpsI64HandlerAnchor>,
) -> Vec<NativeCpsI64HandlerFrame> {
    if let Some(anchor) = anchor {
        if let Some(anchor_index) = captured
            .iter()
            .position(|f| f.prompt == anchor.prompt && f.install_eval_id == anchor.install_eval_id)
        {
            let mut merged = Vec::with_capacity(captured.len() + current.len());
            merged.extend(captured[..=anchor_index].iter().cloned());
            for frame in current {
                let in_prefix = merged.iter().any(|m| same_handler_frame_native(m, frame));
                let in_tail = captured[anchor_index + 1..]
                    .iter()
                    .any(|c| same_handler_frame_native(c, frame));
                if !in_prefix && !in_tail {
                    merged.push(frame.clone());
                }
            }
            merged.extend(captured[anchor_index + 1..].iter().cloned());
            return merged;
        }
    }
    // Shared-prefix fallback.
    let mut shared = 0;
    while shared < captured.len()
        && shared < current.len()
        && same_handler_frame_native(&captured[shared], &current[shared])
    {
        shared += 1;
    }
    let mut merged = Vec::with_capacity(captured.len() + current.len());
    merged.extend(captured[..shared].iter().cloned());
    for frame in &current[shared..] {
        if !captured.iter().any(|c| same_handler_frame_native(c, frame)) {
            merged.push(frame.clone());
        }
    }
    merged.extend(captured[shared..].iter().cloned());
    merged
}

/// `merge_extras_into_frames` port. For each captured return frame,
/// re-merge its `handlers` snapshot with the current resume-site
/// handlers via anchor logic.
fn merge_extras_into_frames_native(
    frames: &[NativeCpsI64ReturnFrame],
    current: &[NativeCpsI64HandlerFrame],
    anchor: Option<NativeCpsI64HandlerAnchor>,
) -> Vec<NativeCpsI64ReturnFrame> {
    frames
        .iter()
        .map(|frame| {
            let merged = merge_resumption_handlers_native(&frame.handlers, current, anchor);
            NativeCpsI64ReturnFrame {
                prompt_exit: frame.prompt_exit.clone(),
                debug_id: frame.debug_id,
                continuation: frame.continuation,
                continuation_id: frame.continuation_id,
                env: frame.env.clone(),
                handlers: native_cps_i64_snapshot(merged),
                guards: frame.guards.clone(),
                owner_initial_frame_count: frame.owner_initial_frame_count,
                owner_eval_id: frame.owner_eval_id,
                owner_function_id: frame.owner_function_id,
                immediately_forces_param: frame.immediately_forces_param,
            }
        })
        .collect()
}

fn capture_native_i64_return_frames_from_start(
    frames: &[NativeCpsI64ReturnFrame],
    start: usize,
    handled_install_eval_id: u64,
) -> NativeCpsI64ReturnFrameSnapshot {
    let mut captured = frames[start..]
        .iter()
        .cloned()
        .map(|frame| rebase_native_i64_captured_return_frame(frame, start, handled_install_eval_id))
        .collect::<Vec<_>>();
    own_native_i64_captured_return_frames(&mut captured);
    native_cps_i64_snapshot(captured)
}

fn native_i64_prompt_frame_start(
    frames: &[NativeCpsI64ReturnFrame],
    prompt: u64,
    _fallback_threshold: usize,
) -> usize {
    frames
        .iter()
        .rposition(|frame| {
            frame
                .prompt_exit
                .as_ref()
                .is_some_and(|exit| exit.prompt == prompt)
        })
        .map(|index| index + 1)
        // If the marker is absent, this captured slice is already running
        // under an inherited prompt. Keep the whole slice; the handler
        // threshold may point at a replay-time post frame that still belongs
        // to this continuation.
        .unwrap_or(0)
        .min(frames.len())
}

fn rebase_native_i64_captured_return_frame(
    mut frame: NativeCpsI64ReturnFrame,
    dropped_frames: usize,
    handled_install_eval_id: u64,
) -> NativeCpsI64ReturnFrame {
    frame.owner_initial_frame_count = frame
        .owner_initial_frame_count
        .saturating_sub(dropped_frames);
    for handler in frame.handlers.make_mut() {
        if handler.install_eval_id >= handled_install_eval_id {
            handler.return_frame_threshold = handler
                .return_frame_threshold
                .saturating_sub(dropped_frames);
        }
    }
    frame
}

fn rebase_native_i64_captured_handlers(
    handlers: &mut [NativeCpsI64HandlerFrame],
    dropped_frames: usize,
    handled_install_eval_id: u64,
) {
    for handler in handlers {
        if handler.install_eval_id >= handled_install_eval_id {
            handler.return_frame_threshold = handler
                .return_frame_threshold
                .saturating_sub(dropped_frames);
        }
    }
}

/// For handlers whose install_eval is below the anchor (inherited from an
/// outer eval), the captured threshold value is stale once the slice is
/// reused inside a nested resumption: the slice now contains a different
/// set of pre-install frames. Re-derive each inherited threshold from the
/// actual position of its prompt-exit marker inside the slice; if the
/// marker is not present, the handler was installed strictly before the
/// slice began, so the slice has no pre-install frames (threshold = 0).
fn recalibrate_inherited_handler_thresholds(
    handlers: &mut [NativeCpsI64HandlerFrame],
    slice: &[NativeCpsI64ReturnFrame],
    handled_install_eval_id: u64,
) {
    for handler in handlers {
        if handler.install_eval_id >= handled_install_eval_id {
            continue;
        }
        let prompt = handler.prompt;
        let marker = slice.iter().position(|frame| {
            frame
                .prompt_exit
                .as_ref()
                .is_some_and(|exit| exit.prompt == prompt)
        });
        handler.return_frame_threshold = marker.unwrap_or(0);
    }
}

fn own_native_i64_captured_return_frames(frames: &mut [NativeCpsI64ReturnFrame]) {
    for frame in frames {
        frame.owner_initial_frame_count = 0;
    }
}

fn append_resume_handler_to_frames(
    frames: &mut [NativeCpsI64ReturnFrame],
    handler: &NativeCpsI64HandlerFrame,
) {
    for frame in frames {
        if !frame
            .handlers
            .iter()
            .any(|existing| same_handler_frame_native(existing, handler))
        {
            let mut handlers = frame.handlers.to_vec();
            handlers.push(handler.clone());
            frame.handlers = native_cps_i64_snapshot(handlers);
        }
    }
}

fn append_resume_handler_to_handler_prefixes(
    handlers: &mut [NativeCpsI64HandlerFrame],
    handler: &NativeCpsI64HandlerFrame,
) {
    for active in handlers {
        if active.return_frame_prefix.is_empty() {
            continue;
        }
        let mut prefix = active.return_frame_prefix.to_vec();
        append_resume_handler_to_frames(&mut prefix, handler);
        active.return_frame_prefix = native_cps_i64_snapshot(prefix);
    }
}

fn push_resume_with_handler_sibling(handler: NativeCpsI64HandlerFrame) {
    NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| {
        let mut siblings = siblings.borrow_mut();
        if !siblings
            .iter()
            .any(|existing| same_handler_frame_native(existing, &handler))
        {
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] push_rwh_sibling: handler={} envs={}",
                    handler.handler,
                    format_handler_envs(&handler.envs)
                );
            }
            siblings.push(handler);
        }
    });
}

fn append_resume_with_handler_siblings(handlers: &mut Vec<NativeCpsI64HandlerFrame>) {
    NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| {
        for sibling in siblings.borrow().iter() {
            if !handlers
                .iter()
                .any(|existing| same_handler_frame_native(existing, sibling))
            {
                handlers.push(sibling.clone());
            }
        }
    });
}

fn restore_native_i64_return_frames_after_resume(
    saved_frames: Vec<NativeCpsI64ReturnFrame>,
    _resumed_frames: &[NativeCpsI64ReturnFrame],
) {
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        let mut slot = frames.borrow_mut();
        let current = slot.take();
        let mut restored = Vec::new();
        let mut used_current = vec![false; current.len()];
        for saved in saved_frames {
            if let Some((index, current_frame)) = current
                .iter()
                .enumerate()
                .find(|(_, frame)| frame.debug_id == saved.debug_id)
            {
                restored.push(current_frame.clone());
                used_current[index] = true;
            } else {
                restored.push(saved);
            }
        }
        for (index, current_frame) in current.into_iter().enumerate() {
            if !used_current[index] {
                restored.push(current_frame);
            }
        }
        slot.replace(restored);
    });
}

/// write27-d d4: shared core of `effectful_apply_resumption_i64_N`.
/// Mirrors Layer 2's `EffectfulApply { Resumption } ` arm:
///   1. push F_post(post_cont, env_slots, owner_initial, owner_eval)
///      onto current return frames.
///   2. anchor-merge resumption.handlers with the current handler stack.
///   3. anchor-merge each of resumption.return_frames' handler snapshots.
///   4. combined_frames = new_frames + adjusted_resumption_frames.
///   5. swap thread-local state and call `resumption.code(env, arg)`.
/// write27-e e1: compact formatter for a handler stack — emits
/// `[h<id>(p=..., ev=..., origin=..., inh=...) ...]` so trace lines
/// don't blow up but each frame's identity is still visible.
fn format_handler_stack(stack: &[NativeCpsI64HandlerFrame]) -> String {
    let mut s = String::from("[");
    for (i, frame) in stack.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(&format!(
            "h{}(p={},ev={},owner_fn={},thr_owner={},{:?},inh={},thr={},guards={:?})",
            frame.handler,
            frame.prompt,
            if frame.install_eval_id == NATIVE_CPS_I64_SYNTHETIC_EVAL_ID {
                "SYN".to_string()
            } else {
                frame.install_eval_id.to_string()
            },
            frame.escape_owner_function_id,
            frame.threshold_owner_function_id,
            frame.origin,
            frame.inherited,
            frame.return_frame_threshold,
            frame.guard_stack,
        ));
    }
    s.push(']');
    s
}

/// write27-e e1: compact formatter for a return-frame stack — useful
/// to verify anchor merge actually modified each frame's
/// `active_handlers`.
fn format_return_frames(frames: &[NativeCpsI64ReturnFrame]) -> String {
    const EDGE_FRAMES: usize = 4;
    let mut s = String::from("[");
    let mut wrote = 0usize;
    for (i, frame) in frames.iter().enumerate() {
        if frames.len() > EDGE_FRAMES * 2 && i == EDGE_FRAMES {
            if wrote > 0 {
                s.push_str(", ");
            }
            s.push_str(&format!("... {} more ...", frames.len() - EDGE_FRAMES * 2));
            wrote += 1;
            continue;
        }
        if frames.len() > EDGE_FRAMES * 2 && i >= EDGE_FRAMES && i < frames.len() - EDGE_FRAMES {
            continue;
        }
        if i > 0 {
            s.push_str(", ");
        }
        let prompt_exit = frame
            .prompt_exit
            .as_ref()
            .map(|exit| format!(",prompt_exit={}", exit.prompt))
            .unwrap_or_default();
        s.push_str(&format!(
            "F#{}/id{}:k{}(owner_eval={},owner_fn={},init={}{} ,handlers={})",
            i,
            frame.debug_id,
            frame.continuation_id,
            frame.owner_eval_id,
            frame.owner_function_id,
            frame.owner_initial_frame_count,
            prompt_exit,
            format_handler_stack(&frame.handlers),
        ));
        wrote += 1;
    }
    s.push(']');
    s
}

fn format_handler_envs(envs: &[NativeCpsI64HandlerEnv]) -> String {
    let parts = envs
        .iter()
        .map(|env| {
            let slots = if env.slots.is_empty() {
                String::new()
            } else {
                let slots = env
                    .slots
                    .iter()
                    .map(|(target, value)| {
                        format!("{}:{}", target, describe_native_i64_value(*value))
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                format!(" {{{}}}", slots)
            };
            format!(
                "{}={}{}",
                env.entry,
                describe_native_i64_value(env.env),
                slots
            )
        })
        .collect::<Vec<_>>();
    format!("[{}]", parts.join(", "))
}

fn refreshed_escape_env(frame: &NativeCpsI64HandlerFrame) -> NativeCpsI64I64Snapshot {
    if frame.escape_env_targets.is_empty() {
        return frame.escape_env.clone();
    }
    let mut env = frame.escape_env.to_vec();
    for (index, target) in frame.escape_env_targets.iter().copied().enumerate() {
        let Some(slot) = env.get_mut(index) else {
            continue;
        };
        if let Some(value) = latest_handler_slot_value(frame.handler, target) {
            *slot = value;
        }
    }
    native_cps_i64_snapshot(env)
}

fn latest_handler_slot_value(handler: i64, target: i64) -> Option<i64> {
    NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| {
        siblings
            .borrow()
            .iter()
            .rev()
            .filter(|frame| frame.handler == handler)
            .flat_map(|frame| frame.envs.iter().rev())
            .flat_map(|env| env.slots.iter().rev())
            .find_map(|(slot_target, value)| (*slot_target == target).then_some(*value))
    })
}

fn append_distinct_return_frames(
    out: &mut Vec<NativeCpsI64ReturnFrame>,
    frames: impl IntoIterator<Item = NativeCpsI64ReturnFrame>,
) {
    for frame in frames {
        if out
            .iter()
            .any(|existing| existing.debug_id == frame.debug_id)
        {
            if jit_trace_enabled() {
                eprintln!("[JIT-CPS] return_frame_dedup: skip id={}", frame.debug_id);
            }
            continue;
        }
        out.push(frame);
    }
}

fn is_captured_handler_key(
    handler: &NativeCpsI64HandlerFrame,
    captured: &[NativeCpsI64HandlerFrame],
) -> bool {
    captured.iter().any(|candidate| {
        candidate.prompt == handler.prompt && candidate.install_eval_id == handler.install_eval_id
    })
}

fn rebase_captured_return_frame_threshold(
    old_threshold: usize,
    captured_frames: &[NativeCpsI64ReturnFrame],
    combined_prefix: &[NativeCpsI64ReturnFrame],
) -> usize {
    let mut rebased = combined_prefix.len();
    let captured_prefix_len = old_threshold.min(captured_frames.len());
    for captured in &captured_frames[..captured_prefix_len] {
        if !combined_prefix
            .iter()
            .any(|existing| existing.debug_id == captured.debug_id)
        {
            rebased += 1;
        }
    }
    rebased
}

fn rebase_captured_handler_thresholds(
    frames: &mut [NativeCpsI64ReturnFrame],
    captured_handlers: &[NativeCpsI64HandlerFrame],
    captured_frames: &[NativeCpsI64ReturnFrame],
    combined_prefix: &[NativeCpsI64ReturnFrame],
) {
    for frame in frames {
        let updates = frame
            .handlers
            .iter()
            .enumerate()
            .filter_map(|(index, handler)| {
                if !is_captured_handler_key(handler, captured_handlers) {
                    return None;
                }
                let threshold = rebase_captured_return_frame_threshold(
                    handler.return_frame_threshold,
                    captured_frames,
                    combined_prefix,
                );
                (threshold != handler.return_frame_threshold).then_some((index, threshold))
            })
            .collect::<Vec<_>>();
        if updates.is_empty() {
            continue;
        }
        let handlers = frame.handlers.make_mut();
        for (index, threshold) in updates {
            if let Some(handler) = handlers.get_mut(index) {
                handler.return_frame_threshold = threshold;
            }
        }
    }
}

fn effectful_apply_resumption_native(
    resumption: *const NativeCpsI64Resumption,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: bool,
    env: Vec<i64>,
) -> i64 {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::EffectfulApplyResumption);
    let resumption = unsafe { &*resumption };
    let current_handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().to_vec());
    let current_guards = current_native_i64_guard_snapshot();
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] effectful_apply_resumption.in: rid={} anchor={:?} captured={} captured_frames={} current={}",
            resumption.debug_id,
            resumption.handled_anchor,
            format_handler_stack(&resumption.handlers),
            format_return_frames(&resumption.return_frames),
            format_handler_stack(&current_handlers),
        );
    }
    // 1. Build F_post.
    let f_post = NativeCpsI64ReturnFrame {
        prompt_exit: None,
        debug_id: next_native_i64_return_frame_debug_id(),
        continuation: post_cont as usize,
        continuation_id: 0,
        env: native_cps_i64_snapshot(env),
        handlers: native_cps_i64_snapshot(current_handlers.clone()),
        guards: current_guards,
        owner_initial_frame_count: owner_initial.max(0) as usize,
        owner_eval_id: owner_eval as u64,
        owner_function_id: owner_function.max(0) as u64,
        immediately_forces_param: immediately_forces,
    };
    let mut new_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().to_vec());
    new_frames.push(f_post);
    // 2 + 3. Anchor merges.
    let anchor = resumption.handled_anchor;
    let resumed_handlers =
        merge_resumption_handlers_native(&resumption.handlers, &current_handlers, anchor);
    let mut adjusted_res =
        merge_extras_into_frames_native(&resumption.return_frames, &current_handlers, anchor);
    rebase_captured_handler_thresholds(
        &mut adjusted_res,
        &resumption.handlers,
        &resumption.return_frames,
        &new_frames,
    );
    // 4. combined frames. A captured resumption can be resumed while one
    // of its captured return-frame instances is already present at the
    // resume site. Re-adding that exact instance replays stale
    // continuations after reject/backtracking; only suppress identical
    // frame instances, not merely same-shaped fresh frames.
    append_distinct_return_frames(&mut new_frames, adjusted_res);
    let combined_len = new_frames.len();
    let resumed_len = resumed_handlers.len();
    // 5. swap state + call.
    let trace_state = jit_trace_enabled().then(|| (resumed_handlers.clone(), new_frames.clone()));
    NATIVE_CPS_I64_RETURN_FRAMES.with(|f| {
        f.borrow_mut().replace(new_frames);
    });
    NATIVE_CPS_I64_HANDLER_STACK.with(|s| {
        s.borrow_mut().replace(resumed_handlers);
    });
    NATIVE_CPS_I64_GUARD_STACK.with(|s| {
        s.borrow_mut()
            .restore_snapshot(resumption.guard_stack.clone());
    });
    let fresh_eval = NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    });
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = NativeCpsI64EvalContext {
            current_eval_id: fresh_eval,
            initial_frame_count: 0,
        };
    });
    if let Some((resumed_handlers, new_frames)) = trace_state {
        eprintln!(
            "[JIT-CPS] effectful_apply_resumption.out: rid={} anchor={:?} fresh_eval={} combined_len={} resumed={} resumed_handlers={} new_frames={}",
            resumption.debug_id,
            anchor,
            fresh_eval,
            combined_len,
            resumed_len,
            format_handler_stack(&resumed_handlers),
            format_return_frames(&new_frames),
        );
    }
    (resumption.code)(resumption.env.as_ptr(), arg)
}

/// write27-d d4: 0..4 env-slot variants for the resumption apply
/// helper. The codegen passes the resume continuation's env slots
/// inline so this helper doesn't need to read them from anywhere
/// else.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_effectful_apply_resumption_i64_0(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        Vec::new(),
    )
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_effectful_apply_resumption_i64_1(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        vec![a],
    )
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_effectful_apply_resumption_i64_2(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        vec![a, b],
    )
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_effectful_apply_resumption_i64_3(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
    c: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        vec![a, b, c],
    )
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_effectful_apply_resumption_i64_4(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        vec![a, b, c, d],
    )
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_effectful_apply_resumption_i64_many(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    ptr: *const i64,
    len: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        unsafe { native_i64_slice(ptr, len) },
    )
}

/// write27-d d4: runtime predicate used by EffectfulApply codegen to
/// branch into the closure or resumption path.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_is_resumption_i64(value: i64) -> i64 {
    let is = NATIVE_CPS_I64_RESUMPTIONS.with(|s| s.borrow().contains(&(value as usize)));
    i64::from(is)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_select_handler_i64(
    fallback_handler: i64,
    effect_mask: i64,
    blocked: i64,
) -> i64 {
    let stack = current_native_i64_handler_stack_with_fallback(fallback_handler, effect_mask);
    // write27-d d6: two-pass search to dodge JIT-only `PendingEnv`
    // placeholders. `take_pending_native_i64_handler_frames` builds
    // these from capture envs without a real prompt/escape; they
    // appear in resumption/thunk handler snapshots and would
    // otherwise shadow legitimate handlers. Legacy installs and
    // static fallbacks stay first-class so existing abort_i64 paths
    // still resolve.
    let is_preferred_origin = |origin: NativeCpsI64HandlerFrameOrigin| {
        !matches!(origin, NativeCpsI64HandlerFrameOrigin::PendingEnv)
    };
    let frame_allowed = |frame: &NativeCpsI64HandlerFrame| {
        let allowed = (frame.consumes_mask & effect_mask) != 0;
        if !allowed {
            return false;
        }
        if blocked >= 0 && frame.guard_stack.contains(&blocked) {
            return false;
        }
        true
    };
    let chosen = stack
        .iter()
        .enumerate()
        .rev()
        .find(|(_, frame)| frame_allowed(frame) && is_preferred_origin(frame.origin))
        .or_else(|| {
            stack
                .iter()
                .enumerate()
                .rev()
                .find(|(_, frame)| frame_allowed(frame))
        });
    if let Some((index, frame)) = chosen {
        // write27-c c3: stash the pre-truncation stack so the post-arm
        // `restore_outer_handler_stack` can reinstate the matched
        // handler. The arm body itself still sees the truncated stack
        // (matches Layer 1/2's `handler_body_stack`).
        NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| {
            snaps.borrow_mut().push(stack.clone());
        });
        // write27-c c3: record the selected frame's metadata so the
        // post-arm path can wrap the natural return as a ScopeReturn
        // targeting this frame's escape.
        NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|meta| {
            meta.borrow_mut().push(NativeCpsI64SelectedHandlerMeta {
                prompt: frame.prompt,
                escape_continuation: frame.escape_continuation,
                escape_env: frame.escape_env.clone(),
                return_frame_threshold: frame.return_frame_threshold,
                install_eval_id: frame.install_eval_id,
                synthetic: frame.install_eval_id == NATIVE_CPS_I64_SYNTHETIC_EVAL_ID
                    || frame.escape_continuation == 0,
            });
        });
        NATIVE_CPS_I64_HANDLER_STACK.with(|active| {
            active.borrow_mut().replace(stack[..index].to_vec());
        });
        NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| {
            *envs.borrow_mut() = frame.envs.to_vec();
        });
        NATIVE_CPS_I64_SELECTED_HANDLER_ID.with(|handler| *handler.borrow_mut() = frame.handler);
        NATIVE_CPS_I64_SELECTED_HANDLER_OWNER_FUNCTION_ID
            .with(|owner| *owner.borrow_mut() = frame.escape_owner_function_id);
        NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow_mut() = false);
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] perform_select: handler={} prompt={} install_eval={} owner_fn={} synthetic={} threshold={} idx={} origin={:?} envs={}",
                frame.handler,
                frame.prompt,
                frame.install_eval_id,
                frame.escape_owner_function_id,
                frame.install_eval_id == NATIVE_CPS_I64_SYNTHETIC_EVAL_ID,
                frame.return_frame_threshold,
                index,
                frame.origin,
                format_handler_envs(&frame.envs),
            );
        }
        return frame.handler;
    }
    NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
    NATIVE_CPS_I64_SELECTED_HANDLER_ID.with(|handler| *handler.borrow_mut() = -1);
    NATIVE_CPS_I64_SELECTED_HANDLER_OWNER_FUNCTION_ID.with(|owner| *owner.borrow_mut() = 0);
    NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow_mut() = false);
    -1
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_active_blocked_guard_i64(effect_mask: i64) -> i64 {
    NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| {
        let stack = stack.borrow();
        let mut peeled = HashSet::new();
        let mut selected = -1;
        for blocked in stack.iter().rev() {
            if peeled.contains(&blocked.guard_id) {
                continue;
            }
            if !blocked.active {
                // `add_id[peek, X]` lowers to an inactive boundary for the
                // same guard. It peels the corresponding active blocker for
                // inner operations, so keep the inactive marker in the stack
                // and let reverse dispatch cancel older entries.
                peeled.insert(blocked.guard_id);
                continue;
            }
            if (blocked.allowed_mask & effect_mask) == 0 {
                selected = blocked.guard_id;
                break;
            }
        }
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] active_blocked: effect_mask={} selected={} stack={:?}",
                effect_mask,
                selected,
                stack
                    .iter()
                    .map(|entry| (entry.guard_id, entry.allowed_mask, entry.active))
                    .collect::<Vec<_>>()
            );
        }
        selected
    })
}

/// write27-c c3: reinstate the outer handler stack saved at the most
/// recent `select_handler` call. The Perform path calls this after
/// the arm body returns so the post-arm `route_scope_return` can walk
/// the full pre-truncation stack (mirrors Layer 1/2 where
/// `active_handlers` is a local variable and arm body mutations
/// don't propagate).
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_restore_outer_handler_stack_i64() -> i64 {
    NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| {
        if let Some(snap) = snaps.borrow_mut().pop() {
            NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
                stack.borrow_mut().replace(snap);
            });
        }
    });
    0
}

/// write27-c c3: combined Perform-arm finish path.
///   1. Restore the pre-truncation handler stack saved at
///      `select_handler` time.
///   2. If the selected handler is real (non-synthetic) AND no
///      ScopeReturn is already active, wrap `value` as a ScopeReturn
///      targeting that handler's escape.
///   3. Try to route any active ScopeReturn to its destination
///      (current handler stack walk, then return-frame walk). Returns
///      the escape's result on hit; the original `value` on miss
///      (with the slot left active to propagate further).
///   4. If the selected handler was synthetic (or no meta exists) AND
///      the legacy abort slot is not set, set it to `routed` so old
///      callback / fold propagation paths can bubble up.
/// Returns the value the JIT function should hand back to its caller.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_perform_finish_i64(value: i64) -> i64 {
    // 1. restore outer.
    NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| {
        if let Some(snap) = snaps.borrow_mut().pop() {
            NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
                stack.borrow_mut().replace(snap);
            });
        }
    });
    // 2. wrap as ScopeReturn if applicable.
    let meta = NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|m| m.borrow_mut().pop());
    let is_real = meta
        .as_ref()
        .map(|m| !m.synthetic && m.escape_continuation != 0)
        .unwrap_or(false);
    let already_active = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active);
    if is_real && !already_active {
        let meta = meta.as_ref().expect("is_real implies meta");
        NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::None);
        NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
            *slot.borrow_mut() = NativeCpsI64ScopeReturn {
                active: true,
                prompt: meta.prompt,
                target: meta.escape_continuation as i64,
                value,
            };
        });
        if jit_trace_enabled() {
            let current_eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().current_eval_id);
            let current_initial =
                NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);
            let stack = NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().to_vec());
            let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().to_vec());
            eprintln!(
                "[JIT-CPS] scope_return_set (perform_finish): prompt={} target={:#x} value={} current_eval={} initial={} stack={} frames={}",
                meta.prompt,
                meta.escape_continuation,
                describe_native_i64_value(value),
                current_eval,
                current_initial,
                format_handler_stack(&stack),
                format_return_frames(&frames),
            );
        }
    }
    // 3. route.
    let routed = yulang_cps_route_scope_return_i64(value);
    // 4. legacy abort fallback (synthetic handler / no SR path).
    if !is_real {
        let abort_already = NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().is_active());
        if !abort_already {
            NATIVE_CPS_I64_ABORT
                .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(routed));
        }
    }
    routed
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_perform_finish_escaped_i64(value: i64) -> i64 {
    NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| {
        if let Some(snap) = snaps.borrow_mut().pop() {
            NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
                stack.borrow_mut().replace(snap);
            });
        }
    });
    let meta = NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|meta| meta.borrow_mut().pop());
    if NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active) {
        return yulang_cps_route_scope_return_i64(value);
    }
    let mut abort_outer_eval = false;
    if let Some(meta) = meta {
        if meta.synthetic || meta.escape_continuation == 0 {
            return value;
        }
        let current_eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().current_eval_id);
        let used_rwh_env = NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow());
        if meta.install_eval_id != current_eval && used_rwh_env {
            return value;
        }
        if meta.install_eval_id != current_eval {
            NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::None);
            NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
                *slot.borrow_mut() = NativeCpsI64ScopeReturn {
                    active: true,
                    prompt: meta.prompt,
                    target: meta.escape_continuation as i64,
                    value,
                };
            });
            return yulang_cps_route_scope_return_i64(value);
        }
        abort_outer_eval = meta.return_frame_threshold == 0;
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            let mut frames = frames.borrow_mut();
            if frames.len() > meta.return_frame_threshold {
                frames.truncate(meta.return_frame_threshold);
            }
        });
    }
    let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    if frame_len == 0 {
        let current_initial =
            NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);
        if abort_outer_eval && current_initial > 0 {
            NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(value));
        }
        return value;
    }
    let result = yulang_cps_continue_return_frame_i64(value);
    let current_initial = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);
    if abort_outer_eval && current_initial > 0 {
        NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(result));
    }
    result
}

/// write27-c c3: if no ScopeReturn is active, wrap `value` as a
/// ScopeReturn targeting the most-recently-selected handler's escape.
/// If the selected handler is synthetic (no real escape), this is a
/// no-op and `value` flows through as the eval frame's natural result.
/// Always returns `value` so the codegen can `return` it directly.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_scope_return_from_selected_handler_i64(value: i64) -> i64 {
    let already_active = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active);
    if already_active {
        return value;
    }
    let meta = NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|m| m.borrow().last().cloned());
    let Some(meta) = meta else {
        return value;
    };
    if meta.synthetic || meta.escape_continuation == 0 {
        return value;
    }
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64ScopeReturn {
            active: true,
            prompt: meta.prompt,
            target: meta.escape_continuation as i64,
            value,
        };
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] scope_return_set (from selected): prompt={} target={:#x} value={}",
            meta.prompt, meta.escape_continuation, value
        );
    }
    value
}

fn find_current_native_i64_scope_handler(
    prompt: u64,
    current_eval: u64,
    skip_current: bool,
) -> Option<NativeCpsI64CurrentScopeHandlerMatch> {
    if skip_current {
        return None;
    }
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let stack = stack.borrow();
        stack
            .iter()
            .rposition(|frame| frame.prompt == prompt && frame.install_eval_id == current_eval)
            .map(|handler_index| NativeCpsI64CurrentScopeHandlerMatch {
                handler_index,
                handler: stack[handler_index].clone(),
            })
    })
}

fn find_native_i64_scope_handler_in_return_frames(
    prompt: u64,
) -> Option<NativeCpsI64ReturnFrameScopeHandlerMatch> {
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        let frames = frames.borrow();
        for return_frame_index in (0..frames.len()).rev() {
            let return_frame = &frames[return_frame_index];
            for (handler_index, handler) in return_frame.handlers.iter().enumerate().rev() {
                if handler.prompt == prompt
                    && handler.install_eval_id == return_frame.owner_eval_id
                    && handler.escape_owner_function_id == return_frame.owner_function_id
                {
                    return Some(NativeCpsI64ReturnFrameScopeHandlerMatch {
                        return_frame_index,
                        handler_index,
                        return_frame: return_frame.clone(),
                        handler: handler.clone(),
                    });
                }
            }
        }
        None
    })
}

/// write27-c c4: dispatch the active `ScopeReturn` slot. Returns the
/// resumed escape's result when a match is found, otherwise leaves
/// the slot active and returns `fallback_value` so the caller can
/// keep propagating up.
///
/// Search order mirrors `cps_eval`/`cps_repr`:
/// 1. Current handler stack: rposition by (prompt, install_eval_id ==
///    current_eval_id). On hit, truncate to that index, truncate
///    return_frames to the matched frame's threshold, clear slot,
///    call escape with the slot's value.
/// 2. Return frames `[current_initial..]`: rposition by frame snapshot
///    handler with (prompt, install_eval_id == frame.owner_eval_id).
///    On hit, restore that frame's snapshot, truncate stack/frames,
///    set eval context, clear slot, call escape.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_route_scope_return_i64(fallback_value: i64) -> i64 {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::RouteScopeReturn);
    let sr = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().clone());
    if !sr.active {
        return fallback_value;
    }
    let prompt = sr.prompt;
    // The active slot stores the destination prompt/escape plus the value
    // currently being propagated through the native stack. A caller can
    // transform a ScopeReturn while unwinding (for example a handler value arm
    // returning `(v, log)` after `k()` produced `v`). In that case the helper's
    // argument is the fresh propagated value; using the older slot payload lets
    // the inner block-tail escape past the value arm.
    let value = fallback_value;
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.active && slot.prompt == prompt {
            slot.value = value;
        }
    });
    let current_eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().current_eval_id);
    let current_initial = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);

    if jit_trace_enabled() {
        let stack = NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().to_vec());
        let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().to_vec());
        eprintln!(
            "[JIT-CPS] route_scope_return.scan: prompt={} value={} current_eval={} initial={} force_frame_walk={} stack={} frames={}",
            prompt,
            describe_native_i64_value(value),
            current_eval,
            current_initial,
            jit_force_frame_walk_sr(),
            format_handler_stack(&stack),
            format_return_frames(&frames),
        );
    }

    // write27-e e4: optionally skip the current-handler scan so we can
    // see whether the frame-walk path matches Layer 1/2's frontier.
    // Toggled via `YULANG_CPS_JIT_FORCE_FRAME_WALK_SR=1`.
    let skip_current = jit_force_frame_walk_sr();

    // 1. Walk the current handler stack reverse.
    if let Some(scope_match) =
        find_current_native_i64_scope_handler(prompt, current_eval, skip_current)
    {
        let handler_index = scope_match.handler_index;
        let frame = scope_match.handler;
        let mut post_handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().to_vec());
        post_handlers.truncate(handler_index);
        let mut post_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().to_vec());
        // Use the handler's install-time threshold. A prompt_exit marker can
        // be outside the already-routed frame slice, while the threshold is
        // the boundary captured with the handler frame itself.
        let truncate_at = frame.return_frame_threshold;
        if post_frames.len() > truncate_at {
            post_frames.truncate(truncate_at);
        }
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
            stack.borrow_mut().replace(post_handlers.clone());
        });
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            frames.borrow_mut().replace(post_frames.clone());
        });
        NATIVE_CPS_I64_SCOPE_RETURN
            .with(|slot| *slot.borrow_mut() = NativeCpsI64ScopeReturn::default());
        NATIVE_CPS_I64_RETURN_FRAMES_ROUTED.with(|routed| *routed.borrow_mut() = true);
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] route_scope_return: prompt={} current_eval={} initial={} action=current_handler value={}",
                prompt,
                current_eval,
                current_initial,
                describe_native_i64_value(value)
            );
        }
        if frame.escape_continuation == 0 {
            if current_initial > 0 && post_handlers.is_empty() {
                NATIVE_CPS_I64_ABORT
                    .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(value));
            }
            return value;
        }
        let escape_env = refreshed_escape_env(&frame);
        if current_initial > 0 && post_handlers.is_empty() && frame.guard_stack.is_empty() {
            let result =
                call_native_i64_continuation(frame.escape_continuation, &escape_env, value);
            NATIVE_CPS_I64_ABORT
                .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(result));
            return result;
        }
        // A current-stack match can still jump out of an inner eval frame
        // when the dynamic handler was restored from a captured return frame.
        // Keep the same short-circuit signal used by the frame-walk path so
        // skipped native callers do not continue with their normal fallback.
        if current_initial > 0 {
            NATIVE_CPS_I64_ABORT.with(|slot| {
                *slot.borrow_mut() = routed_jump_abort(
                    value,
                    truncate_at,
                    frame.escape_continuation,
                    escape_env,
                    post_handlers,
                    frame.guard_stack.to_vec(),
                    post_frames,
                    NativeCpsI64EvalContext {
                        current_eval_id: frame.install_eval_id,
                        initial_frame_count: truncate_at,
                    },
                );
            });
            return value;
        }
        let result = call_native_i64_continuation(frame.escape_continuation, &escape_env, value);
        return result;
    }

    // 2. Walk the whole return-frame snapshot to find a captured handler
    //    that matches. The original install scope can live in an inherited
    //    prefix after callbacks or resumptions; matching by the frame's
    //    owner eval keeps this precise without relying on prompt-only
    //    routing.
    if let Some(scope_match) = find_native_i64_scope_handler_in_return_frames(prompt) {
        let return_frame_index = scope_match.return_frame_index;
        let handler_index = scope_match.handler_index;
        let frame = scope_match.return_frame;
        let handler = scope_match.handler;
        // Restore handler stack to frame.handlers[..hi].
        let mut post_handlers = frame.handlers.to_vec();
        post_handlers.truncate(handler_index);
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
            stack.borrow_mut().replace(post_handlers.clone());
        });
        NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
            stack.borrow_mut().restore_snapshot(frame.guards.clone());
        });
        let mut post_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().to_vec());
        post_frames.truncate(return_frame_index);
        // Use the handler's install-time threshold. A prompt_exit marker can
        // be outside the already-routed frame slice, while the threshold is
        // the boundary captured with the handler frame itself.
        let truncate_at = handler.return_frame_threshold;
        if post_frames.len() > truncate_at {
            post_frames.truncate(truncate_at);
        }
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            frames.borrow_mut().replace(post_frames.clone());
        });
        // Set eval context to frame's owner (capped to current frames).
        let rest_len = post_frames.len();
        let owner_initial = frame.owner_initial_frame_count.min(rest_len);
        let post_eval_context = NativeCpsI64EvalContext {
            current_eval_id: frame.owner_eval_id,
            initial_frame_count: owner_initial,
        };
        NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = post_eval_context);
        NATIVE_CPS_I64_SCOPE_RETURN
            .with(|slot| *slot.borrow_mut() = NativeCpsI64ScopeReturn::default());
        NATIVE_CPS_I64_RETURN_FRAMES_ROUTED.with(|routed| *routed.borrow_mut() = true);
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] route_scope_return: prompt={} current_eval={} initial={} action=frame_walk fi={} hi={} value={}",
                prompt,
                current_eval,
                current_initial,
                return_frame_index,
                handler_index,
                describe_native_i64_value(value)
            );
        }
        if handler.escape_continuation == 0 {
            if current_initial > 0 && post_handlers.is_empty() {
                NATIVE_CPS_I64_ABORT
                    .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(value));
            }
            return value;
        }
        let escape_env = refreshed_escape_env(&handler);
        if current_initial > 0 && post_handlers.is_empty() && handler.guard_stack.is_empty() {
            let result =
                call_native_i64_continuation(handler.escape_continuation, &escape_env, value);
            NATIVE_CPS_I64_ABORT
                .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(result));
            return result;
        }
        if current_initial > 0 {
            NATIVE_CPS_I64_ABORT.with(|slot| {
                *slot.borrow_mut() = routed_jump_abort(
                    value,
                    truncate_at,
                    handler.escape_continuation,
                    escape_env,
                    post_handlers,
                    frame.guards.to_vec(),
                    post_frames,
                    post_eval_context,
                );
            });
            return value;
        }
        let result = call_native_i64_continuation(handler.escape_continuation, &escape_env, value);
        return result;
    }

    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] route_scope_return: prompt={} current_eval={} initial={} action=propagate value={}",
            prompt,
            current_eval,
            current_initial,
            describe_native_i64_value(value)
        );
    }
    fallback_value
}

#[allow(dead_code)]
fn routed_scope_return_abort(
    value: i64,
    return_frame_threshold: usize,
    restore_frames: NativeCpsI64ReturnFrameSnapshot,
) -> NativeCpsI64Abort {
    NativeCpsI64Abort::Scoped {
        value,
        return_frame_threshold,
        propagate_at_threshold: false,
        restore_frames,
    }
}

fn routed_jump_abort(
    value: i64,
    return_frame_threshold: usize,
    continuation: usize,
    env: NativeCpsI64I64Snapshot,
    handlers: Vec<NativeCpsI64HandlerFrame>,
    guards: Vec<i64>,
    return_frames: Vec<NativeCpsI64ReturnFrame>,
    eval_context: NativeCpsI64EvalContext,
) -> NativeCpsI64Abort {
    NativeCpsI64Abort::RoutedJump {
        value,
        return_frame_threshold,
        continuation,
        env,
        handlers,
        guards,
        return_frames: native_cps_i64_snapshot(return_frames),
        eval_context,
    }
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_capture_handler_env_i64(
    handler: i64,
    entry: i64,
    env: i64,
) -> i64 {
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| {
        envs.borrow_mut().push((
            handler,
            NativeCpsI64HandlerEnv {
                entry,
                env,
                slots: Vec::new(),
            },
        ));
    });
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_capture_handler_env_mapped_i64(
    handler: i64,
    entry: i64,
    env: i64,
    target_ptr: *const i64,
    value_ptr: *const i64,
    target_len: i64,
    value_len: i64,
) -> i64 {
    let len = target_len.min(value_len).max(0) as usize;
    let targets = unsafe { native_i64_slice(target_ptr, len as i64) };
    let values = unsafe { native_i64_slice(value_ptr, len as i64) };
    let slots = targets
        .iter()
        .copied()
        .zip(values.iter().copied())
        .collect::<Vec<_>>();
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| {
        envs.borrow_mut()
            .push((handler, NativeCpsI64HandlerEnv { entry, env, slots }));
    });
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_set_pending_escape_env_targets_i64(
    ptr: *const i64,
    len: i64,
) -> i64 {
    let targets = unsafe { native_i64_slice(ptr, len) };
    NATIVE_CPS_I64_PENDING_ESCAPE_ENV_TARGETS.with(|slot| {
        *slot.borrow_mut() = targets.to_vec();
    });
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_install_handler_i64(handler: i64, consumes_mask: i64) -> i64 {
    let envs = take_pending_native_i64_handler_envs(handler);
    let frame = NativeCpsI64HandlerFrame {
        handler,
        consumes_mask,
        guard_stack: current_native_i64_guard_snapshot(),
        envs: native_cps_i64_snapshot(envs),
        prompt: 0,
        install_eval_id: NATIVE_CPS_I64_SYNTHETIC_EVAL_ID,
        escape_owner_function_id: 0,
        threshold_owner_function_id: 0,
        inherited: false,
        escape_continuation: 0,
        escape_env: native_cps_i64_empty_snapshot(),
        escape_env_targets: native_cps_i64_empty_snapshot(),
        return_frame_threshold: 0,
        return_frame_prefix: native_cps_i64_snapshot(Vec::new()),
        origin: NativeCpsI64HandlerFrameOrigin::LegacyInstall,
    };
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        stack.borrow_mut().push(frame);
    });
    if jit_trace_enabled() {
        eprintln!("[JIT-CPS] install_handler (legacy): handler={}", handler);
    }
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_uninstall_handler_i64(handler: i64) -> i64 {
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        if let Some(pos) = stack.iter().rposition(|frame| frame.handler == handler) {
            stack.remove(pos);
        }
    });
    0
}

// =====================================================================
// write27-c c2: full handler install. New helpers carry prompt /
// install_eval_id / escape_continuation / escape_env /
// return_frame_threshold so that ScopeReturn-based Perform (c3) and
// route_scope_return (c4) can dispatch correctly. The legacy
// `yulang_cps_install_handler_i64` stays in place — it constructs a
// synthetic frame with no escape and is only safe for paths that do
// not depend on ScopeReturn routing.
// =====================================================================

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_fresh_prompt_i64() -> i64 {
    NATIVE_CPS_I64_NEXT_PROMPT.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id.wrapping_add(1);
        id as i64
    })
}

fn install_native_i64_handler_full(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    escape_env: Vec<i64>,
) {
    let envs = take_pending_native_i64_handler_envs(handler);
    let trace_envs = jit_trace_enabled().then(|| format_handler_envs(&envs));
    let threshold = return_frame_threshold.max(0) as usize;
    let escape_owner = escape_owner_function_id.max(0) as u64;
    let threshold_owner_function_id = if threshold == 0 {
        escape_owner
    } else {
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            frames
                .borrow()
                .get(threshold - 1)
                .map(|frame| frame.owner_function_id)
                .unwrap_or(escape_owner)
        })
    };
    let return_frame_prefix = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        frames
            .borrow()
            .iter()
            .take(threshold)
            .cloned()
            .collect::<Vec<_>>()
    });
    let frame = NativeCpsI64HandlerFrame {
        handler,
        consumes_mask,
        guard_stack: current_native_i64_guard_snapshot(),
        envs: native_cps_i64_snapshot(envs),
        prompt: prompt as u64,
        install_eval_id: install_eval_id as u64,
        escape_owner_function_id: escape_owner,
        threshold_owner_function_id,
        inherited: inherited != 0,
        escape_continuation: escape_continuation as usize,
        escape_env: native_cps_i64_snapshot(escape_env),
        escape_env_targets: native_cps_i64_snapshot(take_pending_native_i64_escape_env_targets()),
        return_frame_threshold: threshold,
        return_frame_prefix: native_cps_i64_snapshot(return_frame_prefix),
        origin: NativeCpsI64HandlerFrameOrigin::RealInstall,
    };
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        stack.borrow_mut().push(frame);
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] install_handler_full: handler={} prompt={} install_eval={} owner_fn={} consumes={} threshold={} threshold_owner={} escape={:#x} envs={}",
            handler,
            prompt,
            install_eval_id,
            escape_owner_function_id,
            consumes_mask,
            return_frame_threshold,
            threshold_owner_function_id,
            escape_continuation as usize,
            trace_envs.as_deref().unwrap_or("[]")
        );
    }
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_install_handler_full_i64_0(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        Vec::new(),
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_install_handler_full_i64_1(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    a: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        vec![a],
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_install_handler_full_i64_2(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    a: i64,
    b: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        vec![a, b],
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_install_handler_full_i64_3(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    a: i64,
    b: i64,
    c: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        vec![a, b, c],
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_install_handler_full_i64_4(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        vec![a, b, c, d],
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_abort_i64(value: i64) -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64Abort::Global(value);
    });
    value
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_abort_active_i64() -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| {
        let value = slot.borrow().clone();
        let active = value.is_active();
        if jit_trace_enabled() && active {
            eprintln!(
                "[JIT-CPS] abort_active: value={}",
                describe_native_i64_value(value.value_or_zero())
            );
        }
        i64::from(active)
    })
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_abort_should_return_i64() -> i64 {
    i64::from(yulang_cps_abort_mode_i64() == 1)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_routed_jump_should_return_i64() -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| i64::from(slot.borrow().routed_jump_should_return()))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_abort_mode_i64() -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| {
        let abort = slot.borrow().clone();
        let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
        let mode = abort.mode_at_frame_len(frame_len);
        if jit_trace_enabled() && mode != 0 {
            eprintln!(
                "[JIT-CPS] abort_mode: mode={} frame_len={} value={}",
                mode,
                frame_len,
                describe_native_i64_value(abort.value_or_zero())
            );
        }
        mode
    })
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_abort_value_i64() -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().value_or_zero())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_consume_abort_i64() -> i64 {
    consume_native_i64_abort()
}

fn consume_native_i64_abort() -> i64 {
    let cleared_abort = NATIVE_CPS_I64_ABORT.with(|slot| {
        let mut slot = slot.borrow_mut();
        let cleared_abort = std::mem::take(&mut *slot);
        *slot = NativeCpsI64Abort::None;
        cleared_abort
    });
    match cleared_abort {
        NativeCpsI64Abort::None => 0,
        NativeCpsI64Abort::Global(value) => value,
        NativeCpsI64Abort::Scoped {
            value,
            return_frame_threshold,
            restore_frames,
            propagate_at_threshold: false,
        } => {
            restore_native_i64_return_frame_prefix(&restore_frames);
            let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
            let offset = return_frame_threshold.saturating_sub(frame_len);
            if offset > 0 {
                NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET.with(|slot| {
                    let mut slot = slot.borrow_mut();
                    *slot = (*slot).max(offset);
                });
            }
            value
        }
        NativeCpsI64Abort::Scoped { value, .. } => value,
        NativeCpsI64Abort::RoutedJump {
            value,
            continuation,
            env,
            handlers,
            guards,
            return_frames,
            eval_context,
            ..
        } => resume_native_i64_routed_jump(
            value,
            continuation,
            env,
            handlers,
            guards,
            return_frames,
            eval_context,
        ),
    }
}

fn resume_native_i64_routed_jump(
    value: i64,
    continuation: usize,
    env: NativeCpsI64I64Snapshot,
    handlers: Vec<NativeCpsI64HandlerFrame>,
    guards: Vec<i64>,
    return_frames: NativeCpsI64ReturnFrameSnapshot,
    eval_context: NativeCpsI64EvalContext,
) -> i64 {
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        stack.borrow_mut().replace(handlers);
    });
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
        stack.borrow_mut().replace(guards);
    });
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().clear());
    park_native_i64_routed_return_frames(eval_context, return_frames);
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = eval_context);
    call_native_i64_continuation(continuation, &env, value)
}

fn park_native_i64_routed_return_frames(
    eval_context: NativeCpsI64EvalContext,
    frames: NativeCpsI64ReturnFrameSnapshot,
) {
    NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES.with(|pending| {
        *pending.borrow_mut() = Some(NativeCpsI64PendingRoutedReturnFrames::new(
            eval_context.initial_frame_count,
            frames,
        ));
    });
}

fn clear_pending_native_i64_routed_return_frames() {
    NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES.with(|pending| *pending.borrow_mut() = None);
}

fn take_pending_native_i64_routed_return_frames(
    initial: usize,
) -> Option<NativeCpsI64PendingRoutedReturnFrames> {
    NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES.with(|pending| {
        let mut pending = pending.borrow_mut();
        let should_restore = pending
            .as_ref()
            .is_some_and(|frames| frames.should_restore_for_initial(initial));
        if should_restore { pending.take() } else { None }
    })
}

fn restore_pending_routed_return_frames_for_normal_return(initial: usize) {
    let pending = take_pending_native_i64_routed_return_frames(initial);
    if let Some(pending) = pending {
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            let mut frames = frames.borrow_mut();
            if frames.is_empty() {
                frames.replace(pending.frames.to_vec());
            }
        });
    }
}

fn clear_native_i64_abort() {
    let cleared_abort = NATIVE_CPS_I64_ABORT.with(|slot| {
        let mut slot = slot.borrow_mut();
        let cleared_abort = std::mem::take(&mut *slot);
        *slot = NativeCpsI64Abort::None;
        cleared_abort
    });
    let restore_consumed_frames = matches!(
        cleared_abort,
        NativeCpsI64Abort::Scoped {
            propagate_at_threshold: false,
            ..
        }
    );
    if restore_consumed_frames {
        if let NativeCpsI64Abort::Scoped {
            return_frame_threshold,
            restore_frames,
            ..
        } = cleared_abort.clone()
        {
            restore_native_i64_return_frame_prefix(&restore_frames);
            let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
            let offset = return_frame_threshold.saturating_sub(frame_len);
            if offset > 0 {
                NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET.with(|slot| {
                    let mut slot = slot.borrow_mut();
                    *slot = (*slot).max(offset);
                });
            }
        }
    }
}

fn restore_native_i64_return_frame_prefix(prefix: &[NativeCpsI64ReturnFrame]) {
    if prefix.is_empty() {
        return;
    }
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        let mut frames = frames.borrow_mut();
        let current = frames
            .iter()
            .map(|frame| (frame.debug_id, frame.clone()))
            .collect::<HashMap<_, _>>();
        *frames = prefix
            .iter()
            .map(|frame| {
                current
                    .get(&frame.debug_id)
                    .cloned()
                    .unwrap_or_else(|| frame.clone())
            })
            .collect();
    });
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_clear_abort_i64() -> i64 {
    clear_native_i64_abort();
    0
}

// =====================================================================
// write27-a: ScopeReturn slot helpers.
// Mirrors `cps_eval`/`cps_repr` ScopeReturn { prompt, target, value }.
// Old `abort` helpers stay in place for backward-compat paths; new
// codegen (Perform/EffectfulCall etc.) should use these instead.
// =====================================================================

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_scope_return_i64(prompt: i64, target: i64, value: i64) -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64ScopeReturn {
            active: true,
            prompt: prompt as u64,
            target,
            value,
        };
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] scope_return_set: prompt={} target={} value={}",
            prompt, target, value
        );
    }
    value
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_scope_return_active_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| i64::from(slot.borrow().active))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_scope_return_prompt_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().prompt as i64)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_scope_return_target_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().target)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_scope_return_value_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().value)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_clear_scope_return_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64ScopeReturn::default();
    });
    0
}

// =====================================================================
// write27-a: eval context helpers.
// Track current_eval_id and initial_frame_count for the JIT analogue
// of cps_eval's eval signatures. continue_return_frames-style logic
// restores eval_context from a popped return frame.
// =====================================================================

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_fresh_eval_id_i64() -> i64 {
    NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id as i64
    })
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_current_eval_id_i64() -> i64 {
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().current_eval_id as i64)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_current_initial_frame_count_i64() -> i64 {
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count as i64)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_set_eval_context_i64(
    eval_id: i64,
    initial_frame_count: i64,
) -> i64 {
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = NativeCpsI64EvalContext {
            current_eval_id: eval_id as u64,
            initial_frame_count: initial_frame_count.max(0) as usize,
        };
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] set_eval_context: eval={} initial={}",
            eval_id, initial_frame_count
        );
    }
    0
}

// =====================================================================
// write27-a: return-frame stack helpers.
// Each EffectfulCall/Apply/Force pushes a frame; a continue_return_frames
// step pops the innermost frame and invokes its continuation. The actual
// "continue and resume" wiring is implemented by future write27 steps
// in concert with codegen; this commit only exposes the storage and
// raw push/pop primitives.
// =====================================================================

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_return_frame_len_i64() -> i64 {
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len() as i64)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_handler_return_frame_threshold_i64() -> i64 {
    let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    let offset = NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET
        .with(|slot| std::mem::take(&mut *slot.borrow_mut()));
    (frame_len + offset) as i64
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_enter_handler_arm_i64() -> i64 {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::HandlerArm);
    let saved = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().take());
    let consumed_start = NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| ids.borrow().len());
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] enter_handler_arm: saved_frames={}",
            format_return_frames(&saved)
        );
    }
    NATIVE_CPS_I64_HANDLER_ARM_RETURN_FRAME_SNAPSHOTS.with(|snapshots| {
        snapshots
            .borrow_mut()
            .push(NativeCpsI64HandlerArmReturnFrameSnapshot {
                frames: saved,
                consumed_start,
            });
    });
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_exit_handler_arm_i64() -> i64 {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::HandlerArm);
    let snapshot = NATIVE_CPS_I64_HANDLER_ARM_RETURN_FRAME_SNAPSHOTS
        .with(|snapshots| snapshots.borrow_mut().pop().unwrap_or_default());
    let consumed_since = NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| {
        ids.borrow()
            .iter()
            .skip(snapshot.consumed_start)
            .copied()
            .collect::<HashSet<_>>()
    });
    let restored: Vec<NativeCpsI64ReturnFrame> = snapshot
        .frames
        .into_iter()
        .filter(|frame| !consumed_since.contains(&frame.debug_id))
        .collect();
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] exit_handler_arm: restored_frames={}",
            format_return_frames(&restored)
        );
    }
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        frames.borrow_mut().replace(restored);
    });
    0
}

fn push_native_i64_return_frame_with_env(
    prompt_exit: Option<NativeCpsI64PromptExitFrame>,
    continuation: i64,
    continuation_id: i64,
    env: Vec<i64>,
    owner_initial_frame_count: i64,
    owner_eval_id: i64,
    owner_function_id: i64,
    immediately_forces_param: i64,
) {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::PushReturnFrame);
    let handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow_mut().snapshot());
    let guards = NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow_mut().snapshot());
    let env_len = env.len();
    let len_before = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    let debug_id = next_native_i64_return_frame_debug_id();
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        frames.borrow_mut().push(NativeCpsI64ReturnFrame {
            prompt_exit,
            debug_id,
            continuation: continuation as usize,
            continuation_id: continuation_id.max(0) as u32,
            env: native_cps_i64_snapshot(env),
            handlers,
            guards,
            owner_initial_frame_count: owner_initial_frame_count.max(0) as usize,
            owner_eval_id: owner_eval_id as u64,
            owner_function_id: owner_function_id.max(0) as u64,
            immediately_forces_param: immediately_forces_param != 0,
        });
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] push_return_frame: id={} k={} len_before={} len_after={} cont={:#x} env_len={} owner_initial={} owner_eval={} owner_fn={} immediate_force={}",
            debug_id,
            continuation_id,
            len_before,
            len_before + 1,
            continuation as usize,
            env_len,
            owner_initial_frame_count,
            owner_eval_id,
            owner_function_id,
            immediately_forces_param != 0,
        );
    }
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_push_return_frame_i64_0(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        Vec::new(),
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_push_return_frame_i64_1(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        vec![a],
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_push_return_frame_i64_2(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        vec![a, b],
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_push_return_frame_i64_3(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
    c: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        vec![a, b, c],
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_push_return_frame_i64_4(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        vec![a, b, c, d],
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_push_return_frame_i64_many(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    ptr: *const i64,
    len: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        unsafe { native_i64_slice(ptr, len) },
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

fn push_native_i64_prompt_exit_frame_with_env(
    prompt: i64,
    continuation: i64,
    continuation_id: i64,
    env: Vec<i64>,
    owner_initial_frame_count: i64,
    owner_eval_id: i64,
    owner_function_id: i64,
    immediately_forces_param: i64,
) {
    push_native_i64_return_frame_with_env(
        Some(NativeCpsI64PromptExitFrame {
            prompt: prompt as u64,
        }),
        continuation,
        continuation_id,
        env,
        owner_initial_frame_count,
        owner_eval_id,
        owner_function_id,
        immediately_forces_param,
    );
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_push_prompt_exit_frame_i64_0(
    prompt: i64,
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
) -> i64 {
    push_native_i64_prompt_exit_frame_with_env(
        prompt,
        continuation,
        continuation_id,
        Vec::new(),
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_push_prompt_exit_frame_i64_many(
    prompt: i64,
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    ptr: *const i64,
    len: i64,
) -> i64 {
    push_native_i64_prompt_exit_frame_with_env(
        prompt,
        continuation,
        continuation_id,
        unsafe { native_i64_slice(ptr, len) },
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

/// write27-b: pop the innermost return frame, restore its handler /
/// guard / eval context snapshots, and invoke the saved JIT
/// continuation with `value`. Returns the continuation's result.
///
/// Returning a Rust-side helper instead of just `pop` plus a Cranelift
/// trampoline keeps the env / state restore / continuation call atomic
/// — write27-b notes call this out as the main safety win.
///
/// Mirrors cps_eval / cps_repr's `continue_return_frames` single step.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_continue_return_frame_i64(value: i64) -> i64 {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::ContinueReturnFrame);
    with_native_cps_i64_stats(|stats| stats.continue_return_frame_calls += 1);
    // Pop the frame first, dropping the borrow before we invoke the
    // continuation (which may push new frames).
    let frame = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().pop());
    let Some(frame) = frame else {
        // No frame to consume — caller should have checked
        // `return_frame_len_i64()`; treat this as a no-op for safety.
        return value;
    };
    NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| {
        let mut ids = ids.borrow_mut();
        if !ids.contains(&frame.debug_id) {
            ids.push(frame.debug_id);
        }
    });
    let sibling_handlers_empty =
        NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| siblings.borrow().is_empty());
    let restored_handlers = if sibling_handlers_empty {
        None
    } else {
        let mut handlers = frame.handlers.to_vec();
        append_resume_with_handler_siblings(&mut handlers);
        Some(handlers)
    };
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] continue_return_frame: id={} owner_eval={} owner_initial={} restored_handlers_len={} restored_guards_len={} value={}",
            frame.debug_id,
            frame.owner_eval_id,
            frame.owner_initial_frame_count,
            restored_handlers
                .as_ref()
                .map(|handlers| handlers.len())
                .unwrap_or(frame.handlers.len()),
            frame.guards.len(),
            describe_native_i64_value(value),
        );
    }
    if let Some(restored_handlers) = restored_handlers {
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
            stack.borrow_mut().replace(restored_handlers);
        });
    } else {
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
            stack.borrow_mut().restore_snapshot(frame.handlers.clone());
        });
    }
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
        stack.borrow_mut().restore_snapshot(frame.guards.clone());
    });
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = NativeCpsI64EvalContext {
            current_eval_id: frame.owner_eval_id,
            initial_frame_count: frame.owner_initial_frame_count,
        };
    });
    call_native_i64_continuation(frame.continuation, &frame.env, value)
}

/// write27-b: peek at the innermost return frame's
/// `immediately_forces_param` flag without popping it. Used by the
/// JIT `Return` path to decide whether to fire pre-force v2.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_top_return_frame_pre_force_i64() -> i64 {
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        frames
            .borrow()
            .last()
            .map(|frame| i64::from(frame.immediately_forces_param))
            .unwrap_or(0)
    })
}

/// write27-b: pre-force v2 for the JIT. Mirrors cps_eval/cps_repr's
/// Return-terminator pre-force: when the Returned value is a Thunk and
/// the innermost own-frame's continuation immediately ForceThunks its
/// param, run that continuation in the top frame's owner context with
/// the frame retained in `return_frames` and the eval-context's
/// `initial_frame_count` set to the full frame length (so any deeper
/// Return that doesn't push new frames just bubbles back).
///
/// Caller has already verified:
///   - `value` is a thunk pointer (via `yulang_cps_is_thunk_i64`),
///   - `return_frame_len_i64() > current_initial_frame_count_i64()`,
///   - `yulang_cps_top_return_frame_pre_force_i64() != 0`.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_pre_force_top_frame_i64(value: i64) -> i64 {
    let saved_eval_ctx = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        let frames = frames.borrow();
        let top = frames.last().expect("pre-force called with no frame");
        // Restore the top frame's owner context. The frame is RETAINED
        // (we don't pop it) so the body's effects can capture it.
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
            stack.borrow_mut().restore_snapshot(top.handlers.clone());
        });
        NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
            stack.borrow_mut().restore_snapshot(top.guards.clone());
        });
        NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
            *ctx.borrow_mut() = NativeCpsI64EvalContext {
                current_eval_id: top.owner_eval_id,
                // Keep the caller eval's barrier. The thunk body runs before
                // the top frame is consumed, so effects can capture the frame
                // and a plain return can still flow through the retained
                // caller chain.
                initial_frame_count: saved_eval_ctx.initial_frame_count,
            };
        });
    });
    let forced = yulang_cps_force_thunk_i64(value as usize);
    match yulang_cps_abort_mode_i64() {
        1 => {
            return yulang_cps_abort_value_i64();
        }
        2 => {
            if native_i64_abort_is_routed_jump() {
                return yulang_cps_abort_value_i64();
            }
            return yulang_cps_consume_abort_i64();
        }
        _ => {}
    }
    if yulang_cps_abort_active_i64() != 0 {
        return yulang_cps_abort_value_i64();
    }
    if yulang_cps_scope_return_active_i64() != 0 {
        return yulang_cps_route_scope_return_i64(forced);
    }
    yulang_cps_continue_return_frame_i64(forced)
}

/// write27-b: JIT-side analogue of cps_eval's Return terminator. Use
/// this in place of `ireturn value` so that:
/// - if the eval has no own return frames, return value directly,
/// - if pre-force v2 fires, run the top frame's continuation in owner
///   context with the frame retained,
/// - otherwise, consume the innermost own frame and run its
///   continuation with `value`.
///
/// Callers don't have to know about Thunk classification: this helper
/// asks `yulang_cps_is_thunk_i64` (existing) when deciding pre-force.
#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_return_i64(value: i64) -> i64 {
    with_native_cps_i64_stats(|stats| stats.return_i64_calls += 1);
    let mut value = value;
    match yulang_cps_abort_mode_i64() {
        1 => {
            return yulang_cps_abort_value_i64();
        }
        2 => {
            if native_i64_abort_is_routed_jump() {
                return yulang_cps_abort_value_i64();
            }
            value = yulang_cps_consume_abort_i64();
        }
        _ => {}
    }
    let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    let initial = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);
    if frame_len == 0 {
        restore_pending_routed_return_frames_for_normal_return(initial);
    }
    let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    if frame_len <= initial {
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] return_i64: value={} frame_len={} initial={} action=noop",
                describe_native_i64_value(value),
                frame_len,
                initial
            );
        }
        return value;
    }
    // Pre-force v2 check.
    let is_thunk = NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&(value as usize)));
    let top_forces = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        frames
            .borrow()
            .last()
            .map(|frame| frame.immediately_forces_param)
            .unwrap_or(false)
    });
    if is_thunk && top_forces {
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] return_i64: value={} frame_len={} initial={} action=pre_force",
                describe_native_i64_value(value),
                frame_len,
                initial
            );
        }
        return yulang_cps_pre_force_top_frame_i64(value);
    }
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] return_i64: value={} frame_len={} initial={} action=continue",
            describe_native_i64_value(value),
            frame_len,
            initial
        );
    }
    yulang_cps_continue_return_frame_i64(value)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_selected_handler_env_or_i64(entry: i64, fallback: i64) -> i64 {
    let selected_handler = NATIVE_CPS_I64_SELECTED_HANDLER_ID.with(|handler| *handler.borrow());
    // ResumeWithHandler frames publish their handler env before the resumed
    // continuation runs and stay visible while it unwinds. Search newest first,
    // but only within the handler selected by `select_handler`: continuation
    // entry ids are local and can collide across independent mutable refs.
    if let Some(value) = NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| {
        siblings
            .borrow()
            .iter()
            .rev()
            .filter(|handler| handler.handler == selected_handler)
            .flat_map(|handler| handler.envs.iter().rev())
            .find(|env| env.entry == entry)
            .map(|env| env.env)
    }) {
        NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow_mut() = true);
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] selected_handler_env: entry={} fallback={} value={} source=rwh_sibling",
                entry,
                describe_native_i64_value(fallback),
                describe_native_i64_value(value)
            );
        }
        return value;
    }
    let value = NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| {
        envs.borrow()
            .iter()
            .rev()
            .find(|env| env.entry == entry)
            .map(|env| env.env)
            .unwrap_or(fallback)
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] selected_handler_env: entry={} fallback={} value={}",
            entry,
            describe_native_i64_value(fallback),
            describe_native_i64_value(value)
        );
    }
    value
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_selected_handler_owner_function_i64() -> i64 {
    NATIVE_CPS_I64_SELECTED_HANDLER_OWNER_FUNCTION_ID.with(|owner| *owner.borrow() as i64)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_thunk_i64_0(code: usize) -> usize {
    make_native_i64_thunk(code, Vec::new())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_thunk_i64_1(code: usize, a: i64) -> usize {
    make_native_i64_thunk(code, vec![a])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_thunk_i64_2(code: usize, a: i64, b: i64) -> usize {
    make_native_i64_thunk(code, vec![a, b])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_thunk_i64_3(code: usize, a: i64, b: i64, c: i64) -> usize {
    make_native_i64_thunk(code, vec![a, b, c])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_thunk_i64_4(
    code: usize,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> usize {
    make_native_i64_thunk(code, vec![a, b, c, d])
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_make_thunk_i64_many(
    code: usize,
    ptr: *const i64,
    len: i64,
) -> usize {
    make_native_i64_thunk(code, unsafe { native_i64_slice(ptr, len) })
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_is_thunk_i64(value: i64) -> i64 {
    if crate::mmtk_cps_control::is_mmtk_cps_control_thunk_value(value) {
        return 1;
    }
    usize::try_from(value)
        .ok()
        .is_some_and(|value| NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value)))
        .into()
}

enum NativeCpsI64ForceThunkStep {
    Next(usize),
    Return(i64),
}

fn force_native_i64_thunk_step(
    value: usize,
    code: NativeCpsI64ThunkEntry,
    env_ptr: *const i64,
    handlers: &NativeCpsI64HandlerSnapshot,
    guard_stack: &NativeCpsI64I64Snapshot,
    thunk_active_blocked: &[NativeCpsI64BlockedEffect],
) -> NativeCpsI64ForceThunkStep {
    if jit_trace_enabled() {
        let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().to_vec());
        let eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
        eprintln!(
            "[JIT-CPS] force_thunk: thunk={:#x} eval={} initial={} frames={}",
            value,
            eval.current_eval_id,
            eval.initial_frame_count,
            format_return_frames(&frames),
        );
    }
    // write27-e: Layer 2 (cps_repr.rs:1638-1681) uses
    // `if !active_handlers.is_empty() { active_handlers } else
    //  { thunk.handlers }` for the inner eval — i.e. the caller's
    // active handlers shadow the captured thunk handlers when the
    // caller has any. Previously the JIT appended thunk.handlers
    // onto the current stack (via
    // `native_i64_handler_stack_for_force`), which compounded the
    // synthetic PendingEnv frames every time a thunk got forced
    // inside another thunk. Use the caller stack as-is when it
    // has at least one frame; otherwise fall back to the thunk's
    // captured stack.
    let handlers = if NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().is_empty()) {
        Some(handlers.to_vec())
    } else {
        None
    };
    let guards = if NATIVE_CPS_I64_GUARD_STACK.with(|s| s.borrow().is_empty()) {
        Some(guard_stack.clone())
    } else {
        None
    };
    let mut active_blocked = NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| stack.borrow().clone());
    active_blocked.extend(thunk_active_blocked.iter().copied());
    let saved_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().to_vec());
    let consumed_start = NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| ids.borrow().len());
    let saved_eval_ctx = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
    let result =
        with_native_i64_cps_state_override_guard_snapshot(handlers, guards, active_blocked, || {
            code(env_ptr)
        });
    if native_i64_abort_should_consume_after_thunk_force() {
        return NativeCpsI64ForceThunkStep::Return(yulang_cps_consume_abort_i64());
    }
    let routed_frames = NATIVE_CPS_I64_RETURN_FRAMES_ROUTED
        .with(|routed| std::mem::take(&mut *routed.borrow_mut()));
    let active_abort = NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().clone());
    let active_scope_return = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active);
    let propagating_non_local = active_scope_return || active_abort.is_active();
    if propagating_non_local && (!routed_frames || active_scope_return) {
        let consumed_since = NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| {
            ids.borrow()
                .iter()
                .skip(consumed_start)
                .copied()
                .collect::<HashSet<_>>()
        });
        let restore_consumed = matches!(
            active_abort,
            NativeCpsI64Abort::Scoped {
                propagate_at_threshold: false,
                ..
            }
        ) || active_scope_return;
        let restored = if restore_consumed {
            saved_frames.clone()
        } else {
            saved_frames
                .clone()
                .into_iter()
                .filter(|frame| !consumed_since.contains(&frame.debug_id))
                .collect()
        };
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            frames.borrow_mut().replace(restored);
        });
    } else if !routed_frames {
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            let mut frames = frames.borrow_mut();
            let keep_len = frames
                .iter()
                .zip(saved_frames.iter())
                .take_while(|(current, saved)| current.debug_id == saved.debug_id)
                .count();
            frames.truncate(keep_len);
        });
    }
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = saved_eval_ctx);
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.active && slot.value == value as i64 {
            slot.value = result;
        }
    });
    if yulang_cps_abort_active_i64() != 0 || yulang_cps_scope_return_active_i64() != 0 {
        return NativeCpsI64ForceThunkStep::Return(result);
    }
    NativeCpsI64ForceThunkStep::Next(result as usize)
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_force_thunk_i64(value: usize) -> i64 {
    let _site = enter_native_cps_i64_stats_site(NativeCpsI64StatsSite::ForceThunk);
    with_native_cps_i64_stats(|stats| stats.force_thunk_calls += 1);
    let mut value = value;
    loop {
        let is_thunk = NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value));
        if !is_thunk {
            if crate::mmtk_cps_control::is_mmtk_cps_control_thunk_value(value as i64) {
                value =
                    crate::mmtk_cps_control::yulang_mmtk_cps_control_force_thunk_i64(value as i64)
                        as usize;
                continue;
            }
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] force_thunk.out: value={}",
                    describe_native_i64_value(value as i64)
                );
            }
            return value as i64;
        }
        let thunk = unsafe { &*(value as *const NativeCpsI64Thunk) };
        match force_native_i64_thunk_step(
            value,
            thunk.code,
            thunk.env.as_ptr(),
            &thunk.handlers,
            &thunk.guard_stack,
            &thunk.active_blocked,
        ) {
            NativeCpsI64ForceThunkStep::Next(next) => value = next,
            NativeCpsI64ForceThunkStep::Return(result) => return result,
        }
    }
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_force_thunk_context_i64(
    value: usize,
    context: usize,
    code: usize,
    env_ptr: *const i64,
) -> i64 {
    let context = unsafe { &*(context as *const NativeCpsI64ThunkContext) };
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64ThunkEntry>(code) };
    match force_native_i64_thunk_step(
        value,
        code,
        env_ptr,
        &context.handlers,
        &context.guard_stack,
        &context.active_blocked,
    ) {
        NativeCpsI64ForceThunkStep::Next(next) => yulang_cps_force_thunk_i64(next),
        NativeCpsI64ForceThunkStep::Return(result) => result,
    }
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_fresh_guard_i64() -> i64 {
    let id = NATIVE_CPS_I64_NEXT_GUARD.with(|next| {
        let mut next = next.borrow_mut();
        let id = *next;
        *next += 1;
        id
    });
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
        stack.borrow_mut().push(id);
    });
    id
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_peek_guard_i64() -> i64 {
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow().last().copied().unwrap_or(0))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn yulang_cps_find_guard_i64(id: i64) -> i64 {
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| i64::from(stack.borrow().contains(&id)))
}
