//! Private storage and public observation for collected constraint terms.
//!
//! A `Term` is an identity in one logical collection lineage.  The immutable
//! collected prefix is shared by batch aliases; solve-time additions live in a
//! sparse branch so one consumed alias never forces another to grow densely.

use std::{
    alloc::{Layout, alloc},
    collections::HashMap,
    mem::MaybeUninit,
    sync::{
        Arc,
        atomic::{AtomicU32, Ordering},
    },
};

#[cfg(test)]
use std::{cell::Cell, sync::atomic::AtomicUsize};

use yu_types::{ComponentKind, Leaf};

use crate::{ComponentId, F5bCapacityLane, reserve_f5b};

pub(crate) const TERM_PAGE_SLOTS: u32 = 256;
const TERM_PAGE_MASK: u32 = TERM_PAGE_SLOTS - 1;

static NEXT_TERM_ARENA_BRAND: AtomicU32 = AtomicU32::new(1);

#[cfg(test)]
thread_local! {
    static TEST_SEAL_COLLECTED_LEN: Cell<Option<u32>> = const { Cell::new(None) };
    static TEST_POST_GROWTH_FAILURE: Cell<Option<(usize, usize)>> = const { Cell::new(None) };
}

#[cfg(test)]
pub(crate) fn inject_post_growth_failure(physical_lane: usize, skip: usize) {
    TEST_POST_GROWTH_FAILURE.with(|target| target.set(Some((physical_lane, skip))));
}

#[cfg(test)]
pub(crate) fn post_growth_failure_pending() -> bool {
    TEST_POST_GROWTH_FAILURE.with(|target| target.get().is_some())
}

#[cfg(test)]
pub(crate) struct TestSealCollectedLengthOverride(Option<u32>);
#[cfg(test)]
impl Drop for TestSealCollectedLengthOverride {
    fn drop(&mut self) {
        TEST_SEAL_COLLECTED_LEN.with(|length| length.set(self.0));
    }
}

#[cfg(test)]
pub(crate) fn override_seal_collected_length(
    collected_len: u32,
) -> TestSealCollectedLengthOverride {
    let previous = TEST_SEAL_COLLECTED_LEN.with(|length| {
        let previous = length.get();
        length.set(Some(collected_len));
        previous
    });
    TestSealCollectedLengthOverride(previous)
}

/// An opaque, copyable address in a logical term-arena lineage.
///
/// ```compile_fail
/// use yu_solver::Term;
///
/// let _ = Term { index: 0 };
/// ```
///
/// ```compile_fail
/// use yu_solver::Term;
///
/// let term: Term = unimplemented!();
/// let _ = term.kind();
/// ```
///
/// ```compile_fail
/// use yu_solver::Term;
///
/// let _ = Term::Leaf;
/// let _ = Term::Component;
/// ```
///
/// ```compile_fail
/// use yu_solver::{ConstraintStore, Term, TermView};
///
/// fn cannot_extend_store<'a>(store: &'a ConstraintStore, term: Term) -> TermView<'static> {
///     store.term_view(term).unwrap()
/// }
/// ```
///
/// ```compile_fail
/// use yu_solver::ConstraintStore;
///
/// let _ = ConstraintStore::leaf_term;
/// let _ = ConstraintStore::component_term;
/// ```
///
/// ```
/// use std::{fmt::Debug, hash::Hash};
/// use yu_solver::Term;
///
/// fn exact_term_traits<T: Clone + Copy + Debug + Eq + Hash>() {}
/// exact_term_traits::<Term>();
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Term {
    brand: TermArenaBrand,
    index: u32,
}
#[cfg(test)]
impl Term {
    pub(crate) const fn test_index(self) -> u32 {
        self.index
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct TermArenaBrand(u32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TermLookupError {
    ArenaMismatch,
    InvalidHandle,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct LiveVariableView {
    kind: ComponentKind,
    polarity: Polarity,
    ordinal: u32,
}
impl LiveVariableView {
    pub const fn kind(self) -> ComponentKind {
        self.kind
    }
    pub const fn polarity(self) -> Polarity {
        self.polarity
    }
    pub const fn ordinal(self) -> u32 {
        self.ordinal
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Polarity {
    Positive,
    Negative,
}

/// One named structural child. Presence is retained through every row map.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RecordField<T> {
    pub name: Box<str>,
    pub optional: bool,
    pub value: T,
}
impl<T> RecordField<T> {
    pub(crate) fn required(name: impl Into<Box<str>>, value: T) -> Self {
        Self { name: name.into(), optional: false, value }
    }
    pub(crate) fn map<U>(&self, value: U) -> RecordField<U> {
        RecordField { name: self.name.clone(), optional: self.optional, value }
    }
}

/// An ordered tagged alternative. Arity is the payload count, including zero.
/// This carrier preserves alternatives verbatim; it does not merge domains or
/// certify that a whole case accepts a value.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct VariantAlternative<T> {
    pub tag: Box<str>,
    pub payloads: Box<[T]>,
}

/// Borrowed term observation remains exhaustively matchable without exposing a
/// constructor or interner for its opaque child handles.
///
/// ```
/// use yu_solver::TermView;
///
/// fn observe(view: TermView<'_>) {
///     match view {
///         TermView::Leaf(_) | TermView::Component(_) | TermView::LiveVariable(_) => {}
///         TermView::PositiveBottom | TermView::NegativeTop | TermView::NegativeBottom => {}
///         TermView::PositiveFunction { .. } | TermView::NegativeFunction { .. } => {}
///         TermView::PositiveTuple { .. } | TermView::NegativeTuple { .. } => {}
///         TermView::PositiveRecord { .. } | TermView::NegativeRecord { .. } => {}
///         TermView::PositiveVariant { .. } | TermView::NegativeVariant { .. } => {}
///     }
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TermView<'a> {
    Leaf(Leaf),
    Component(&'a ComponentId),
    LiveVariable(LiveVariableView),
    PositiveBottom,
    NegativeTop,
    NegativeBottom,
    PositiveFunction {
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    },
    NegativeFunction {
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    },
    PositiveVariant { alternatives: &'a [VariantAlternative<Term>] },
    NegativeVariant { alternatives: &'a [VariantAlternative<Term>] },
    PositiveRecord { fields: &'a [RecordField<Term>] },
    NegativeRecord { fields: &'a [RecordField<Term>] },
    PositiveTuple { elements: &'a [Term] },
    NegativeTuple { elements: &'a [Term] },
}

#[allow(
    dead_code,
    reason = "F5b exposes the approved observation algebra before F5d constructs live/function terms"
)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TermNode {
    Leaf(Leaf),
    Component(ComponentId),
    LiveVariable(LiveVariableView),
    PositiveBottom,
    NegativeTop,
    NegativeBottom,
    PositiveFunction {
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    },
    NegativeFunction {
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    },
    PositiveVariant { alternatives: Arc<[VariantAlternative<Term>]> },
    NegativeVariant { alternatives: Arc<[VariantAlternative<Term>]> },
    PositiveRecord { fields: Arc<[RecordField<Term>]> },
    NegativeRecord { fields: Arc<[RecordField<Term>]> },
    PositiveTuple { elements: Arc<[Term]> },
    NegativeTuple { elements: Arc<[Term]> },
}
impl TermNode {
    pub(crate) const fn kind(&self) -> ComponentKind {
        match self {
            Self::Leaf(leaf) => leaf.component_kind(),
            Self::Component(component) => component.kind(),
            Self::LiveVariable(view) => view.kind,
            Self::PositiveBottom | Self::NegativeTop | Self::NegativeBottom => ComponentKind::Value,
            // Function collection is a later F5 gate.  These variants exist
            // solely because the approved observation algebra already names
            // them; no F5b path constructs one.
            Self::PositiveFunction { .. } | Self::NegativeFunction { .. }
            | Self::PositiveVariant { .. } | Self::NegativeVariant { .. }
            | Self::PositiveTuple { .. } | Self::NegativeTuple { .. } | Self::PositiveRecord { .. } | Self::NegativeRecord { .. } => ComponentKind::Value,
        }
    }
    pub(crate) fn view(&self) -> TermView<'_> {
        match self {
            Self::Leaf(leaf) => TermView::Leaf(*leaf),
            Self::Component(component) => TermView::Component(component),
            Self::LiveVariable(view) => TermView::LiveVariable(*view),
            Self::PositiveBottom => TermView::PositiveBottom,
            Self::NegativeTop => TermView::NegativeTop,
            Self::NegativeBottom => TermView::NegativeBottom,
            Self::PositiveFunction {
                argument,
                argument_effect,
                result_effect,
                result,
            } => TermView::PositiveFunction {
                argument: *argument,
                argument_effect: *argument_effect,
                result_effect: *result_effect,
                result: *result,
            },
            Self::NegativeFunction {
                argument,
                argument_effect,
                result_effect,
                result,
            } => TermView::NegativeFunction {
                argument: *argument,
                argument_effect: *argument_effect,
                result_effect: *result_effect,
                result: *result,
            },
            Self::PositiveVariant { alternatives } => TermView::PositiveVariant { alternatives },
            Self::NegativeVariant { alternatives } => TermView::NegativeVariant { alternatives },
            Self::PositiveRecord { fields } => TermView::PositiveRecord { fields },
            Self::NegativeRecord { fields } => TermView::NegativeRecord { fields },
            Self::PositiveTuple { elements } => TermView::PositiveTuple { elements },
            Self::NegativeTuple { elements } => TermView::NegativeTuple { elements },
        }
    }
}

#[allow(
    dead_code,
    reason = "the shared postfix allocator is activated by later solve-time term families"
)]
#[derive(Debug)]
pub(crate) struct TermLineage {
    brand: TermArenaBrand,
    collected: Arc<[TermNode]>,
    first_postfix_page: u32,
    postfix_allocator: Arc<TermPostfixAllocator>,
}
impl TermLineage {
    fn node(&self, term: Term) -> Result<&TermNode, TermLookupError> {
        if term.brand != self.brand {
            return Err(TermLookupError::ArenaMismatch);
        }
        self.collected
            .get(term.index as usize)
            .ok_or(TermLookupError::InvalidHandle)
    }
}

/// Collection-only interning.  It is sealed before a batch becomes observable.
#[derive(Clone, Debug)]
pub(crate) struct TermBuilder {
    brand: TermArenaBrand,
    nodes: Vec<TermNode>,
    positions: HashMap<TermNode, Term>,
    /// Test-only retained builders and all batch aliases must use the exact
    /// same post-prefix allocator for a collection brand.
    postfix_allocator: Arc<TermPostfixAllocator>,
}
impl TermBuilder {
    pub(crate) fn new() -> Result<Self, crate::CollectionAvailabilityError> {
        #[allow(
            deprecated,
            reason = "retain compatibility with compilers predating Atomic::try_update"
        )]
        let brand = NEXT_TERM_ARENA_BRAND
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |brand| {
                brand.checked_add(1)
            })
            .map_err(|_| crate::CollectionAvailabilityError::ComponentIdentityExhausted)?;
        Ok(Self {
            brand: TermArenaBrand(brand),
            nodes: Vec::new(),
            positions: HashMap::new(),
            postfix_allocator: Arc::new(TermPostfixAllocator::new()),
        })
    }

    pub(crate) fn intern(
        &mut self,
        node: TermNode,
    ) -> Result<Term, crate::CollectionAvailabilityError> {
        if let Some(term) = self.positions.get(&node).copied() {
            return Ok(term);
        }
        let index = u32::try_from(self.nodes.len())
            .map_err(|_| crate::CollectionAvailabilityError::ComponentIdentityExhausted)?;
        let term = Term {
            brand: self.brand,
            index,
        };
        self.nodes.push(node.clone());
        self.positions.insert(node, term);
        Ok(term)
    }

    pub(crate) fn seal(self) -> Result<Arc<TermLineage>, crate::CollectionAvailabilityError> {
        let collected_len = u32::try_from(self.nodes.len())
            .map_err(|_| crate::CollectionAvailabilityError::ComponentIdentityExhausted)?;
        #[cfg(test)]
        let collected_len = TEST_SEAL_COLLECTED_LEN
            .with(|test_collected_len| test_collected_len.get())
            .unwrap_or(collected_len);
        let first_postfix_page = align_up(collected_len)?;
        Ok(Arc::new(TermLineage {
            brand: self.brand,
            collected: Arc::from(self.nodes),
            first_postfix_page,
            postfix_allocator: self.postfix_allocator.initialize(first_postfix_page),
        }))
    }
}

/// The sole checked page allocator for every branch and test-only retained
/// builder in one logical Term lineage.
#[derive(Debug)]
struct TermPostfixAllocator {
    next_postfix_page: AtomicU32,
    /// 0 is uninitialized, 1 is initializing, and 2 is initialized.  Keeping
    /// initialization separate lets page zero remain a valid aligned start.
    initialization: AtomicU32,
    #[cfg(test)]
    cas_attempts: AtomicUsize,
}
impl TermPostfixAllocator {
    fn new() -> Self {
        Self {
            next_postfix_page: AtomicU32::new(0),
            initialization: AtomicU32::new(0),
            #[cfg(test)]
            cas_attempts: AtomicUsize::new(0),
        }
    }

    fn initialize(self: &Arc<Self>, first_postfix_page: u32) -> Arc<Self> {
        match self
            .initialization
            .compare_exchange(0, 1, Ordering::AcqRel, Ordering::Acquire)
        {
            Ok(_) => {
                self.next_postfix_page
                    .store(first_postfix_page, Ordering::Release);
                self.initialization.store(2, Ordering::Release);
            }
            Err(1) => {
                while self.initialization.load(Ordering::Acquire) == 1 {
                    std::hint::spin_loop();
                }
            }
            Err(2) => {}
            Err(_) => unreachable!("Term postfix allocator has three states"),
        }
        // Test-only synthetic collection can extend an otherwise sealed batch.
        // No ordinary branch has allocated before that synthetic re-seal; the
        // floor prevents a new prefix from overlapping a later postfix page.
        let mut current = self.next_postfix_page.load(Ordering::Acquire);
        while current < first_postfix_page {
            match self.next_postfix_page.compare_exchange_weak(
                current,
                first_postfix_page,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => break,
                Err(observed) => current = observed,
            }
        }
        self.clone()
    }
}

fn align_up(length: u32) -> Result<u32, crate::CollectionAvailabilityError> {
    length
        .checked_add(TERM_PAGE_MASK)
        .map(|value| value & !TERM_PAGE_MASK)
        .ok_or(crate::CollectionAvailabilityError::ComponentIdentityExhausted)
}

#[derive(Debug)]
enum StructuralBacking {
    Variant(Arc<[VariantAlternative<Term>]>),
    Tuple(Arc<[Term]>),
    Record(Arc<[RecordField<Term>]>),
}
impl StructuralBacking {
    fn payload_bytes(&self) -> Option<usize> {
        match self {
            Self::Variant(alternatives) => alternatives.iter().try_fold(
                alternatives.len().checked_mul(std::mem::size_of::<VariantAlternative<Term>>())?,
                |bytes, alternative| bytes.checked_add(alternative.tag.len())?
                    .checked_add(alternative.payloads.len().checked_mul(std::mem::size_of::<Term>())?)),
            Self::Tuple(elements) => elements.len().checked_mul(std::mem::size_of::<Term>()),
            Self::Record(fields) => fields.iter().try_fold(
                fields.len().checked_mul(std::mem::size_of::<RecordField<Term>>())?,
                |bytes, field| bytes.checked_add(field.name.len())),
        }
    }
}

#[allow(
    dead_code,
    reason = "F5b branch allocation is exercised by private lifecycle tests; F5d owns production postfix terms"
)]
#[derive(Debug)]
pub(crate) struct BranchTermArena {
    lineage: Arc<TermLineage>,
    pages: Vec<TermPage>,
    page_positions: HashMap<u32, usize>,
    /// Solve-time terms are a branch-local, source-free extension of the
    /// immutable collected prefix.  Reusing an equal node is required for the
    /// typed pair memo to have one stable structural handle per branch.
    positions: HashMap<TermNode, Term>,
    route_journal: Option<BranchTermJournal>,
    route_journal_spare: Option<BranchTermJournal>,
    /// Owns variable-arity child payloads once; TermNode clones share them.
    structural_backings: Vec<StructuralBacking>,
    structural_payload_bytes: usize,
    capacity_events: TermCapacityEvents,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    owner_events: [TermOwnerEvent; 5],
    #[cfg(test)]
    lane_requests: [usize; 6],
    #[cfg(test)]
    lane_growths: [usize; 6],
    #[cfg(test)]
    journal_transfers: usize,
    #[cfg(test)]
    directory_probes: AtomicUsize,
}

/// Physical owners, in retained-byte order. Reserve-injection tags are not
/// lane identities: the map and journal reserves deliberately share tags.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TermCapacitySnapshot(
    pub(crate) [usize; 6],
    #[cfg(test)] pub(crate) TermLaneState,
    #[cfg(test)] pub(crate) TermOwnerLanes,
    pub(crate) usize,
);
impl TermCapacitySnapshot {
    pub(crate) const fn structural_storage_bytes(self) -> usize {
        #[cfg(test)]
        { self.3 }
        #[cfg(not(test))]
        { self.1 }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TermOwnerLanes {
    pub(crate) lengths: [usize; 6],
    pub(crate) requests: [usize; 6],
    pub(crate) growths: [usize; 6],
    pub(crate) capacities: [usize; 6],
    pub(crate) bytes: [usize; 6],
    pub(crate) active: bool,
    pub(crate) transfers: usize,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TermLaneState {
    pub(crate) lengths: [usize; 6],
    pub(crate) requests: [usize; 6],
    pub(crate) growths: [usize; 6],
    pub(crate) journal_active: bool,
    pub(crate) journal_transfers: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TermCapacityLane {
    PageDescriptors = 1,
    PagePositions = 2,
    Interner = 3,
    InternedJournal = 4,
    ClaimedPagesJournal = 5,
}

// One intern can reserve five existing owners, then record one Tuple payload.
const TERM_CAPACITY_EVENT_MAX: usize = 6;
#[derive(Debug)]
struct TermCapacityEvents {
    snapshots: [Option<TermCapacitySnapshot>; TERM_CAPACITY_EVENT_MAX],
    len: usize,
}
impl TermCapacityEvents {
    fn new() -> Self {
        Self {
            snapshots: [None; TERM_CAPACITY_EVENT_MAX],
            len: 0,
        }
    }
    fn push(&mut self, snapshot: TermCapacitySnapshot) {
        assert!(
            self.len < TERM_CAPACITY_EVENT_MAX,
            "Term constructor event bound"
        );
        self.snapshots[self.len] = Some(snapshot);
        self.len += 1;
    }
    fn take(&mut self) -> Self {
        std::mem::replace(self, Self::new())
    }
}

/// A bounded rollback point for solve-time terms.  The page descriptor
/// capacity is retained when a transaction is rolled back, but newly claimed
/// fixed-page backing is released, and the initialized prefix plus interning
/// directory return to the checkpoint.  The global postfix index is
/// intentionally monotonic; rolled-back handles are never reused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BranchTermCheckpoint {
    pages_len: usize,
    last_page_initialized: u16,
    structural_backings_len: usize,
    structural_payload_bytes: usize,
    #[cfg(test)]
    positions_len: usize,
    #[cfg(test)]
    page_positions_len: usize,
}

#[derive(Debug)]
struct BranchTermJournal {
    checkpoint: BranchTermCheckpoint,
    interned: Vec<TermNode>,
    claimed_pages: Vec<u32>,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Debug)]
struct TermOwnerEvent { id: usize, requested: usize, capacity: usize }

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl Drop for BranchTermArena {
    fn drop(&mut self) {
        let sizes = Self::independent_lane_sizes();
        drop(std::mem::take(&mut self.pages));
        self.release_owner_event(1, sizes[1]);
        drop(std::mem::take(&mut self.page_positions));
        self.release_owner_event(2, sizes[2]);
        drop(std::mem::take(&mut self.positions));
        self.release_owner_event(3, sizes[3]);
        drop(self.route_journal.take());
        drop(self.route_journal_spare.take());
        self.release_owner_event(4, sizes[4]);
        self.release_owner_event(5, sizes[5]);
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl TermOwnerEvent {
    fn new(lane: usize, size: usize) -> Self {
        Self { id: crate::f5c_draft_heap::new_term_owner(lane, 0, 0, size),
            requested: 0, capacity: 0 }
    }
    fn observe(&mut self, lane: usize, requested: usize, capacity: usize, size: usize) {
        crate::f5c_draft_heap::update_term_owner(self.id, lane, requested,
            self.requested, capacity, self.capacity, size);
        self.requested = requested;
        self.capacity = capacity;
    }
}

#[allow(
    dead_code,
    reason = "F5b fixed-page allocation is exercised by private lifecycle seams before F5d produces postfix terms"
)]
impl BranchTermArena {
    #[cfg(test)]
    pub(crate) const fn independent_lane_sizes() -> [usize; 6] {
        [
            std::mem::size_of::<[MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize]>(),
            std::mem::size_of::<TermPage>(),
            std::mem::size_of::<(u32, usize)>(),
            std::mem::size_of::<(TermNode, Term)>(),
            std::mem::size_of::<TermNode>(),
            1,
        ]
    }

    #[cfg(test)]
    pub(crate) fn independent_owner_lanes(&self) -> Option<TermOwnerLanes> {
        let journal = self
            .route_journal
            .as_ref()
            .or(self.route_journal_spare.as_ref());
        let tuple_storage = self.structural_backings.capacity()
            .checked_mul(std::mem::size_of::<StructuralBacking>())?
            .checked_add(self.structural_payload_bytes)?;
        let capacities = [
            self.pages.len(),
            self.pages.capacity(),
            self.page_positions.capacity(),
            self.positions.capacity(),
            journal.map_or(0, |owner| owner.interned.capacity()),
            journal.map_or(0, |owner| owner.claimed_pages.capacity())
                .checked_mul(std::mem::size_of::<u32>())?
                .checked_add(tuple_storage)?,
        ];
        let sizes = Self::independent_lane_sizes();
        let mut bytes = [0; 6];
        for index in 0..6 {
            bytes[index] = if index == 5 { capacities[index] } else { capacities[index].checked_mul(sizes[index])? };
        }
        Some(TermOwnerLanes {
            lengths: [
                self.pages.len(),
                self.pages.len(),
                self.page_positions.len(),
                self.positions.len(),
                journal.map_or(0, |owner| owner.interned.len()),
                journal.map_or(0, |owner| owner.claimed_pages.len()),
            ],
            requests: self.lane_requests,
            growths: self.lane_growths,
            capacities,
            bytes,
            active: self.route_journal.is_some(),
            transfers: self.journal_transfers,
        })
    }
    pub(crate) fn new(lineage: Arc<TermLineage>) -> Self {
        Self {
            lineage,
            pages: Vec::new(),
            page_positions: HashMap::new(),
            positions: HashMap::new(),
            route_journal: None,
            route_journal_spare: None,
            structural_backings: Vec::new(),
            structural_payload_bytes: 0,
            capacity_events: TermCapacityEvents::new(),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            owner_events: std::array::from_fn(|index| {
                let lane = index + 1;
                TermOwnerEvent::new(lane, Self::independent_lane_sizes()[lane])
            }),
            #[cfg(test)]
            lane_requests: [0; 6],
            #[cfg(test)]
            lane_growths: [0; 6],
            #[cfg(test)]
            journal_transfers: 0,
            #[cfg(test)]
            directory_probes: AtomicUsize::new(0),
        }
    }

    #[cfg(test)]
    pub(crate) fn checkpoint(&self) -> BranchTermCheckpoint {
        BranchTermCheckpoint {
            pages_len: self.pages.len(),
            last_page_initialized: self.pages.last().map_or(0, |page| page.initialized),
            structural_backings_len: self.structural_backings.len(),
            structural_payload_bytes: self.structural_payload_bytes,
            positions_len: self.positions.len(),
            page_positions_len: self.page_positions.len(),
        }
    }

    pub(crate) fn begin_route(&mut self) {
        assert!(
            self.route_journal.is_none(),
            "Term route transaction is not nested"
        );
        let mut journal = self
            .route_journal_spare
            .take()
            .unwrap_or(BranchTermJournal {
                checkpoint: BranchTermCheckpoint {
                    pages_len: 0,
                    last_page_initialized: 0,
                    structural_backings_len: 0,
                    structural_payload_bytes: 0,
                    #[cfg(test)]
                    positions_len: 0,
                    #[cfg(test)]
                    page_positions_len: 0,
                },
                interned: Vec::new(),
                claimed_pages: Vec::new(),
            });
        #[cfg(test)]
        {
            self.journal_transfers += 1;
        }
        journal.checkpoint = BranchTermCheckpoint {
            pages_len: self.pages.len(),
            last_page_initialized: self.pages.last().map_or(0, |page| page.initialized),
            structural_backings_len: self.structural_backings.len(),
            structural_payload_bytes: self.structural_payload_bytes,
            #[cfg(test)]
            positions_len: self.positions.len(),
            #[cfg(test)]
            page_positions_len: self.page_positions.len(),
        };
        journal.interned.clear();
        journal.claimed_pages.clear();
        self.route_journal = Some(journal);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner_events();
    }

    pub(crate) fn commit_route(&mut self) {
        let journal = self
            .route_journal
            .take()
            .expect("Term route transaction is active");
        self.route_journal_spare = Some(journal);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner_events();
        #[cfg(test)]
        {
            self.journal_transfers += 1;
        }
    }

    pub(crate) fn rollback_route(&mut self) {
        let mut journal = self
            .route_journal
            .take()
            .expect("Term route transaction is active");
        for node in journal.interned.iter().rev() {
            assert!(self.positions.remove(&node).is_some());
        }
        for base in journal.claimed_pages.iter().rev() {
            assert!(self.page_positions.remove(&base).is_some());
        }
        self.pages.truncate(journal.checkpoint.pages_len);
        if journal.checkpoint.pages_len != 0 {
            self.pages[journal.checkpoint.pages_len - 1]
                .truncate_to(journal.checkpoint.last_page_initialized);
        }
        journal.interned.clear();
        self.structural_backings.truncate(journal.checkpoint.structural_backings_len);
        self.structural_payload_bytes = journal.checkpoint.structural_payload_bytes;
        self.route_journal_spare = Some(journal);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner_events();
        #[cfg(test)]
        {
            self.journal_transfers += 1;
        }
    }

    pub(crate) fn lookup(&self, term: Term) -> Result<&TermNode, TermLookupError> {
        if term.brand != self.lineage.brand {
            return Err(TermLookupError::ArenaMismatch);
        }
        if let Some(node) = self.lineage.collected.get(term.index as usize) {
            return Ok(node);
        }
        if term.index < self.lineage.first_postfix_page {
            return Err(TermLookupError::InvalidHandle);
        }
        let base = term.index & !TERM_PAGE_MASK;
        let offset = (term.index & TERM_PAGE_MASK) as usize;
        #[cfg(test)]
        self.directory_probes.fetch_add(1, Ordering::Relaxed);
        let position = self
            .page_positions
            .get(&base)
            .copied()
            .ok_or(TermLookupError::InvalidHandle)?;
        self.pages
            .get(position)
            .and_then(|page| page.get(offset))
            .ok_or(TermLookupError::InvalidHandle)
    }

    pub(crate) fn term_view(&self, term: Term) -> Result<TermView<'_>, TermLookupError> {
        self.lookup(term).map(TermNode::view)
    }

    pub(crate) fn term_kind(&self, term: Term) -> Result<ComponentKind, TermLookupError> {
        self.lookup(term).map(TermNode::kind)
    }

    /// O(1) logical retained-byte observation for the branch-owned inference
    /// Term arena.  The fixed pages are counted by page descriptors, not by a
    /// traversal of initialized nodes.
    pub(crate) fn checked_retained_bytes(&self) -> Option<usize> {
        let snapshot = self.capacity_snapshot();
        Self::checked_capacity_bytes(snapshot.0)?.checked_add(snapshot.structural_storage_bytes())
    }

    pub(crate) fn capacity_snapshot(&self) -> TermCapacitySnapshot {
        let journal = self
            .route_journal
            .as_ref()
            .or(self.route_journal_spare.as_ref());
        TermCapacitySnapshot(
            [
                self.pages.len(),
                self.pages.capacity(),
                self.page_positions.capacity(),
                self.positions.capacity(),
                journal.map_or(0, |j| j.interned.capacity()),
                journal.map_or(0, |j| j.claimed_pages.capacity()),
            ],
            #[cfg(test)]
            TermLaneState {
                lengths: [
                    self.pages.len(),
                    self.pages.len(),
                    self.page_positions.len(),
                    self.positions.len(),
                    journal.map_or(0, |j| j.interned.len()),
                    journal.map_or(0, |j| j.claimed_pages.len()),
                ],
                requests: self.lane_requests,
                growths: self.lane_growths,
                journal_active: self.route_journal.is_some(),
                journal_transfers: self.journal_transfers,
            },
            #[cfg(test)]
            self.independent_owner_lanes()
                .expect("Term owner lanes fit usize"),
            self.structural_backings.capacity().checked_mul(std::mem::size_of::<StructuralBacking>())
                .and_then(|bytes| bytes.checked_add(self.structural_payload_bytes))
                .expect("structural backing bytes fit usize"),
        )
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn observe_owner_events(&mut self) {
        let owner = self.independent_owner_lanes().expect("term owner capacity fits");
        let sizes = Self::independent_lane_sizes();
        for lane in 1..6 {
            self.owner_events[lane - 1].observe(lane, owner.lengths[lane],
                owner.capacities[lane], sizes[lane]);
        }
    }
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn release_owner_event(&mut self, lane: usize, size: usize) {
        let owner = &mut self.owner_events[lane - 1];
        crate::f5c_draft_heap::release_term_owner(owner.id, lane, owner.capacity, size);
        owner.id = 0;
    }
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(crate) fn start_owner_events(&mut self) {
        let sizes = Self::independent_lane_sizes();
        for page in &mut self.pages {
            assert_eq!(page.owner_id.id, 0, "term page owner already traced");
            page.owner_id.id = crate::f5c_draft_heap::new_term_owner(0, 1, 1, sizes[0]);
        }
        let lanes = self.independent_owner_lanes().expect("term owner capacity fits");
        for lane in 1..6 {
            let owner = &mut self.owner_events[lane - 1];
            assert_eq!(owner.id, 0, "term vector owner already traced");
            owner.id = crate::f5c_draft_heap::new_term_owner(lane,
                lanes.lengths[lane], lanes.capacities[lane], sizes[lane]);
            owner.requested = lanes.lengths[lane];
            owner.capacity = lanes.capacities[lane];
        }
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(crate) fn transfer_owner_events_to_solved_store(&self) {
        let sizes = Self::independent_lane_sizes();
        for page in &self.pages {
            crate::f5c_draft_heap::transfer_term_owner(page.owner_id.id, 0, 1, 1, sizes[0]);
        }
        for (index, owner) in self.owner_events.iter().enumerate() {
            crate::f5c_draft_heap::transfer_term_owner(owner.id, index + 1,
                owner.requested, owner.capacity, sizes[index + 1]);
        }
    }

    pub(crate) fn take_capacity_events(
        &mut self,
    ) -> impl Iterator<Item = TermCapacitySnapshot> + use<> {
        self.capacity_events.take().snapshots.into_iter().flatten()
    }

    fn record_capacity_change(&mut self, before: TermCapacitySnapshot, lane: TermCapacityLane) {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner_events();
        let after = self.capacity_snapshot();
        if before.0[lane as usize] != after.0[lane as usize] {
            #[cfg(test)]
            if crate::incoming_sample_trace::in_attempt() {
                crate::incoming_sample_trace::event(
                    || "Term".into(),
                    || format!("{lane:?}"),
                    before.0[lane as usize],
                    after.0[lane as usize],
                );
            }
            #[cfg(test)]
            {
                self.lane_growths[lane as usize] += 1;
            }
            #[cfg(test)]
            let after = self.capacity_snapshot();
            self.capacity_events.push(after);
        }
    }

    #[cfg(test)]
    fn fail_after_growth(
        &self,
        before: TermCapacitySnapshot,
        lane: TermCapacityLane,
    ) -> Result<(), crate::ConstraintError> {
        if self.capacity_snapshot().0[lane as usize] == before.0[lane as usize] {
            return Ok(());
        }
        TEST_POST_GROWTH_FAILURE.with(|target| match target.get() {
            Some((wanted, skip)) if wanted == lane as usize && skip == 0 => {
                target.set(None);
                Err(crate::ConstraintError::IdentityExhausted)
            }
            Some((wanted, skip)) if wanted == lane as usize => {
                target.set(Some((wanted, skip - 1)));
                Ok(())
            }
            _ => Ok(()),
        })
    }

    pub(crate) fn checked_capacity_bytes(capacities: [usize; 6]) -> Option<usize> {
        capacities
            .into_iter()
            .zip([
                std::mem::size_of::<[MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize]>(),
                std::mem::size_of::<TermPage>(),
                std::mem::size_of::<(u32, usize)>(),
                std::mem::size_of::<(TermNode, Term)>(),
                std::mem::size_of::<TermNode>(),
                std::mem::size_of::<u32>(),
            ])
            .try_fold(0usize, |total, (capacity, size)| {
                total.checked_add(capacity.checked_mul(size)?)
            })
    }

    #[cfg(test)]
    pub(crate) fn checked_independent_capacity_bytes(capacities: [usize; 6]) -> Option<usize> {
        capacities
            .into_iter()
            .zip([
                std::mem::size_of::<[MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize]>(),
                std::mem::size_of::<TermPage>(),
                std::mem::size_of::<(u32, usize)>(),
                std::mem::size_of::<(TermNode, Term)>(),
                std::mem::size_of::<TermNode>(),
                1,
            ])
            .try_fold(0usize, |total, (capacity, size)| {
                total.checked_add(capacity.checked_mul(size)?)
            })
    }

    #[cfg(test)]
    pub(crate) fn checked_independent_retained_bytes(&self) -> Option<usize> {
        let fixed_page_bytes = self.pages.len().checked_mul(std::mem::size_of::<
            [MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize],
        >())?;
        let journal_bytes = self
            .route_journal
            .as_ref()
            .or(self.route_journal_spare.as_ref())
            .map_or(Some(0), |journal| {
                journal
                    .interned
                    .capacity()
                    .checked_mul(std::mem::size_of::<TermNode>())?
                    .checked_add(
                        journal
                            .claimed_pages
                            .capacity()
                            .checked_mul(std::mem::size_of::<u32>())?,
                    )
            })?;
        [
            fixed_page_bytes,
            self.pages
                .capacity()
                .checked_mul(std::mem::size_of::<TermPage>())?,
            self.page_positions
                .capacity()
                .checked_mul(std::mem::size_of::<(u32, usize)>())?,
            self.positions
                .capacity()
                .checked_mul(std::mem::size_of::<(TermNode, Term)>())?,
            journal_bytes,
            self.structural_backings.capacity().checked_mul(std::mem::size_of::<StructuralBacking>())?,
            self.structural_payload_bytes,
        ]
        .into_iter()
        .try_fold(0usize, usize::checked_add)
    }

    /// Allocate only a page needed by this branch.  Descriptor and directory
    /// reservations precede the checked page claim, so ordinary allocation
    /// failure cannot consume a lineage index.
    pub(crate) fn push(&mut self, node: TermNode) -> Result<Term, crate::ConstraintError> {
        let needs_page = self
            .pages
            .last()
            .is_none_or(|page| page.initialized == TERM_PAGE_SLOTS as u16);
        if needs_page {
            #[cfg(test)]
            {
                self.lane_requests[1] += 1;
            }
            let before = self.capacity_snapshot();
            let result = reserve_f5b(&mut self.pages, 1, F5bCapacityLane::TermPages);
            self.record_capacity_change(before, TermCapacityLane::PageDescriptors);
            result?;
            #[cfg(test)]
            {
                self.lane_requests[2] += 1;
            }
            let before = self.capacity_snapshot();
            let result = reserve_f5b(
                &mut self.page_positions,
                1,
                F5bCapacityLane::TermPagePositions,
            );
            self.record_capacity_change(before, TermCapacityLane::PagePositions);
            result?;
            #[cfg(test)]
            {
                if self.route_journal.is_some() {
                    self.lane_requests[5] += 1;
                }
            }
            let before = self.capacity_snapshot();
            if let Some(journal) = &mut self.route_journal {
                let result = reserve_f5b(
                    &mut journal.claimed_pages,
                    1,
                    F5bCapacityLane::TermPagePositions,
                );
                self.record_capacity_change(before, TermCapacityLane::ClaimedPagesJournal);
                result?;
                #[cfg(test)]
                self.fail_after_growth(before, TermCapacityLane::ClaimedPagesJournal)?;
            }
            let mut page =
                TermPage::try_new().map_err(|_| crate::ConstraintError::IdentityExhausted)?;
            let base = self.claim_page()?;
            let position = self.pages.len();
            let previous = self.page_positions.insert(base, position);
            debug_assert!(previous.is_none(), "a claimed page base is never reused");
            page.base = base;
            self.pages.push(page);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.observe_owner_events();
            #[cfg(test)]
            {
                self.lane_requests[0] += 1;
                self.lane_growths[0] += 1;
            }
            #[cfg(test)]
            if crate::incoming_sample_trace::in_attempt() {
                crate::incoming_sample_trace::event(
                    || "Term".into(),
                    || "PageBacking".into(),
                    before.0[0],
                    self.capacity_snapshot().0[0],
                );
            }
            self.capacity_events.push(self.capacity_snapshot());
            if let Some(journal) = &mut self.route_journal {
                journal.claimed_pages.push(base);
            }
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.observe_owner_events();
        }
        let page = self.pages.last_mut().expect("new branch page is available");
        let index = page.push(node);
        Ok(Term {
            brand: self.lineage.brand,
            index,
        })
    }

    pub(crate) fn intern(&mut self, node: TermNode) -> Result<Term, crate::ConstraintError> {
        if let Some(term) = self.positions.get(&node).copied() {
            return Ok(term);
        }
        // The dedup directory is part of publication.  Reserve it before a
        // page can be claimed so a failed map growth cannot leave a committed
        // node which a later equal request fails to observe.
        #[cfg(test)]
        {
            self.lane_requests[3] += 1;
        }
        let before = self.capacity_snapshot();
        let result = reserve_f5b(&mut self.positions, 1, F5bCapacityLane::TermInterner);
        self.record_capacity_change(before, TermCapacityLane::Interner);
        result?;
        #[cfg(test)]
        {
            if self.route_journal.is_some() {
                self.lane_requests[4] += 1;
            }
        }
        let before = self.capacity_snapshot();
        if let Some(journal) = &mut self.route_journal {
            let result = reserve_f5b(&mut journal.interned, 1, F5bCapacityLane::TermInterner);
            self.record_capacity_change(before, TermCapacityLane::InternedJournal);
            result?;
            #[cfg(test)]
            self.fail_after_growth(before, TermCapacityLane::InternedJournal)?;
        }
        let term = self.push(node.clone())?;
        self.positions.insert(node.clone(), term);
        if let Some(journal) = &mut self.route_journal {
            journal.interned.push(node);
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner_events();
        Ok(term)
    }

    pub(crate) fn live_variable(
        &mut self,
        kind: ComponentKind,
        polarity: Polarity,
        ordinal: u32,
    ) -> Result<Term, crate::ConstraintError> {
        self.intern(TermNode::LiveVariable(LiveVariableView {
            kind,
            polarity,
            ordinal,
        }))
    }

    pub(crate) fn positive_bottom(&mut self) -> Result<Term, crate::ConstraintError> {
        self.intern(TermNode::PositiveBottom)
    }

    pub(crate) fn negative_top(&mut self) -> Result<Term, crate::ConstraintError> {
        self.intern(TermNode::NegativeTop)
    }

    pub(crate) fn negative_bottom(&mut self) -> Result<Term, crate::ConstraintError> {
        self.intern(TermNode::NegativeBottom)
    }

    pub(crate) fn positive_function(
        &mut self,
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    ) -> Result<Term, crate::ConstraintError> {
        self.require_function_children([
            (argument, ComponentKind::Value, Polarity::Negative),
            (argument_effect, ComponentKind::Effect, Polarity::Negative),
            (result_effect, ComponentKind::Effect, Polarity::Positive),
            (result, ComponentKind::Value, Polarity::Positive),
        ])?;
        self.intern(TermNode::PositiveFunction {
            argument,
            argument_effect,
            result_effect,
            result,
        })
    }

    pub(crate) fn negative_function(
        &mut self,
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    ) -> Result<Term, crate::ConstraintError> {
        self.require_function_children([
            (argument, ComponentKind::Value, Polarity::Positive),
            (argument_effect, ComponentKind::Effect, Polarity::Positive),
            (result_effect, ComponentKind::Effect, Polarity::Negative),
            (result, ComponentKind::Value, Polarity::Negative),
        ])?;
        self.intern(TermNode::NegativeFunction {
            argument,
            argument_effect,
            result_effect,
            result,
        })
    }

    pub(crate) fn positive_tuple(&mut self, elements: &[Term]) -> Result<Term, crate::ConstraintError> {
        self.require_tuple_children(elements, Polarity::Positive)?;
        self.intern_tuple(elements, true)
    }

    pub(crate) fn negative_tuple(&mut self, elements: &[Term]) -> Result<Term, crate::ConstraintError> {
        self.require_tuple_children(elements, Polarity::Negative)?;
        self.intern_tuple(elements, false)
    }

    fn require_tuple_children(&self, elements: &[Term], polarity: Polarity) -> Result<(), crate::ConstraintError> {
        if elements.is_empty() {
            return Err(crate::ConstraintError::ArtifactMismatch);
        }
        for &term in elements {
            let node = self.lookup(term).map_err(|_| crate::ConstraintError::ArtifactMismatch)?;
            if !matches_endpoint(node, ComponentKind::Value, polarity) {
                return Err(crate::ConstraintError::ArtifactMismatch);
            }
        }
        Ok(())
    }

    fn intern_tuple(&mut self, elements: &[Term], positive: bool) -> Result<Term, crate::ConstraintError> {
        let mut owned = Vec::new();
        owned.try_reserve_exact(elements.len()).map_err(|_| crate::ConstraintError::IdentityExhausted)?;
        owned.extend_from_slice(elements);
        let backing: Arc<[Term]> = Arc::from(owned);
        let node = if positive { TermNode::PositiveTuple { elements: backing.clone() } }
            else { TermNode::NegativeTuple { elements: backing.clone() } };
        self.intern_structure(node, StructuralBacking::Tuple(backing))
    }

    pub(crate) fn positive_variant(&mut self, alternatives: &[VariantAlternative<Term>]) -> Result<Term, crate::ConstraintError> {
        self.variant(alternatives, Polarity::Positive)
    }
    pub(crate) fn negative_variant(&mut self, alternatives: &[VariantAlternative<Term>]) -> Result<Term, crate::ConstraintError> {
        self.variant(alternatives, Polarity::Negative)
    }
    fn variant(&mut self, alternatives: &[VariantAlternative<Term>], polarity: Polarity) -> Result<Term, crate::ConstraintError> {
        // Empty families have no construction owner yet; bare tags are instead
        // nonempty families with one zero-payload alternative.
        if alternatives.is_empty() { return Err(crate::ConstraintError::ArtifactMismatch); }
        for alternative in alternatives {
            for &child in &alternative.payloads {
                let node = self.lookup(child).map_err(|_| crate::ConstraintError::ArtifactMismatch)?;
                if !matches_endpoint(node, ComponentKind::Value, polarity) {
                    return Err(crate::ConstraintError::ArtifactMismatch);
                }
            }
        }
        let mut owned = Vec::new();
        owned.try_reserve_exact(alternatives.len()).map_err(|_| crate::ConstraintError::IdentityExhausted)?;
        owned.extend(alternatives.iter().cloned());
        let alternatives: Arc<[VariantAlternative<Term>]> = Arc::from(owned);
        let node = match polarity {
            Polarity::Positive => TermNode::PositiveVariant { alternatives: alternatives.clone() },
            Polarity::Negative => TermNode::NegativeVariant { alternatives: alternatives.clone() },
        };
        self.intern_structure(node, StructuralBacking::Variant(alternatives))
    }

    pub(crate) fn positive_record(&mut self, fields: &[RecordField<Term>]) -> Result<Term, crate::ConstraintError> {
        self.record(fields, Polarity::Positive)
    }
    pub(crate) fn negative_record(&mut self, fields: &[RecordField<Term>]) -> Result<Term, crate::ConstraintError> {
        self.record(fields, Polarity::Negative)
    }
    fn record(&mut self, fields: &[RecordField<Term>], polarity: Polarity) -> Result<Term, crate::ConstraintError> {
        for field in fields {
            let node = self.lookup(field.value).map_err(|_| crate::ConstraintError::ArtifactMismatch)?;
            if !matches_endpoint(node, ComponentKind::Value, polarity) {
                return Err(crate::ConstraintError::ArtifactMismatch);
            }
        }
        let mut owned = Vec::new();
        owned.try_reserve_exact(fields.len()).map_err(|_| crate::ConstraintError::IdentityExhausted)?;
        owned.extend(fields.iter().cloned());
        let fields: Arc<[RecordField<Term>]> = Arc::from(owned);
        let node = match polarity {
            Polarity::Positive => TermNode::PositiveRecord { fields: fields.clone() },
            Polarity::Negative => TermNode::NegativeRecord { fields: fields.clone() },
        };
        self.intern_structure(node, StructuralBacking::Record(fields))
    }

    fn intern_structure(&mut self, node: TermNode, backing: StructuralBacking) -> Result<Term, crate::ConstraintError> {
        if let Some(term) = self.positions.get(&node).copied() { return Ok(term); }
        let payload_bytes = backing.payload_bytes()
            .and_then(|bytes| self.structural_payload_bytes.checked_add(bytes))
            .ok_or(crate::ConstraintError::IdentityExhausted)?;
        let backing_capacity = self.structural_backings.capacity();
        self.structural_backings.try_reserve(1).map_err(|_| crate::ConstraintError::IdentityExhausted)?;
        let term = match self.intern(node) {
            Ok(term) => term,
            Err(error) => {
                // A failed first interner reserve may have no event of its own,
                // but the preceding structural-owner growth is still retained.
                if self.structural_backings.capacity() != backing_capacity {
                    self.capacity_events.push(self.capacity_snapshot());
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    self.observe_owner_events();
                }
                return Err(error);
            }
        };
        self.structural_backings.push(backing);
        self.structural_payload_bytes = payload_bytes;
        self.capacity_events.push(self.capacity_snapshot());
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner_events();
        Ok(term)
    }

    /// Function construction is the sole post-prefix structural constructor.
    /// Validate lineage, kind, and polarity before `intern` can reserve or
    /// publish a node.  The existing artifact error is the boundary for a
    /// foreign, absent, or ill-polarized private handle.
    fn require_function_children(
        &self,
        children: [(Term, ComponentKind, Polarity); 4],
    ) -> Result<(), crate::ConstraintError> {
        for (term, kind, polarity) in children {
            let node = self
                .lookup(term)
                .map_err(|_| crate::ConstraintError::ArtifactMismatch)?;
            if !matches_endpoint(node, kind, polarity) {
                return Err(crate::ConstraintError::ArtifactMismatch);
            }
        }
        Ok(())
    }

    fn claim_page(&self) -> Result<u32, crate::ConstraintError> {
        let allocator = &self.lineage.postfix_allocator;
        let mut current = allocator.next_postfix_page.load(Ordering::Relaxed);
        loop {
            let next = current
                .checked_add(TERM_PAGE_SLOTS)
                .ok_or(crate::ConstraintError::IdentityExhausted)?;
            #[cfg(test)]
            allocator.cas_attempts.fetch_add(1, Ordering::Relaxed);
            match allocator.next_postfix_page.compare_exchange_weak(
                current,
                next,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Ok(current),
                Err(observed) => current = observed,
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn observations(&self) -> TermPageObservations {
        let claims = self.pages.len();
        let committed_nodes = self
            .pages
            .iter()
            .map(|page| page.initialized as usize)
            .sum::<usize>();
        TermPageObservations {
            claims,
            reserved_slots: claims * TERM_PAGE_SLOTS as usize,
            committed_nodes,
            directory_probes: self.directory_probes.load(Ordering::Relaxed),
            alignment_gap: (self.lineage.first_postfix_page as usize)
                .saturating_sub(self.lineage.collected.len()),
            slack_slots: claims * TERM_PAGE_SLOTS as usize - committed_nodes,
            cas_attempts: self
                .lineage
                .postfix_allocator
                .cas_attempts
                .load(Ordering::Relaxed),
        }
    }
}

fn matches_endpoint(node: &TermNode, kind: ComponentKind, polarity: Polarity) -> bool {
    match (kind, polarity, node) {
        (ComponentKind::Value, Polarity::Positive, TermNode::Leaf(Leaf::IntPositive | Leaf::UnitPositive | Leaf::BoolPositive | Leaf::StrPositive))
        | (ComponentKind::Value, Polarity::Positive, TermNode::PositiveBottom)
        | (ComponentKind::Value, Polarity::Positive, TermNode::PositiveTuple { .. })
        | (ComponentKind::Value, Polarity::Positive, TermNode::PositiveVariant { .. })
        | (ComponentKind::Value, Polarity::Negative, TermNode::NegativeVariant { .. })
        | (ComponentKind::Value, Polarity::Positive, TermNode::PositiveRecord { .. })
        | (ComponentKind::Value, Polarity::Negative, TermNode::NegativeRecord { .. })
        | (ComponentKind::Value, Polarity::Negative, TermNode::Leaf(Leaf::IntNegative | Leaf::UnitNegative | Leaf::BoolNegative | Leaf::StrNegative))
        | (ComponentKind::Value, Polarity::Negative, TermNode::NegativeTop)
        | (ComponentKind::Value, Polarity::Negative, TermNode::NegativeBottom)
        | (ComponentKind::Value, Polarity::Negative, TermNode::NegativeTuple { .. })
        | (ComponentKind::Effect, Polarity::Positive, TermNode::Leaf(Leaf::EffectBottomPositive))
        | (ComponentKind::Effect, Polarity::Negative, TermNode::Leaf(Leaf::EmptyEffectNegative)) => {
            true
        }
        (
            _,
            _,
            TermNode::LiveVariable(LiveVariableView {
                kind: node_kind,
                polarity: node_polarity,
                ..
            }),
        ) if *node_kind == kind && *node_polarity == polarity => true,
        (ComponentKind::Value, Polarity::Positive, TermNode::PositiveFunction { .. })
        | (ComponentKind::Value, Polarity::Negative, TermNode::NegativeFunction { .. }) => true,
        _ => false,
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TermPageObservations {
    pub(crate) claims: usize,
    pub(crate) reserved_slots: usize,
    pub(crate) committed_nodes: usize,
    pub(crate) directory_probes: usize,
    pub(crate) alignment_gap: usize,
    pub(crate) slack_slots: usize,
    pub(crate) cas_attempts: usize,
}

#[allow(
    dead_code,
    reason = "fixed-page identity is consumed by the branch allocator"
)]
#[derive(Debug)]
struct TermPage {
    base: u32,
    initialized: u16,
    nodes: Box<[MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize]>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    owner_id: TermPageOwnerEvent,
}
#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Debug)]
struct TermPageOwnerEvent {
    id: usize,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl Drop for TermPageOwnerEvent {
    fn drop(&mut self) {
        if self.id != 0 {
            crate::f5c_draft_heap::release_term_owner(self.id, 0, 1,
                std::mem::size_of::<[MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize]>());
        }
    }
}
#[allow(
    dead_code,
    reason = "fixed pages are allocated only by the branch allocator"
)]
impl TermPage {
    fn try_new() -> Result<Self, ()> {
        let layout = Layout::new::<[MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize]>();
        // The global allocator is used directly because a fixed, exact 256-slot
        // backing array must report allocation failure rather than aborting.
        let pointer =
            unsafe { alloc(layout) } as *mut [MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize];
        if pointer.is_null() {
            return Err(());
        }
        Ok(Self {
            base: 0,
            initialized: 0,
            // `pointer` was allocated for this exact array layout immediately
            // above and every element is `MaybeUninit`, so uninitialized bytes
            // are valid until `push` initializes their prefix.
            nodes: unsafe { Box::from_raw(pointer) },
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            owner_id: TermPageOwnerEvent {
                id: crate::f5c_draft_heap::new_term_owner(0, 1, 1, layout.size()),
            },
        })
    }

    fn push(&mut self, node: TermNode) -> u32 {
        let offset = self.initialized as usize;
        debug_assert!(offset < TERM_PAGE_SLOTS as usize);
        self.nodes[offset].write(node);
        self.initialized += 1;
        self.base + offset as u32
    }

    fn truncate_to(&mut self, initialized: u16) {
        debug_assert!(initialized <= self.initialized);
        let old_initialized = self.initialized;
        for node in &mut self.nodes[initialized as usize..old_initialized as usize] {
            unsafe { node.assume_init_drop() };
        }
        self.initialized = initialized;
    }

    fn get(&self, offset: usize) -> Option<&TermNode> {
        (offset < self.initialized as usize).then(|| {
            // The initialized-prefix invariant is established only by `push`.
            unsafe { self.nodes[offset].assume_init_ref() }
        })
    }
}
impl Drop for TermPage {
    fn drop(&mut self) {
        for node in &mut self.nodes[..self.initialized as usize] {
            // Exactly this prefix was written by `push`; the remainder stays
            // uninitialized and must not be dropped.
            unsafe { node.assume_init_drop() };
        }
    }
}

pub(crate) fn view_prefix(
    lineage: &TermLineage,
    term: Term,
) -> Result<TermView<'_>, TermLookupError> {
    lineage.node(term).map(TermNode::view)
}

pub(crate) fn kind_prefix(
    lineage: &TermLineage,
    term: Term,
) -> Result<ComponentKind, TermLookupError> {
    lineage.node(term).map(TermNode::kind)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn live(ordinal: u32) -> TermNode {
        TermNode::LiveVariable(LiveVariableView {
            kind: ComponentKind::Value,
            polarity: Polarity::Positive,
            ordinal,
        })
    }

    #[test]
    fn fixed_pages_keep_prefix_and_sibling_branches_sparse() {
        for (prefix, expected_first_page, expected_gap) in
            [(255, 256, 1), (256, 256, 0), (257, 512, 255)]
        {
            let mut builder = TermBuilder::new().unwrap();
            for ordinal in 0..prefix {
                builder.intern(live(ordinal)).unwrap();
            }
            let lineage = builder.seal().unwrap();
            assert_eq!(lineage.collected.len(), prefix as usize);
            assert_eq!(lineage.first_postfix_page, expected_first_page);

            let branch = BranchTermArena::new(lineage);
            assert_eq!(branch.observations().alignment_gap, expected_gap);
        }

        let mut builder = TermBuilder::new().unwrap();
        for ordinal in 0..257 {
            builder.intern(live(ordinal)).unwrap();
        }
        let lineage = builder.seal().unwrap();

        let mut first = BranchTermArena::new(lineage.clone());
        let mut second = BranchTermArena::new(lineage.clone());
        let first_term = first.push(live(300)).unwrap();
        for ordinal in 0..257 {
            second.push(live(400 + ordinal)).unwrap();
        }
        assert_eq!(first.pages.len(), 1);
        assert_eq!(second.pages.len(), 2);
        assert!(matches!(
            first.term_view(first_term),
            Ok(TermView::LiveVariable(_))
        ));
        assert_eq!(
            second.term_view(first_term),
            Err(TermLookupError::InvalidHandle)
        );

        let other_lineage = TermBuilder::new().unwrap().seal().unwrap();
        let other = BranchTermArena::new(other_lineage);
        assert_eq!(
            other.term_view(first_term),
            Err(TermLookupError::ArenaMismatch)
        );
        assert_eq!(first.pages[0].initialized, 1);
        assert_eq!(second.pages[0].initialized, TERM_PAGE_SLOTS as u16);
        assert_eq!(second.pages[1].initialized, 1);
        assert_eq!(first.observations().claims, 1);
        assert_eq!(first.observations().reserved_slots, 256);
        assert_eq!(first.observations().committed_nodes, 1);
        assert_eq!(first.observations().slack_slots, 255);
        assert!(first.observations().directory_probes >= 1);
        assert!(first.observations().cas_attempts >= 3);
    }

    #[test]
    fn page_lifecycle_has_exact_boundary_cases_and_exhaustion() {
        for (count, pages, slack) in [(1, 1, 255), (256, 1, 0), (257, 2, 255), (513, 3, 255)] {
            let lineage = TermBuilder::new().unwrap().seal().unwrap();
            let mut branch = BranchTermArena::new(lineage);
            for ordinal in 0..count {
                branch.push(live(ordinal)).unwrap();
            }
            let observed = branch.observations();
            assert_eq!(observed.claims, pages);
            assert_eq!(observed.reserved_slots, TERM_PAGE_SLOTS as usize * pages);
            assert_eq!(observed.committed_nodes, count as usize);
            assert_eq!(observed.slack_slots, slack as usize);
            assert!(observed.cas_attempts >= pages);
        }
        assert_eq!(align_up(255), Ok(256));
        assert_eq!(align_up(256), Ok(256));
        assert_eq!(align_up(257), Ok(512));
        assert_eq!(
            align_up(u32::MAX - TERM_PAGE_MASK),
            Ok(u32::MAX - TERM_PAGE_MASK)
        );
        assert_eq!(
            align_up(u32::MAX),
            Err(crate::CollectionAvailabilityError::ComponentIdentityExhausted)
        );
        let page = TermPage::try_new().unwrap();
        assert_eq!(page.nodes.len(), TERM_PAGE_SLOTS as usize);

        let lineage = TermBuilder::new().unwrap().seal().unwrap();
        lineage
            .postfix_allocator
            .next_postfix_page
            .store(u32::MAX - TERM_PAGE_MASK, Ordering::Relaxed);
        let mut branch = BranchTermArena::new(lineage);
        assert_eq!(
            branch.push(live(0)),
            Err(crate::ConstraintError::IdentityExhausted)
        );
        assert_eq!(branch.observations().claims, 0);
        assert_eq!(branch.observations().committed_nodes, 0);
    }

    #[test]
    fn retained_test_builders_share_one_postfix_allocator() {
        let mut builder = TermBuilder::new().unwrap();
        builder.intern(live(0)).unwrap();
        let retained = builder.clone();
        let first = builder.seal().unwrap();
        let second = retained.seal().unwrap();
        assert!(Arc::ptr_eq(
            &first.postfix_allocator,
            &second.postfix_allocator
        ));

        let mut first_branch = BranchTermArena::new(first);
        let mut second_branch = BranchTermArena::new(second);
        let first_term = first_branch.push(live(1)).unwrap();
        let second_term = second_branch.push(live(2)).unwrap();
        assert_ne!(first_term, second_term);
        assert_eq!(
            first_branch.lookup(second_term),
            Err(TermLookupError::InvalidHandle)
        );
        assert_eq!(
            second_branch.lookup(first_term),
            Err(TermLookupError::InvalidHandle)
        );
    }

    #[test]
    fn live_and_function_interning_are_idempotent_and_reject_children_before_publication() {
        let lineage = TermBuilder::new().unwrap().seal().unwrap();
        let mut branch = BranchTermArena::new(lineage.clone());
        let argument = branch
            .live_variable(ComponentKind::Value, Polarity::Negative, 7)
            .unwrap();
        assert_eq!(
            argument,
            branch
                .live_variable(ComponentKind::Value, Polarity::Negative, 7)
                .unwrap()
        );
        let argument_effect = branch
            .live_variable(ComponentKind::Effect, Polarity::Negative, 8)
            .unwrap();
        let result_effect = branch
            .live_variable(ComponentKind::Effect, Polarity::Positive, 8)
            .unwrap();
        let result = branch
            .live_variable(ComponentKind::Value, Polarity::Positive, 7)
            .unwrap();
        let function = branch
            .positive_function(argument, argument_effect, result_effect, result)
            .unwrap();
        assert_eq!(
            function,
            branch
                .positive_function(argument, argument_effect, result_effect, result)
                .unwrap()
        );
        let before = branch.observations().committed_nodes;
        let mut foreign = BranchTermArena::new(TermBuilder::new().unwrap().seal().unwrap());
        let foreign_argument = foreign
            .live_variable(ComponentKind::Value, Polarity::Negative, 7)
            .unwrap();
        assert_eq!(
            branch.positive_function(foreign_argument, argument_effect, result_effect, result),
            Err(crate::ConstraintError::ArtifactMismatch)
        );
        assert_eq!(
            branch.positive_function(argument_effect, argument_effect, result_effect, result),
            Err(crate::ConstraintError::ArtifactMismatch)
        );
        assert_eq!(
            branch.positive_function(result, argument_effect, result_effect, result),
            Err(crate::ConstraintError::ArtifactMismatch)
        );
        assert_eq!(branch.observations().committed_nodes, before);

        let sibling = BranchTermArena::new(lineage);
        assert_eq!(
            sibling.term_view(function),
            Err(TermLookupError::InvalidHandle)
        );
        assert!(matches!(
            branch.term_view(function),
            Ok(TermView::PositiveFunction { .. })
        ));
    }

    #[test]
    fn variant_terms_preserve_tag_arity_aliases_polarity_and_storage() {
        let lineage = TermBuilder::new().unwrap().seal().unwrap();
        let mut branch = BranchTermArena::new(lineage.clone());
        let child = branch.live_variable(ComponentKind::Value, Polarity::Positive, 0).unwrap();
        branch.take_capacity_events().count();
        let negative = branch.live_variable(ComponentKind::Value, Polarity::Negative, 0).unwrap();
        branch.take_capacity_events().count();
        let unit = branch.intern(TermNode::Leaf(Leaf::UnitPositive)).unwrap();
        branch.take_capacity_events().count();
        let alternatives = [
            VariantAlternative { tag: "empty".into(), payloads: Box::new([]) },
            VariantAlternative { tag: "empty".into(), payloads: Box::new([unit]) },
            VariantAlternative { tag: "pair".into(), payloads: Box::new([child, child]) },
        ];
        let before_bytes = branch.structural_payload_bytes;
        let term = branch.positive_variant(&alternatives).unwrap();
        branch.take_capacity_events().count();
        assert_eq!(branch.term_view(term).unwrap(), TermView::PositiveVariant { alternatives: &alternatives });
        assert_eq!(branch.positive_variant(&alternatives).unwrap(), term);
        assert_eq!(branch.structural_payload_bytes - before_bytes,
            3 * std::mem::size_of::<VariantAlternative<Term>>() + 14 + 3 * std::mem::size_of::<Term>());
        let negative_alternatives = [VariantAlternative { tag: "pair".into(), payloads: Box::new([negative, negative]) }];
        let neg = branch.negative_variant(&negative_alternatives).unwrap();
        branch.take_capacity_events().count();
        assert_eq!(branch.term_view(neg).unwrap(), TermView::NegativeVariant { alternatives: &negative_alternatives });
        let before = branch.observations().committed_nodes;
        assert_eq!(branch.positive_variant(&negative_alternatives), Err(crate::ConstraintError::ArtifactMismatch));
        assert_eq!(branch.negative_variant(&alternatives), Err(crate::ConstraintError::ArtifactMismatch));
        assert_eq!(branch.positive_variant(&[]), Err(crate::ConstraintError::ArtifactMismatch));
        let foreign = BranchTermArena::new(TermBuilder::new().unwrap().seal().unwrap())
            .live_variable(ComponentKind::Value, Polarity::Positive, 0).unwrap();
        assert_eq!(branch.positive_variant(&[VariantAlternative { tag: "foreign".into(), payloads: Box::new([foreign]) }]),
            Err(crate::ConstraintError::ArtifactMismatch));
        assert_eq!(branch.observations().committed_nodes, before);
        assert_eq!(BranchTermArena::new(lineage).term_view(term), Err(TermLookupError::InvalidHandle));
        assert_eq!(branch.checked_retained_bytes(), branch.checked_independent_retained_bytes());
        branch.begin_route();
        let nested = branch.positive_variant(&[VariantAlternative { tag: "nested".into(), payloads: Box::new([term]) }]).unwrap();
        branch.rollback_route();
        assert!(branch.term_view(term).is_ok());
        assert_eq!(branch.term_view(nested), Err(TermLookupError::InvalidHandle));
        assert_eq!(branch.checked_retained_bytes(), branch.checked_independent_retained_bytes());
    }

    #[test]
    fn record_terms_preserve_labels_empty_identity_children_and_branch_accounting() {
        #[cfg(feature = "f5c_resource_probe")]
        let event_path = {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target")
                .join(format!("record-owner-{}.bin", std::process::id()));
            crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
            path
        };
        let mut branch = BranchTermArena::new(TermBuilder::new().unwrap().seal().unwrap());
        let child = branch.live_variable(ComponentKind::Value, Polarity::Positive, 0).unwrap();
        branch.take_capacity_events().count();
        let negative = branch.live_variable(ComponentKind::Value, Polarity::Negative, 0).unwrap();
        branch.take_capacity_events().count();
        let fields = vec![RecordField::required("x", child), RecordField::required("alias", child)];
        let record = branch.positive_record(&fields).unwrap();
        branch.take_capacity_events().count();
        assert_eq!(branch.term_view(record).unwrap(), TermView::PositiveRecord { fields: &fields });
        assert_eq!(branch.positive_record(&fields).unwrap(), record);
        let empty = branch.positive_record(&[]).unwrap();
        branch.take_capacity_events().count();
        assert_ne!(record, empty);
        assert_eq!(branch.term_view(empty).unwrap(), TermView::PositiveRecord { fields: &[] });
        let swapped = branch.positive_record(&[RecordField::required("alias", child), RecordField::required("x", child)]).unwrap();
        branch.take_capacity_events().count();
        assert_ne!(record, swapped);
        let before = branch.observations().committed_nodes;
        assert_eq!(branch.positive_record(&[RecordField::required("bad", negative)]), Err(crate::ConstraintError::ArtifactMismatch));
        let foreign = BranchTermArena::new(TermBuilder::new().unwrap().seal().unwrap())
            .live_variable(ComponentKind::Value, Polarity::Positive, 0).unwrap();
        assert_eq!(branch.positive_record(&[RecordField::required("foreign", foreign)]), Err(crate::ConstraintError::ArtifactMismatch));
        assert_eq!(branch.observations().committed_nodes, before);
        assert_eq!(branch.checked_retained_bytes(), branch.checked_independent_retained_bytes());
        assert_eq!(branch.independent_owner_lanes().unwrap().bytes.into_iter().sum::<usize>(), branch.checked_retained_bytes().unwrap());
        branch.begin_route();
        let rolled_back = branch.positive_record(&[RecordField::required("nested", record)]).unwrap();
        branch.rollback_route();
        assert!(branch.term_view(record).is_ok());
        assert_eq!(branch.term_view(rolled_back), Err(TermLookupError::InvalidHandle));
        assert_eq!(branch.checked_retained_bytes(), branch.checked_independent_retained_bytes());
        #[cfg(feature = "f5c_resource_probe")]
        {
            assert_eq!(crate::f5c_draft_heap::term_event_totals().1, branch.checked_retained_bytes().unwrap());
            drop(branch);
            assert_eq!(crate::f5c_draft_heap::term_event_totals().1, 0);
            crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
            std::fs::remove_file(event_path).unwrap();
        }
    }

    #[test]
    fn record_presence_and_negative_children_remain_distinct_interned_payloads() {
        let mut branch = BranchTermArena::new(TermBuilder::new().unwrap().seal().unwrap());
        let positive = branch.live_variable(ComponentKind::Value, Polarity::Positive, 0).unwrap();
        branch.take_capacity_events().count();
        let negative = branch.live_variable(ComponentKind::Value, Polarity::Negative, 0).unwrap();
        branch.take_capacity_events().count();
        for polarity in [Polarity::Positive, Polarity::Negative] {
            let child = if polarity == Polarity::Positive { positive } else { negative };
            let required = vec![RecordField::required("x", child), RecordField::required("again", child)];
            let mut optional = required.clone();
            optional[0].optional = true;
            let first = branch.record(&required, polarity).unwrap();
            branch.take_capacity_events().count();
            let second = branch.record(&optional, polarity).unwrap();
            branch.take_capacity_events().count();
            assert_ne!(first, second);
            assert_eq!(branch.record(&optional, polarity).unwrap(), second);
            let retained = match branch.term_view(second).unwrap() {
                TermView::PositiveRecord { fields } if polarity == Polarity::Positive => fields,
                TermView::NegativeRecord { fields } if polarity == Polarity::Negative => fields,
                other => panic!("record polarity changed: {other:?}"),
            };
            assert_eq!(retained, optional);
            let opposite = if polarity == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
            assert_eq!(branch.record(&optional, opposite), Err(crate::ConstraintError::ArtifactMismatch));
        }
        let positive_empty = branch.positive_record(&[]).unwrap();
        branch.take_capacity_events().count();
        let negative_empty = branch.negative_record(&[]).unwrap();
        branch.take_capacity_events().count();
        assert_ne!(positive_empty, negative_empty);
        assert_eq!(branch.checked_retained_bytes(), branch.checked_independent_retained_bytes());
    }

    #[test]
    fn ordered_tuple_terms_preserve_arity_order_duplicates_and_polarity() {
        let mut branch = BranchTermArena::new(TermBuilder::new().unwrap().seal().unwrap());
        macro_rules! positive_tuple {
            ($elements:expr) => {{
                let term = branch.positive_tuple($elements).unwrap();
                branch.take_capacity_events().count();
                term
            }};
        }
        macro_rules! negative_tuple {
            ($elements:expr) => {{
                let term = branch.negative_tuple($elements).unwrap();
                branch.take_capacity_events().count();
                term
            }};
        }
        let p0 = branch.live_variable(ComponentKind::Value, Polarity::Positive, 0).unwrap();
        branch.take_capacity_events().count();
        let p1 = branch.live_variable(ComponentKind::Value, Polarity::Positive, 1).unwrap();
        branch.take_capacity_events().count();
        let p2 = branch.live_variable(ComponentKind::Value, Polarity::Positive, 2).unwrap();
        branch.take_capacity_events().count();
        let n0 = branch.live_variable(ComponentKind::Value, Polarity::Negative, 0).unwrap();
        branch.take_capacity_events().count();
        let n1 = branch.live_variable(ComponentKind::Value, Polarity::Negative, 1).unwrap();
        branch.take_capacity_events().count();
        let n2 = branch.live_variable(ComponentKind::Value, Polarity::Negative, 2).unwrap();
        branch.take_capacity_events().count();

        for elements in [&[p0][..], &[p0, p1][..], &[p0, p1, p2][..], &[p0, p1, p0][..]] {
            let tuple = positive_tuple!(elements);
            assert_eq!(branch.term_view(tuple).unwrap(), TermView::PositiveTuple { elements });
            assert_eq!(positive_tuple!(elements), tuple);
        }
        let pair = positive_tuple!(&[p0, p1]);
        let swapped = positive_tuple!(&[p1, p0]);
        let duplicate = positive_tuple!(&[p0, p0]);
        assert_ne!(pair, swapped);
        assert_ne!(pair, duplicate);
        assert_eq!(branch.term_kind(pair).unwrap(), ComponentKind::Value);

        let negative = negative_tuple!(&[n0, n1, n2]);
        assert_eq!(branch.term_view(negative).unwrap(), TermView::NegativeTuple { elements: &[n0, n1, n2] });
        let before = branch.observations().committed_nodes;
        assert_eq!(branch.positive_tuple(&[]), Err(crate::ConstraintError::ArtifactMismatch));
        assert_eq!(branch.negative_tuple(&[]), Err(crate::ConstraintError::ArtifactMismatch));
        assert_eq!(branch.positive_tuple(&[n0]), Err(crate::ConstraintError::ArtifactMismatch));
        assert_eq!(branch.negative_tuple(&[p0]), Err(crate::ConstraintError::ArtifactMismatch));
        let foreign = BranchTermArena::new(TermBuilder::new().unwrap().seal().unwrap())
            .live_variable(ComponentKind::Value, Polarity::Positive, 0).unwrap();
        assert_eq!(branch.positive_tuple(&[foreign]), Err(crate::ConstraintError::ArtifactMismatch));
        assert_eq!(branch.observations().committed_nodes, before);

        assert_eq!(branch.checked_retained_bytes(), branch.checked_independent_retained_bytes());
        assert_eq!(branch.independent_owner_lanes().unwrap().bytes.into_iter().sum::<usize>(),
            branch.checked_retained_bytes().unwrap());
        let retained = positive_tuple!(&[p2, p1]);
        branch.begin_route();
        let rolled_back = branch.positive_tuple(&[p2, p0]).unwrap();
        branch.rollback_route();
        assert!(branch.term_view(retained).is_ok());
        assert_eq!(branch.term_view(rolled_back), Err(TermLookupError::InvalidHandle));
        assert_eq!(branch.checked_retained_bytes(), branch.checked_independent_retained_bytes());

    }

    #[test]
    fn f5b_term_reserve_failures_do_not_publish_a_node_and_retry_keeps_the_prior_handle() {
        let lineage = TermBuilder::new().unwrap().seal().unwrap();
        let mut branch = BranchTermArena::new(lineage);
        let committed = branch
            .live_variable(ComponentKind::Value, Polarity::Positive, 1)
            .unwrap();
        let before = branch.observations();
        crate::inject_next_f5b_reserve_failure(crate::F5bCapacityLane::TermInterner);
        assert_eq!(
            branch.live_variable(ComponentKind::Value, Polarity::Positive, 2),
            Err(crate::ConstraintError::IdentityExhausted)
        );
        assert_eq!(
            branch.observations().committed_nodes,
            before.committed_nodes
        );
        assert!(branch.term_view(committed).is_ok());
        let retry = branch
            .live_variable(ComponentKind::Value, Polarity::Positive, 2)
            .unwrap();
        assert!(branch.term_view(retry).is_ok());

        let mut fresh_branch = BranchTermArena::new(TermBuilder::new().unwrap().seal().unwrap());
        crate::inject_next_f5b_reserve_failure(crate::F5bCapacityLane::TermPages);
        assert_eq!(
            fresh_branch.live_variable(ComponentKind::Value, Polarity::Positive, 3),
            Err(crate::ConstraintError::IdentityExhausted)
        );
        assert_eq!(fresh_branch.observations().committed_nodes, 0);
        assert!(
            fresh_branch
                .live_variable(ComponentKind::Value, Polarity::Positive, 3)
                .is_ok()
        );
    }

    #[test]
    fn route_rollback_truncates_nodes_added_to_an_existing_page() {
        let lineage = TermBuilder::new().unwrap().seal().unwrap();
        let mut branch = BranchTermArena::new(lineage);
        let retained = branch
            .live_variable(ComponentKind::Value, Polarity::Positive, 1)
            .unwrap();
        branch.begin_route();
        let rolled_back = branch
            .live_variable(ComponentKind::Value, Polarity::Positive, 2)
            .unwrap();

        branch.rollback_route();

        assert!(branch.term_view(retained).is_ok());
        assert_eq!(
            branch.term_view(rolled_back),
            Err(TermLookupError::InvalidHandle)
        );
        assert_eq!(branch.pages.len(), 1);
        assert_eq!(branch.pages[0].initialized, 1);
    }
}
