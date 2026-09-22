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

/// Borrowed term observation remains exhaustively matchable without exposing a
/// constructor or interner for its opaque child handles.
///
/// ```
/// use yu_solver::TermView;
///
/// fn observe(view: TermView<'_>) {
///     match view {
///         TermView::Leaf(_) | TermView::Component(_) | TermView::LiveVariable(_) => {}
///         TermView::PositiveFunction { .. } | TermView::NegativeFunction { .. } => {}
///     }
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TermView<'a> {
    Leaf(Leaf),
    Component(&'a ComponentId),
    LiveVariable(LiveVariableView),
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
}
impl TermNode {
    pub(crate) const fn kind(&self) -> ComponentKind {
        match self {
            Self::Leaf(leaf) => leaf.component_kind(),
            Self::Component(component) => component.kind(),
            Self::LiveVariable(view) => view.kind,
            // Function collection is a later F5 gate.  These variants exist
            // solely because the approved observation algebra already names
            // them; no F5b path constructs one.
            Self::PositiveFunction { .. } | Self::NegativeFunction { .. } => ComponentKind::Value,
        }
    }
    pub(crate) fn view(&self) -> TermView<'_> {
        match self {
            Self::Leaf(leaf) => TermView::Leaf(*leaf),
            Self::Component(component) => TermView::Component(component),
            Self::LiveVariable(view) => TermView::LiveVariable(*view),
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
    #[cfg(test)]
    directory_probes: AtomicUsize,
}
#[allow(
    dead_code,
    reason = "F5b fixed-page allocation is exercised by private lifecycle seams before F5d produces postfix terms"
)]
impl BranchTermArena {
    pub(crate) fn new(lineage: Arc<TermLineage>) -> Self {
        Self {
            lineage,
            pages: Vec::new(),
            page_positions: HashMap::new(),
            positions: HashMap::new(),
            #[cfg(test)]
            directory_probes: AtomicUsize::new(0),
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
    pub(crate) fn retained_bytes(&self) -> usize {
        let page_slots = self
            .pages
            .len()
            .checked_mul(std::mem::size_of::<
                [MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize],
            >())
            .expect("F5b Term page storage fits usize");
        [
            page_slots,
            self.pages
                .capacity()
                .checked_mul(std::mem::size_of::<TermPage>())
                .expect("F5b Term page descriptors fit usize"),
            self.page_positions
                .capacity()
                .checked_mul(std::mem::size_of::<(u32, usize)>())
                .expect("F5b Term page index fits usize"),
            self.positions
                .capacity()
                .checked_mul(std::mem::size_of::<(TermNode, Term)>())
                .expect("F5b Term interner fits usize"),
        ]
        .into_iter()
        .try_fold(0usize, |total, lane| total.checked_add(lane))
        .expect("F5b Term arena aggregate fits usize")
    }

    #[cfg(test)]
    pub(crate) fn independent_retained_bytes(&self) -> usize {
        let fixed_page_bytes = self
            .pages
            .len()
            .checked_mul(std::mem::size_of::<
                [MaybeUninit<TermNode>; TERM_PAGE_SLOTS as usize],
            >())
            .expect("independent Term fixed pages fit usize");
        [
            fixed_page_bytes,
            self.pages
                .capacity()
                .checked_mul(std::mem::size_of::<TermPage>())
                .expect("independent Term descriptors fit usize"),
            self.page_positions
                .capacity()
                .checked_mul(std::mem::size_of::<(u32, usize)>())
                .expect("independent Term directory fits usize"),
            self.positions
                .capacity()
                .checked_mul(std::mem::size_of::<(TermNode, Term)>())
                .expect("independent Term memo fits usize"),
        ]
        .into_iter()
        .try_fold(0usize, usize::checked_add)
        .expect("independent Term storage fits usize")
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
            reserve_f5b(&mut self.pages, 1, F5bCapacityLane::TermPages)?;
            reserve_f5b(
                &mut self.page_positions,
                1,
                F5bCapacityLane::TermPagePositions,
            )?;
            let mut page =
                TermPage::try_new().map_err(|_| crate::ConstraintError::IdentityExhausted)?;
            let base = self.claim_page()?;
            let position = self.pages.len();
            let previous = self.page_positions.insert(base, position);
            debug_assert!(previous.is_none(), "a claimed page base is never reused");
            page.base = base;
            self.pages.push(page);
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
        reserve_f5b(&mut self.positions, 1, F5bCapacityLane::TermInterner)?;
        let term = self.push(node.clone())?;
        self.positions.insert(node, term);
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
        (ComponentKind::Value, Polarity::Positive, TermNode::Leaf(Leaf::IntPositive))
        | (ComponentKind::Value, Polarity::Negative, TermNode::Leaf(Leaf::IntNegative))
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
        })
    }

    fn push(&mut self, node: TermNode) -> u32 {
        let offset = self.initialized as usize;
        debug_assert!(offset < TERM_PAGE_SLOTS as usize);
        self.nodes[offset].write(node);
        self.initialized += 1;
        self.base + offset as u32
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
}
