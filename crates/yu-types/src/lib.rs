//! Canonical type and effect boundary for Yulang3.

use std::{
    collections::HashMap,
    marker::PhantomData,
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
    rc::Rc,
    sync::atomic::{AtomicU64, Ordering},
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ComponentKind {
    Value,
    Effect,
}
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Polarity {
    Positive,
    Negative,
}
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Leaf {
    IntPositive,
    IntNegative,
    EffectBottomPositive,
    EmptyEffectNegative,
}
impl Leaf {
    pub const fn component_kind(self) -> ComponentKind {
        match self {
            Self::IntPositive | Self::IntNegative => ComponentKind::Value,
            Self::EffectBottomPositive | Self::EmptyEffectNegative => ComponentKind::Effect,
        }
    }
    pub const fn polarity(self) -> Polarity {
        match self {
            Self::IntPositive | Self::EffectBottomPositive => Polarity::Positive,
            Self::IntNegative | Self::EmptyEffectNegative => Polarity::Negative,
        }
    }
}

static NEXT_ARENA_BRAND: AtomicU64 = AtomicU64::new(1);
macro_rules! id {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name {
            arena: u64,
            index: u32,
        }
    };
}
id!(PositiveValueId);
id!(NegativeValueId);
id!(PositiveEffectId);
id!(NegativeEffectId);
id!(NeutralValueId);
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct QuantifierId(u32);
impl QuantifierId {
    pub const fn ordinal(self) -> u32 {
        self.0
    }
}
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecursiveBinderId(u32);
impl RecursiveBinderId {
    pub const fn ordinal(self) -> u32 {
        self.0
    }
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ClosedRecursiveBound {
    binder: RecursiveBinderId,
    bounds: NeutralValueId,
}
impl ClosedRecursiveBound {
    pub const fn binder(self) -> RecursiveBinderId {
        self.binder
    }
    pub const fn bounds(self) -> NeutralValueId {
        self.bounds
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClosedTypeLookupError {
    ArenaMismatch,
    InvalidHandle,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PositiveValueView<'a> {
    Bottom,
    Int,
    Quantified(QuantifierId),
    Recursive(RecursiveBinderId),
    Function {
        argument: NegativeValueId,
        argument_effect: NegativeEffectId,
        result_effect: PositiveEffectId,
        result: PositiveValueId,
    },
    Union(&'a [PositiveValueId]),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NegativeValueView<'a> {
    Top,
    Bottom,
    Int,
    Quantified(QuantifierId),
    Recursive(RecursiveBinderId),
    Function {
        argument: PositiveValueId,
        argument_effect: PositiveEffectId,
        result_effect: NegativeEffectId,
        result: NegativeValueId,
    },
    Intersection(&'a [NegativeValueId]),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PositiveEffectView {
    Bottom,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NegativeEffectView {
    Empty,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NeutralValueView {
    Bounds {
        lower: PositiveValueId,
        upper: NegativeValueId,
    },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ClosedValueScheme {
    arena: u64,
    quantifier_count: u32,
    recursive_bounds_start: u32,
    recursive_bounds_len: u32,
    predicate: PositiveValueId,
}
#[derive(Clone, Copy)]
pub struct ClosedValueSchemeView<'a> {
    arena: &'a ClosedTypeArena,
    scheme: &'a ClosedValueScheme,
}
impl<'a> ClosedValueSchemeView<'a> {
    pub const fn quantifier_count(self) -> u32 {
        self.scheme.quantifier_count
    }
    pub fn recursive_bounds(self) -> &'a [ClosedRecursiveBound] {
        let start = self.scheme.recursive_bounds_start as usize;
        let end = start + self.scheme.recursive_bounds_len as usize;
        &self.arena.recursive_bounds[start..end]
    }
    pub const fn predicate(self) -> PositiveValueId {
        self.scheme.predicate
    }
    pub fn positive_value(
        self,
        id: PositiveValueId,
    ) -> Result<PositiveValueView<'a>, ClosedTypeLookupError> {
        self.arena.positive_value(id)
    }
    pub fn negative_value(
        self,
        id: NegativeValueId,
    ) -> Result<NegativeValueView<'a>, ClosedTypeLookupError> {
        self.arena.negative_value(id)
    }
    pub fn positive_effect(
        self,
        id: PositiveEffectId,
    ) -> Result<PositiveEffectView, ClosedTypeLookupError> {
        self.arena.positive_effect(id)
    }
    pub fn negative_effect(
        self,
        id: NegativeEffectId,
    ) -> Result<NegativeEffectView, ClosedTypeLookupError> {
        self.arena.negative_effect(id)
    }
    pub fn neutral_value(
        self,
        id: NeutralValueId,
    ) -> Result<NeutralValueView, ClosedTypeLookupError> {
        self.arena.neutral_value(id)
    }
    pub fn alpha_eq(self, other: ClosedValueSchemeView<'_>) -> bool {
        alpha_eq(self, other)
    }
}

#[derive(Clone, Debug)]
enum PNode {
    Bottom,
    Int,
    Quantified(QuantifierId),
    Recursive(RecursiveBinderId),
    Function {
        argument: NegativeValueId,
        argument_effect: NegativeEffectId,
        result_effect: PositiveEffectId,
        result: PositiveValueId,
    },
    Union {
        start: u32,
        len: u32,
    },
}
#[derive(Clone, Debug)]
enum NNode {
    Top,
    Bottom,
    Int,
    Quantified(QuantifierId),
    Recursive(RecursiveBinderId),
    Function {
        argument: PositiveValueId,
        argument_effect: PositiveEffectId,
        result_effect: NegativeEffectId,
        result: NegativeValueId,
    },
    Intersection {
        start: u32,
        len: u32,
    },
}
#[derive(Clone, Copy, Debug)]
struct NeutralNode {
    lower: PositiveValueId,
    upper: NegativeValueId,
}

#[derive(Debug)]
pub struct ClosedTypeArena {
    brand: u64,
    positives: Vec<PNode>,
    positive_children: Vec<PositiveValueId>,
    negatives: Vec<NNode>,
    negative_children: Vec<NegativeValueId>,
    positive_effects: Vec<()>,
    negative_effects: Vec<()>,
    neutrals: Vec<NeutralNode>,
    recursive_bounds: Vec<ClosedRecursiveBound>,
}
impl ClosedTypeArena {
    pub fn scheme_view<'a>(
        &'a self,
        scheme: &'a ClosedValueScheme,
    ) -> Result<ClosedValueSchemeView<'a>, ClosedTypeLookupError> {
        if scheme.arena != self.brand || scheme.predicate.arena != self.brand {
            return Err(ClosedTypeLookupError::ArenaMismatch);
        }
        self.positive_value(scheme.predicate)?;
        for bound in (ClosedValueSchemeView {
            arena: self,
            scheme,
        })
        .recursive_bounds()
        {
            self.neutral_value(bound.bounds)?;
        }
        Ok(ClosedValueSchemeView {
            arena: self,
            scheme,
        })
    }
    fn index(&self, arena: u64, index: u32) -> Result<usize, ClosedTypeLookupError> {
        if arena == self.brand {
            Ok(index as usize)
        } else {
            Err(ClosedTypeLookupError::ArenaMismatch)
        }
    }
    fn positive_value(
        &self,
        id: PositiveValueId,
    ) -> Result<PositiveValueView<'_>, ClosedTypeLookupError> {
        Ok(
            match self
                .positives
                .get(self.index(id.arena, id.index)?)
                .ok_or(ClosedTypeLookupError::InvalidHandle)?
            {
                PNode::Bottom => PositiveValueView::Bottom,
                PNode::Int => PositiveValueView::Int,
                PNode::Quantified(x) => PositiveValueView::Quantified(*x),
                PNode::Recursive(x) => PositiveValueView::Recursive(*x),
                PNode::Function {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } => PositiveValueView::Function {
                    argument: *argument,
                    argument_effect: *argument_effect,
                    result_effect: *result_effect,
                    result: *result,
                },
                PNode::Union { start, len } => {
                    let start = *start as usize;
                    let end = start + *len as usize;
                    PositiveValueView::Union(&self.positive_children[start..end])
                }
            },
        )
    }
    fn negative_value(
        &self,
        id: NegativeValueId,
    ) -> Result<NegativeValueView<'_>, ClosedTypeLookupError> {
        Ok(
            match self
                .negatives
                .get(self.index(id.arena, id.index)?)
                .ok_or(ClosedTypeLookupError::InvalidHandle)?
            {
                NNode::Top => NegativeValueView::Top,
                NNode::Bottom => NegativeValueView::Bottom,
                NNode::Int => NegativeValueView::Int,
                NNode::Quantified(x) => NegativeValueView::Quantified(*x),
                NNode::Recursive(x) => NegativeValueView::Recursive(*x),
                NNode::Function {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } => NegativeValueView::Function {
                    argument: *argument,
                    argument_effect: *argument_effect,
                    result_effect: *result_effect,
                    result: *result,
                },
                NNode::Intersection { start, len } => {
                    let start = *start as usize;
                    let end = start + *len as usize;
                    NegativeValueView::Intersection(&self.negative_children[start..end])
                }
            },
        )
    }
    fn positive_effect(
        &self,
        id: PositiveEffectId,
    ) -> Result<PositiveEffectView, ClosedTypeLookupError> {
        self.positive_effects
            .get(self.index(id.arena, id.index)?)
            .ok_or(ClosedTypeLookupError::InvalidHandle)?;
        Ok(PositiveEffectView::Bottom)
    }
    fn negative_effect(
        &self,
        id: NegativeEffectId,
    ) -> Result<NegativeEffectView, ClosedTypeLookupError> {
        self.negative_effects
            .get(self.index(id.arena, id.index)?)
            .ok_or(ClosedTypeLookupError::InvalidHandle)?;
        Ok(NegativeEffectView::Empty)
    }
    fn neutral_value(&self, id: NeutralValueId) -> Result<NeutralValueView, ClosedTypeLookupError> {
        let n = self
            .neutrals
            .get(self.index(id.arena, id.index)?)
            .ok_or(ClosedTypeLookupError::InvalidHandle)?;
        Ok(NeutralValueView::Bounds {
            lower: n.lower,
            upper: n.upper,
        })
    }
    #[cfg(test)]
    fn retained_bytes(&self) -> usize {
        fn bytes<T>(lane: &Vec<T>) -> usize {
            lane.capacity()
                .checked_mul(std::mem::size_of::<T>())
                .expect("closed type arena accounting fits")
        }
        [
            bytes(&self.positives),
            bytes(&self.positive_children),
            bytes(&self.negatives),
            bytes(&self.negative_children),
            bytes(&self.positive_effects),
            bytes(&self.negative_effects),
            bytes(&self.neutrals),
            bytes(&self.recursive_bounds),
        ]
        .into_iter()
        .sum()
    }
}

/// The one-shot result of a successful closed scheme transaction.
///
/// ```
/// use yu_types::ClosedSchemeFinalization;
/// fn require_send_sync<T: Send + Sync>() {}
/// require_send_sync::<ClosedSchemeFinalization>();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedSchemeFinalization;
/// let _ = ClosedSchemeFinalization {};
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedSchemeFinalization;
/// fn require_clone<T: Clone>() {}
/// require_clone::<ClosedSchemeFinalization>();
/// ```
#[doc(hidden)]
#[derive(Debug)]
pub struct ClosedSchemeFinalization {
    scheme: ClosedValueScheme,
    checkpoint: ClosedTypeAccountingCheckpoint,
}
impl ClosedSchemeFinalization {
    #[doc(hidden)]
    pub fn into_parts(self) -> (ClosedValueScheme, ClosedTypeAccountingCheckpoint) {
        (self.scheme, self.checkpoint)
    }
    #[cfg(test)]
    fn test_scheme(&self) -> &ClosedValueScheme {
        &self.scheme
    }
}

/// Capacity accounting attached to one successful closed scheme transaction.
///
/// ```
/// use yu_types::ClosedTypeAccountingCheckpoint;
/// fn require_send_sync<T: Send + Sync>() {}
/// require_send_sync::<ClosedTypeAccountingCheckpoint>();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeAccountingCheckpoint;
/// let _ = ClosedTypeAccountingCheckpoint {};
/// ```
#[doc(hidden)]
pub struct ClosedTypeAccountingCheckpoint {
    retained_bytes_before: usize,
    retained_bytes_after: usize,
    peak_bytes_during_call: usize,
    // This remains test-only evidence for the private failure-epoch rule.
    #[allow(dead_code)]
    epoch: u64,
}
impl std::fmt::Debug for ClosedTypeAccountingCheckpoint {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ClosedTypeAccountingCheckpoint")
            .field("retained_bytes_before", &self.retained_bytes_before)
            .field("retained_bytes_after", &self.retained_bytes_after)
            .field("peak_bytes_during_call", &self.peak_bytes_during_call)
            .finish()
    }
}
impl PartialEq for ClosedTypeAccountingCheckpoint {
    fn eq(&self, other: &Self) -> bool {
        self.retained_bytes_before == other.retained_bytes_before
            && self.retained_bytes_after == other.retained_bytes_after
            && self.peak_bytes_during_call == other.peak_bytes_during_call
    }
}
impl Eq for ClosedTypeAccountingCheckpoint {}
impl ClosedTypeAccountingCheckpoint {
    #[doc(hidden)]
    pub const fn retained_bytes_before(&self) -> usize {
        self.retained_bytes_before
    }
    #[doc(hidden)]
    pub const fn retained_bytes_after(&self) -> usize {
        self.retained_bytes_after
    }
    #[doc(hidden)]
    pub const fn peak_bytes_during_call(&self) -> usize {
        self.peak_bytes_during_call
    }
}

/// The consuming result of a completed closed finalization session.
///
/// ```
/// use yu_types::ClosedTypeFinalizationOutput;
/// fn require_send_sync<T: Send + Sync>() {}
/// require_send_sync::<ClosedTypeFinalizationOutput>();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizationOutput;
/// let _ = ClosedTypeFinalizationOutput {};
/// ```
#[doc(hidden)]
#[derive(Debug)]
pub struct ClosedTypeFinalizationOutput {
    arena: ClosedTypeArena,
    receipt: ClosedTypeAccountingReceipt,
}
impl ClosedTypeFinalizationOutput {
    #[doc(hidden)]
    pub fn into_parts(self) -> (ClosedTypeArena, ClosedTypeAccountingReceipt) {
        (self.arena, self.receipt)
    }
}

/// Capacity accounting attached to finalization-session consumption.
///
/// ```
/// use yu_types::ClosedTypeAccountingReceipt;
/// fn require_send_sync<T: Send + Sync>() {}
/// require_send_sync::<ClosedTypeAccountingReceipt>();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeAccountingReceipt;
/// fn require_default<T: Default>() {}
/// require_default::<ClosedTypeAccountingReceipt>();
/// ```
#[doc(hidden)]
#[derive(Debug, Eq, PartialEq)]
pub struct ClosedTypeAccountingReceipt {
    retained_bytes_before_finish: usize,
    retained_bytes_after_finish: usize,
}
impl ClosedTypeAccountingReceipt {
    #[doc(hidden)]
    pub const fn retained_bytes_before_finish(&self) -> usize {
        self.retained_bytes_before_finish
    }
    #[doc(hidden)]
    pub const fn retained_bytes_after_finish(&self) -> usize {
        self.retained_bytes_after_finish
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClosedTypeFinalizeError {
    IdentityExhausted,
    InvalidDraft,
}
macro_rules! draft {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        #[doc(hidden)]
        pub struct $name<'tx> {
            index: u32,
            // Function argument and return positions make this lifetime
            // invariant, so a draft cannot be widened out of its callback.
            marker: PhantomData<fn(&'tx mut ()) -> &'tx mut ()>,
        }
    };
}
draft!(DraftQuantifierId);
draft!(DraftRecursiveBinderId);
draft!(DraftPositiveValueId);
draft!(DraftNegativeValueId);
draft!(DraftPositiveEffectId);
draft!(DraftNegativeEffectId);
draft!(DraftNeutralValueId);
draft!(DraftRecursiveBound);
#[derive(Clone, Copy)]
struct DraftRange {
    start: u32,
    len: u32,
}
#[derive(Clone)]
enum DP {
    Bottom,
    Int,
    Q(u32),
    R(u32),
    Function { a: u32, ae: u32, re: u32, r: u32 },
    Union(DraftRange),
}
#[derive(Clone)]
enum DN {
    Top,
    Bottom,
    Int,
    Q(u32),
    R(u32),
    Function { a: u32, ae: u32, re: u32, r: u32 },
    Intersection(DraftRange),
}
#[derive(Clone, Copy)]
struct DBound {
    binder: u32,
    bounds: u32,
}
#[derive(Clone, Copy)]
struct DScheme {
    q: u32,
    bounds: DraftRange,
    predicate: u32,
}
#[derive(Clone)]
enum PlannedPNode {
    Bottom,
    Int,
    Quantified(u32),
    Recursive(u32),
    Function { a: u32, ae: u32, re: u32, r: u32 },
    Union(DraftRange),
}
#[derive(Clone)]
enum PlannedNNode {
    Top,
    Bottom,
    Int,
    Quantified(u32),
    Recursive(u32),
    Function { a: u32, ae: u32, re: u32, r: u32 },
    Intersection(DraftRange),
}
#[derive(Clone, Copy)]
struct PlannedNeutralNode {
    lower: u32,
    upper: u32,
}
#[derive(Clone, Copy)]
struct PlannedBound {
    binder: u32,
    bounds: u32,
}

/// The only permanent closed-type lane order. Child backing is committed ahead
/// of its referring node, and this sequence governs both reservation and
/// commit so an injected event names one deterministic transaction point.
#[derive(Clone, Copy)]
enum PermanentLane {
    PositiveChild,
    PositiveValue,
    NegativeChild,
    NegativeValue,
    PositiveEffect,
    NegativeEffect,
    NeutralValue,
    RecursiveBound,
    SchemeHeader,
}
const PERMANENT_LANES: [PermanentLane; 9] = [
    PermanentLane::PositiveChild,
    PermanentLane::PositiveValue,
    PermanentLane::NegativeChild,
    PermanentLane::NegativeValue,
    PermanentLane::PositiveEffect,
    PermanentLane::NegativeEffect,
    PermanentLane::NeutralValue,
    PermanentLane::RecursiveBound,
    PermanentLane::SchemeHeader,
];

#[derive(Default)]
struct Scratch {
    q: Vec<u32>,
    r: Vec<u32>,
    p: Vec<DP>,
    p_children: Vec<u32>,
    n: Vec<DN>,
    n_children: Vec<u32>,
    pe: Vec<()>,
    ne: Vec<()>,
    neutral: Vec<(u32, u32)>,
    bounds: Vec<DBound>,
    scheme_bounds: Vec<u32>,
    mapped_p: Vec<PlannedPNode>,
    mapped_p_children: Vec<u32>,
    mapped_n: Vec<PlannedNNode>,
    mapped_n_children: Vec<u32>,
    mapped_neutral: Vec<PlannedNeutralNode>,
    mapped_bounds: Vec<PlannedBound>,
    scheme: Option<DScheme>,
    failure: Option<ClosedTypeFinalizeError>,
}
impl Scratch {
    fn clear(&mut self) {
        self.q.clear();
        self.r.clear();
        self.p.clear();
        self.p_children.clear();
        self.n.clear();
        self.n_children.clear();
        self.pe.clear();
        self.ne.clear();
        self.neutral.clear();
        self.bounds.clear();
        self.scheme_bounds.clear();
        self.mapped_p.clear();
        self.mapped_p_children.clear();
        self.mapped_n.clear();
        self.mapped_n_children.clear();
        self.mapped_neutral.clear();
        self.mapped_bounds.clear();
        self.scheme = None;
        self.failure = None;
    }
    /// Checked draft-lane indexing owns the transaction poison: callers are
    /// allowed to ignore a constructor error, but no later constructor may
    /// turn that ignored exhaustion into a candidate scheme.
    fn index_for_len(
        len: usize,
        failure: &mut Option<ClosedTypeFinalizeError>,
    ) -> Result<u32, ClosedTypeFinalizeError> {
        if let Some(error) = *failure {
            return Err(error);
        }
        match u32::try_from(len) {
            Ok(index) => Ok(index),
            Err(_) => {
                *failure = Some(ClosedTypeFinalizeError::IdentityExhausted);
                Err(ClosedTypeFinalizeError::IdentityExhausted)
            }
        }
    }
    fn checked_capacity_bytes(&self) -> Result<usize, ClosedTypeFinalizeError> {
        fn bytes<T>(v: &Vec<T>) -> Result<usize, ClosedTypeFinalizeError> {
            v.capacity()
                .checked_mul(std::mem::size_of::<T>())
                .ok_or(ClosedTypeFinalizeError::IdentityExhausted)
        }
        [
            bytes(&self.q)?,
            bytes(&self.r)?,
            bytes(&self.p)?,
            bytes(&self.p_children)?,
            bytes(&self.n)?,
            bytes(&self.n_children)?,
            bytes(&self.pe)?,
            bytes(&self.ne)?,
            bytes(&self.neutral)?,
            bytes(&self.bounds)?,
            bytes(&self.scheme_bounds)?,
            bytes(&self.mapped_p)?,
            bytes(&self.mapped_p_children)?,
            bytes(&self.mapped_n)?,
            bytes(&self.mapped_n_children)?,
            bytes(&self.mapped_neutral)?,
            bytes(&self.mapped_bounds)?,
        ]
        .into_iter()
        .try_fold(0usize, |total, lane| {
            total
                .checked_add(lane)
                .ok_or(ClosedTypeFinalizeError::IdentityExhausted)
        })
    }
    #[cfg(test)]
    fn capacity_bytes(&self) -> usize {
        self.checked_capacity_bytes()
            .expect("closed finalization scratch accounting fits")
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FinalizationLane {
    Quantifier,
    RecursiveBinder,
    PositiveValue,
    PositiveChild,
    NegativeValue,
    NegativeChild,
    PositiveEffect,
    NegativeEffect,
    NeutralValue,
    RecursiveBound,
    SchemeHeader,
}
#[cfg(test)]
const fn finalization_lane(lane: PermanentLane) -> FinalizationLane {
    match lane {
        PermanentLane::PositiveChild => FinalizationLane::PositiveChild,
        PermanentLane::PositiveValue => FinalizationLane::PositiveValue,
        PermanentLane::NegativeChild => FinalizationLane::NegativeChild,
        PermanentLane::NegativeValue => FinalizationLane::NegativeValue,
        PermanentLane::PositiveEffect => FinalizationLane::PositiveEffect,
        PermanentLane::NegativeEffect => FinalizationLane::NegativeEffect,
        PermanentLane::NeutralValue => FinalizationLane::NeutralValue,
        PermanentLane::RecursiveBound => FinalizationLane::RecursiveBound,
        PermanentLane::SchemeHeader => FinalizationLane::SchemeHeader,
    }
}
#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FinalizationFailureEvent {
    OverlayWrite {
        lane: FinalizationLane,
        ordinal: usize,
    },
    ArenaReserve {
        lane: FinalizationLane,
        ordinal: usize,
    },
    CommitWrite {
        lane: FinalizationLane,
        ordinal: usize,
    },
}
#[cfg(test)]
#[derive(Default)]
struct FinalizationTestControl {
    fail: Option<FinalizationFailureEvent>,
    panic: Option<FinalizationFailureEvent>,
    seen: Vec<FinalizationFailureEvent>,
    attempts: usize,
    successes: usize,
    rollbacks: usize,
    scratch_peak_bytes: usize,
    scratch_pushes: usize,
    capacity_growths: usize,
    commit_started: bool,
    permanent_handle_writes: usize,
    permanent_handle_writes_before_commit: usize,
    force_capacity_excess_after_reserve: bool,
    force_scratch_capacity_excess_after_reserve: bool,
    force_capacity_excess_during_unwind: bool,
}
#[cfg(test)]
impl FinalizationTestControl {
    fn before(&mut self, event: FinalizationFailureEvent) -> Result<(), ClosedTypeFinalizeError> {
        self.attempts += 1;
        self.seen.push(event);
        if self.panic == Some(event) {
            panic!("injected finalization commit unwind");
        }
        if self.fail == Some(event) {
            return Err(ClosedTypeFinalizeError::InvalidDraft);
        }
        Ok(())
    }
    fn permanent_handle_write(&mut self) {
        self.permanent_handle_writes += 1;
        if !self.commit_started {
            self.permanent_handle_writes_before_commit += 1;
        }
    }
}

/// The finalizer is callback-scoped. It has no public constructor and cannot
/// outlive the higher-ranked transaction that supplies it.
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizer;
/// fn require_send<T: Send>() {}
/// require_send::<ClosedTypeFinalizer<'static>>();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizer;
/// fn require_sync<T: Sync>() {}
/// require_sync::<ClosedTypeFinalizer<'static>>();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizer;
/// fn require_clone<T: Clone>() {}
/// require_clone::<ClosedTypeFinalizer<'static>>();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizer;
/// fn require_copy<T: Copy>() {}
/// require_copy::<ClosedTypeFinalizer<'static>>();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizer;
/// let _ = ClosedTypeFinalizer {};
/// ```
#[doc(hidden)]
pub struct ClosedTypeFinalizer<'tx> {
    scratch: &'tx mut Scratch,
    retained_bytes: &'tx mut usize,
    arena_retained_bytes: usize,
    accounting: &'tx mut AccountingState,
    failure_epoch: &'tx mut u64,
    #[cfg(test)]
    control: &'tx mut FinalizationTestControl,
    marker: PhantomData<Rc<()>>,
}
impl<'tx> ClosedTypeFinalizer<'tx> {
    fn reconcile_after_scratch_reservation(
        &mut self,
        _reservation_succeeded: bool,
    ) -> Result<(), ClosedTypeFinalizeError> {
        #[cfg(test)]
        if _reservation_succeeded && self.control.force_scratch_capacity_excess_after_reserve {
            self.control.force_scratch_capacity_excess_after_reserve = false;
            enter_accounting_exhaustion(self.accounting, self.failure_epoch);
            return Err(ClosedTypeFinalizeError::IdentityExhausted);
        }
        let scratch_bytes = match self.scratch.checked_capacity_bytes() {
            Ok(bytes) => bytes,
            Err(error) => {
                enter_accounting_exhaustion(self.accounting, self.failure_epoch);
                return Err(error);
            }
        };
        let retained_bytes = match self.arena_retained_bytes.checked_add(scratch_bytes) {
            Some(bytes) => bytes,
            None => {
                enter_accounting_exhaustion(self.accounting, self.failure_epoch);
                return Err(ClosedTypeFinalizeError::IdentityExhausted);
            }
        };
        *self.retained_bytes = retained_bytes;
        Ok(())
    }

    fn push_into<T>(
        &mut self,
        lane: fn(&mut Scratch) -> &mut Vec<T>,
        value: T,
    ) -> Result<u32, ClosedTypeFinalizeError> {
        if let Some(error) = self.scratch.failure {
            return Err(error);
        }
        let reservation = {
            let lane = lane(self.scratch);
            let required = lane
                .len()
                .checked_add(1)
                .ok_or(ClosedTypeFinalizeError::IdentityExhausted)?;
            (lane.capacity() < required).then(|| lane.try_reserve_exact(1))
        };
        if let Some(reservation) = reservation {
            // Vec exposes its actual capacity only after this call returns.
            // Reconcile it before an index, draft node, or scheme write.
            if let Err(error) = self.reconcile_after_scratch_reservation(reservation.is_ok()) {
                self.scratch.failure = Some(error);
                return Err(error);
            }
            if reservation.is_err() {
                self.scratch.failure = Some(ClosedTypeFinalizeError::IdentityExhausted);
                return Err(ClosedTypeFinalizeError::IdentityExhausted);
            }
        }
        let index = Scratch::index_for_len(lane(self.scratch).len(), &mut self.scratch.failure)?;
        lane(self.scratch).push(value);
        #[cfg(test)]
        {
            self.control.scratch_pushes += 1;
        }
        Ok(index)
    }

    #[cfg(test)]
    fn before(
        &mut self,
        lane: FinalizationLane,
        ordinal: usize,
    ) -> Result<(), ClosedTypeFinalizeError> {
        self.control
            .before(FinalizationFailureEvent::OverlayWrite { lane, ordinal })
    }
    fn infallible_write(&mut self, lane: u8, ordinal: u32) {
        #[cfg(test)]
        {
            let final_lane = if lane == 0 {
                FinalizationLane::Quantifier
            } else {
                FinalizationLane::RecursiveBinder
            };
            if let Err(error) = self.before(final_lane, ordinal as usize) {
                self.scratch.failure = Some(error);
            }
        }
        #[cfg(not(test))]
        let _ = (lane, ordinal);
    }
    #[cfg(test)]
    fn inject_lane_length_overflow(&mut self) {
        let overflow = usize::try_from(u32::MAX)
            .expect("test target can represent closed draft identities")
            .checked_add(1)
            .expect("test target can represent one exhausted closed draft identity");
        assert_eq!(
            Scratch::index_for_len(overflow, &mut self.scratch.failure),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        );
    }
    pub fn quantifier(&mut self, ordinal: u32) -> DraftQuantifierId<'tx> {
        let position = Scratch::index_for_len(self.scratch.q.len(), &mut self.scratch.failure)
            .unwrap_or(u32::MAX);
        self.infallible_write(0, position);
        let _ = self.push_into(|scratch| &mut scratch.q, ordinal);
        DraftQuantifierId {
            index: ordinal,
            marker: PhantomData,
        }
    }
    pub fn recursive_binder(&mut self, ordinal: u32) -> DraftRecursiveBinderId<'tx> {
        let position = Scratch::index_for_len(self.scratch.r.len(), &mut self.scratch.failure)
            .unwrap_or(u32::MAX);
        self.infallible_write(1, position);
        let _ = self.push_into(|scratch| &mut scratch.r, ordinal);
        DraftRecursiveBinderId {
            index: ordinal,
            marker: PhantomData,
        }
    }
    pub fn positive_bottom(
        &mut self,
    ) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError> {
        self.p(DP::Bottom)
    }
    pub fn positive_int(&mut self) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError> {
        self.p(DP::Int)
    }
    pub fn positive_quantified(
        &mut self,
        b: DraftQuantifierId<'tx>,
    ) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError> {
        self.p(DP::Q(b.index))
    }
    pub fn positive_recursive(
        &mut self,
        b: DraftRecursiveBinderId<'tx>,
    ) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError> {
        self.p(DP::R(b.index))
    }
    pub fn positive_function(
        &mut self,
        a: DraftNegativeValueId<'tx>,
        ae: DraftNegativeEffectId<'tx>,
        re: DraftPositiveEffectId<'tx>,
        r: DraftPositiveValueId<'tx>,
    ) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError> {
        self.nok(a.index)?;
        self.neok(ae.index)?;
        self.peok(re.index)?;
        self.pok(r.index)?;
        self.p(DP::Function {
            a: a.index,
            ae: ae.index,
            re: re.index,
            r: r.index,
        })
    }
    pub fn positive_union(
        &mut self,
        xs: &[DraftPositiveValueId<'tx>],
    ) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError> {
        let start =
            Scratch::index_for_len(self.scratch.p_children.len(), &mut self.scratch.failure)?;
        for x in xs {
            self.pok(x.index)?;
            #[cfg(test)]
            self.before(
                FinalizationLane::PositiveChild,
                self.scratch.p_children.len(),
            )?;
            self.push_into(|scratch| &mut scratch.p_children, x.index)?;
        }
        let len = Scratch::index_for_len(xs.len(), &mut self.scratch.failure)?;
        self.p(DP::Union(DraftRange { start, len }))
    }
    pub fn negative_top(&mut self) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError> {
        self.n(DN::Top)
    }
    pub fn negative_bottom(
        &mut self,
    ) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError> {
        self.n(DN::Bottom)
    }
    pub fn negative_int(&mut self) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError> {
        self.n(DN::Int)
    }
    pub fn negative_quantified(
        &mut self,
        b: DraftQuantifierId<'tx>,
    ) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError> {
        self.n(DN::Q(b.index))
    }
    pub fn negative_recursive(
        &mut self,
        b: DraftRecursiveBinderId<'tx>,
    ) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError> {
        self.n(DN::R(b.index))
    }
    pub fn negative_function(
        &mut self,
        a: DraftPositiveValueId<'tx>,
        ae: DraftPositiveEffectId<'tx>,
        re: DraftNegativeEffectId<'tx>,
        r: DraftNegativeValueId<'tx>,
    ) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError> {
        self.pok(a.index)?;
        self.peok(ae.index)?;
        self.neok(re.index)?;
        self.nok(r.index)?;
        self.n(DN::Function {
            a: a.index,
            ae: ae.index,
            re: re.index,
            r: r.index,
        })
    }
    pub fn negative_intersection(
        &mut self,
        xs: &[DraftNegativeValueId<'tx>],
    ) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError> {
        let start =
            Scratch::index_for_len(self.scratch.n_children.len(), &mut self.scratch.failure)?;
        for x in xs {
            self.nok(x.index)?;
            #[cfg(test)]
            self.before(
                FinalizationLane::NegativeChild,
                self.scratch.n_children.len(),
            )?;
            self.push_into(|scratch| &mut scratch.n_children, x.index)?;
        }
        let len = Scratch::index_for_len(xs.len(), &mut self.scratch.failure)?;
        self.n(DN::Intersection(DraftRange { start, len }))
    }
    pub fn positive_effect_bottom(
        &mut self,
    ) -> Result<DraftPositiveEffectId<'tx>, ClosedTypeFinalizeError> {
        #[cfg(test)]
        self.before(FinalizationLane::PositiveEffect, self.scratch.pe.len())?;
        Ok(DraftPositiveEffectId {
            index: self.push_into(|scratch| &mut scratch.pe, ())?,
            marker: PhantomData,
        })
    }
    pub fn negative_effect_empty(
        &mut self,
    ) -> Result<DraftNegativeEffectId<'tx>, ClosedTypeFinalizeError> {
        #[cfg(test)]
        self.before(FinalizationLane::NegativeEffect, self.scratch.ne.len())?;
        Ok(DraftNegativeEffectId {
            index: self.push_into(|scratch| &mut scratch.ne, ())?,
            marker: PhantomData,
        })
    }
    pub fn neutral_bounds(
        &mut self,
        l: DraftPositiveValueId<'tx>,
        u: DraftNegativeValueId<'tx>,
    ) -> Result<DraftNeutralValueId<'tx>, ClosedTypeFinalizeError> {
        self.pok(l.index)?;
        self.nok(u.index)?;
        #[cfg(test)]
        self.before(FinalizationLane::NeutralValue, self.scratch.neutral.len())?;
        Ok(DraftNeutralValueId {
            index: self.push_into(|scratch| &mut scratch.neutral, (l.index, u.index))?,
            marker: PhantomData,
        })
    }
    pub fn recursive_bound(
        &mut self,
        b: DraftRecursiveBinderId<'tx>,
        n: DraftNeutralValueId<'tx>,
    ) -> Result<DraftRecursiveBound<'tx>, ClosedTypeFinalizeError> {
        self.neutralok(n.index)?;
        #[cfg(test)]
        self.before(FinalizationLane::RecursiveBound, self.scratch.bounds.len())?;
        Ok(DraftRecursiveBound {
            index: self.push_into(
                |scratch| &mut scratch.bounds,
                DBound {
                    binder: b.index,
                    bounds: n.index,
                },
            )?,
            marker: PhantomData,
        })
    }
    pub fn set_scheme(
        &mut self,
        q: u32,
        bounds: &[DraftRecursiveBound<'tx>],
        predicate: DraftPositiveValueId<'tx>,
    ) -> Result<(), ClosedTypeFinalizeError> {
        if let Some(error) = self.scratch.failure {
            return Err(error);
        }
        self.pok(predicate.index)?;
        if self.scratch.scheme.is_some() {
            self.scratch.failure = Some(ClosedTypeFinalizeError::InvalidDraft);
            return Err(ClosedTypeFinalizeError::InvalidDraft);
        }
        let start =
            Scratch::index_for_len(self.scratch.scheme_bounds.len(), &mut self.scratch.failure)?;
        for bound in bounds {
            self.boundok(bound.index)?;
            #[cfg(test)]
            self.before(
                FinalizationLane::SchemeHeader,
                self.scratch.scheme_bounds.len(),
            )?;
            self.push_into(|scratch| &mut scratch.scheme_bounds, bound.index)?;
        }
        self.scratch.scheme = Some(DScheme {
            q,
            bounds: DraftRange {
                start,
                len: Scratch::index_for_len(bounds.len(), &mut self.scratch.failure)?,
            },
            predicate: predicate.index,
        });
        Ok(())
    }
    fn p(&mut self, x: DP) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError> {
        #[cfg(test)]
        self.before(FinalizationLane::PositiveValue, self.scratch.p.len())?;
        Ok(DraftPositiveValueId {
            index: self.push_into(|scratch| &mut scratch.p, x)?,
            marker: PhantomData,
        })
    }
    fn n(&mut self, x: DN) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError> {
        #[cfg(test)]
        self.before(FinalizationLane::NegativeValue, self.scratch.n.len())?;
        Ok(DraftNegativeValueId {
            index: self.push_into(|scratch| &mut scratch.n, x)?,
            marker: PhantomData,
        })
    }
    fn pok(&self, i: u32) -> Result<(), ClosedTypeFinalizeError> {
        self.scratch
            .p
            .get(i as usize)
            .map(|_| ())
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)
    }
    fn nok(&self, i: u32) -> Result<(), ClosedTypeFinalizeError> {
        self.scratch
            .n
            .get(i as usize)
            .map(|_| ())
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)
    }
    fn peok(&self, i: u32) -> Result<(), ClosedTypeFinalizeError> {
        self.scratch
            .pe
            .get(i as usize)
            .map(|_| ())
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)
    }
    fn neok(&self, i: u32) -> Result<(), ClosedTypeFinalizeError> {
        self.scratch
            .ne
            .get(i as usize)
            .map(|_| ())
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)
    }
    fn neutralok(&self, i: u32) -> Result<(), ClosedTypeFinalizeError> {
        self.scratch
            .neutral
            .get(i as usize)
            .map(|_| ())
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)
    }
    fn boundok(&self, i: u32) -> Result<(), ClosedTypeFinalizeError> {
        self.scratch
            .bounds
            .get(i as usize)
            .map(|_| ())
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ArenaLengths {
    p: usize,
    pc: usize,
    n: usize,
    nc: usize,
    pe: usize,
    ne: usize,
    neutral: usize,
    bounds: usize,
}
impl ArenaLengths {
    fn from_arena(a: &ClosedTypeArena) -> Self {
        Self {
            p: a.positives.len(),
            pc: a.positive_children.len(),
            n: a.negatives.len(),
            nc: a.negative_children.len(),
            pe: a.positive_effects.len(),
            ne: a.negative_effects.len(),
            neutral: a.neutrals.len(),
            bounds: a.recursive_bounds.len(),
        }
    }
}
struct CommitRollback<'a> {
    arena: &'a mut ClosedTypeArena,
    lengths: ArenaLengths,
    committed: bool,
}
impl Drop for CommitRollback<'_> {
    fn drop(&mut self) {
        if !self.committed {
            self.arena.positives.truncate(self.lengths.p);
            self.arena.positive_children.truncate(self.lengths.pc);
            self.arena.negatives.truncate(self.lengths.n);
            self.arena.negative_children.truncate(self.lengths.nc);
            self.arena.positive_effects.truncate(self.lengths.pe);
            self.arena.negative_effects.truncate(self.lengths.ne);
            self.arena.neutrals.truncate(self.lengths.neutral);
            self.arena.recursive_bounds.truncate(self.lengths.bounds);
        }
    }
}

/// A solve-scoped, non-transferable closed-type construction capability.
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizationSession;
/// let session = ClosedTypeFinalizationSession::try_new().unwrap();
/// let _clone = session.clone();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizationSession;
/// let session = ClosedTypeFinalizationSession::try_new().unwrap();
/// let _copy = session;
/// let _again = session;
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizationSession;
/// let session = ClosedTypeFinalizationSession::try_new().unwrap();
/// let _debug = format!("{session:?}");
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizationSession;
/// fn require_send<T: Send>() {}
/// require_send::<ClosedTypeFinalizationSession>();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizationSession;
/// fn require_sync<T: Sync>() {}
/// require_sync::<ClosedTypeFinalizationSession>();
/// ```
///
/// ```compile_fail
/// use yu_types::{ClosedTypeFinalizationSession, DraftPositiveValueId};
/// fn leak<'a>() -> DraftPositiveValueId<'a> {
///     let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
///     let mut leaked = None;
///     session.finalize_scheme(|finalizer| {
///         leaked = Some(finalizer.positive_bottom()?);
///         Ok(())
///     }).unwrap();
///     leaked.unwrap()
/// }
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizationSession;
/// let _ = ClosedTypeFinalizationSession {};
/// ```
///
/// ```compile_fail
/// use yu_types::DraftQuantifierId;
/// use core::marker::PhantomData;
/// let _: DraftQuantifierId<'static> = DraftQuantifierId { index: 0, marker: PhantomData };
/// ```
///
/// ```compile_fail
/// use yu_types::DraftRecursiveBinderId;
/// use core::marker::PhantomData;
/// let _: DraftRecursiveBinderId<'static> = DraftRecursiveBinderId { index: 0, marker: PhantomData };
/// ```
///
/// ```compile_fail
/// use yu_types::DraftPositiveValueId;
/// use core::marker::PhantomData;
/// let _: DraftPositiveValueId<'static> = DraftPositiveValueId { index: 0, marker: PhantomData };
/// ```
///
/// ```compile_fail
/// use yu_types::DraftNegativeValueId;
/// use core::marker::PhantomData;
/// let _: DraftNegativeValueId<'static> = DraftNegativeValueId { index: 0, marker: PhantomData };
/// ```
///
/// ```compile_fail
/// use yu_types::DraftPositiveEffectId;
/// use core::marker::PhantomData;
/// let _: DraftPositiveEffectId<'static> = DraftPositiveEffectId { index: 0, marker: PhantomData };
/// ```
///
/// ```compile_fail
/// use yu_types::DraftNegativeEffectId;
/// use core::marker::PhantomData;
/// let _: DraftNegativeEffectId<'static> = DraftNegativeEffectId { index: 0, marker: PhantomData };
/// ```
///
/// ```compile_fail
/// use yu_types::DraftNeutralValueId;
/// use core::marker::PhantomData;
/// let _: DraftNeutralValueId<'static> = DraftNeutralValueId { index: 0, marker: PhantomData };
/// ```
///
/// ```compile_fail
/// use yu_types::DraftRecursiveBound;
/// use core::marker::PhantomData;
/// let _: DraftRecursiveBound<'static> = DraftRecursiveBound { index: 0, marker: PhantomData };
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeFinalizationSession;
/// let mut left = ClosedTypeFinalizationSession::try_new().unwrap();
/// let mut right = ClosedTypeFinalizationSession::try_new().unwrap();
/// let _ = left.finalize_scheme(|left_finalizer| {
///     let foreign = left_finalizer.positive_bottom()?;
///     right.finalize_scheme(|right_finalizer| {
///         right_finalizer.set_scheme(0, &[], foreign)
///     })?;
///     left_finalizer.set_scheme(0, &[], foreign)
/// });
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeArena;
/// let _ = ClosedTypeArena::try_new_for_finalization();
/// ```
///
/// ```compile_fail
/// use yu_types::ClosedTypeArena;
/// fn old_entrypoint(arena: &mut ClosedTypeArena) {
///     let _ = arena.finalize_scheme(|_| Ok(()));
/// }
/// ```
#[doc(hidden)]
pub struct ClosedTypeFinalizationSession {
    arena: ClosedTypeArena,
    scratch: Scratch,
    retained_bytes: usize,
    arena_retained_bytes: usize,
    accounting: AccountingState,
    failure_epoch: u64,
    #[cfg(test)]
    control: FinalizationTestControl,
    marker: PhantomData<Rc<()>>,
}
/// The byte totals are valid only while every observed capacity sum fits.
/// Exhaustion deliberately retains the physical allocations for drop, while
/// making all later publication impossible.
enum AccountingState {
    Valid,
    Exhausted,
}
impl ClosedTypeFinalizationSession {
    #[doc(hidden)]
    pub fn try_new() -> Result<Self, ClosedTypeFinalizeError> {
        let brand = NEXT_ARENA_BRAND
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |x| x.checked_add(1))
            .map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        Ok(Self {
            arena: ClosedTypeArena {
                brand,
                positives: Vec::new(),
                positive_children: Vec::new(),
                negatives: Vec::new(),
                negative_children: Vec::new(),
                positive_effects: Vec::new(),
                negative_effects: Vec::new(),
                neutrals: Vec::new(),
                recursive_bounds: Vec::new(),
            },
            scratch: Scratch::default(),
            retained_bytes: 0,
            arena_retained_bytes: 0,
            accounting: AccountingState::Valid,
            failure_epoch: 0,
            #[cfg(test)]
            control: FinalizationTestControl::default(),
            marker: PhantomData,
        })
    }
    #[doc(hidden)]
    pub fn finalize_scheme<F>(
        &mut self,
        build: F,
    ) -> Result<ClosedSchemeFinalization, ClosedTypeFinalizeError>
    where
        F: for<'tx> FnOnce(&mut ClosedTypeFinalizer<'tx>) -> Result<(), ClosedTypeFinalizeError>,
    {
        if matches!(self.accounting, AccountingState::Exhausted) {
            return Err(ClosedTypeFinalizeError::IdentityExhausted);
        }
        let retained_bytes_before = self.retained_bytes;
        #[cfg(test)]
        let capacity_before = {
            self.control.seen.clear();
            self.control.commit_started = false;
            self.arena
                .retained_bytes()
                .checked_add(self.scratch.capacity_bytes())
                .expect("closed finalization capacity accounting fits")
        };
        self.scratch.clear();
        let outcome = {
            let mut finalizer = ClosedTypeFinalizer {
                scratch: &mut self.scratch,
                retained_bytes: &mut self.retained_bytes,
                arena_retained_bytes: self.arena_retained_bytes,
                accounting: &mut self.accounting,
                failure_epoch: &mut self.failure_epoch,
                #[cfg(test)]
                control: &mut self.control,
                marker: PhantomData,
            };
            catch_unwind(AssertUnwindSafe(|| build(&mut finalizer)))
        };
        let result = match outcome {
            Err(payload) => {
                #[cfg(test)]
                {
                    self.control.rollbacks += 1;
                }
                self.scratch.clear();
                self.record_failed_attempt();
                resume_unwind(payload)
            }
            Ok(Err(error)) => Err(error),
            Ok(Ok(())) => {
                if let Some(error) = self.scratch.failure {
                    Err(error)
                } else {
                    let committed = catch_unwind(AssertUnwindSafe(|| {
                        validate(&self.scratch)?;
                        self.plan()?;
                        self.reserve()?;
                        self.commit()
                    }));
                    match committed {
                        Ok(result) => result,
                        Err(payload) => {
                            #[cfg(test)]
                            {
                                self.control.rollbacks += 1;
                            }
                            self.scratch.clear();
                            self.record_failed_attempt();
                            resume_unwind(payload)
                        }
                    }
                }
            }
        };
        let result = result.and_then(|scheme| {
            self.reconcile_capacity_state()?;
            let (retained_bytes_after, _arena_retained_bytes) = self
                .valid_accounting()
                .ok_or(ClosedTypeFinalizeError::IdentityExhausted)?;
            Ok(ClosedSchemeFinalization {
                scheme,
                checkpoint: ClosedTypeAccountingCheckpoint {
                    retained_bytes_before,
                    retained_bytes_after,
                    peak_bytes_during_call: retained_bytes_before.max(retained_bytes_after),
                    epoch: self.failure_epoch,
                },
            })
        });
        if result.is_err() {
            // A failed reservation may retain capacity. Reconciliation records
            // that physical retry baseline before the next callback can run.
            self.record_failed_attempt();
        }
        #[cfg(test)]
        {
            self.control.scratch_peak_bytes = self
                .control
                .scratch_peak_bytes
                .max(self.scratch.capacity_bytes());
            let capacity_after = self
                .arena
                .retained_bytes()
                .checked_add(self.scratch.capacity_bytes())
                .expect("closed finalization capacity accounting fits");
            self.control.capacity_growths += usize::from(capacity_after != capacity_before);
            if result.is_ok() {
                self.control.successes += 1;
            } else {
                self.control.rollbacks += 1;
            }
        }
        self.scratch.clear();
        result
    }
    #[doc(hidden)]
    pub fn scheme_view<'a>(
        &'a self,
        scheme: &'a ClosedValueScheme,
    ) -> Result<ClosedValueSchemeView<'a>, ClosedTypeLookupError> {
        self.arena.scheme_view(scheme)
    }
    #[doc(hidden)]
    pub fn finish(self) -> Result<ClosedTypeFinalizationOutput, ClosedTypeFinalizeError> {
        let AccountingState::Valid = self.accounting else {
            return Err(ClosedTypeFinalizeError::IdentityExhausted);
        };
        debug_assert!(self.arena_retained_bytes <= self.retained_bytes);
        Ok(ClosedTypeFinalizationOutput {
            arena: self.arena,
            receipt: ClosedTypeAccountingReceipt {
                retained_bytes_before_finish: self.retained_bytes,
                retained_bytes_after_finish: self.arena_retained_bytes,
            },
        })
    }
    fn valid_accounting(&self) -> Option<(usize, usize)> {
        matches!(self.accounting, AccountingState::Valid)
            .then_some((self.retained_bytes, self.arena_retained_bytes))
    }
    fn enter_accounting_exhaustion(&mut self) {
        enter_accounting_exhaustion(&mut self.accounting, &mut self.failure_epoch);
    }
    fn reconcile_capacity_state(&mut self) -> Result<(), ClosedTypeFinalizeError> {
        let retained_bytes = match self.checked_retained_bytes() {
            Ok(bytes) => bytes,
            Err(error) => {
                self.enter_accounting_exhaustion();
                return Err(error);
            }
        };
        let arena_retained_bytes = match self.checked_arena_retained_bytes() {
            Ok(bytes) => bytes,
            Err(error) => {
                self.enter_accounting_exhaustion();
                return Err(error);
            }
        };
        self.retained_bytes = retained_bytes;
        self.arena_retained_bytes = arena_retained_bytes;
        Ok(())
    }
    fn reconcile_after_reservation(
        &mut self,
        _lane: PermanentLane,
    ) -> Result<(), ClosedTypeFinalizeError> {
        #[cfg(test)]
        if self.control.force_capacity_excess_after_reserve
            && matches!(_lane, PermanentLane::PositiveValue)
        {
            self.control.force_capacity_excess_after_reserve = false;
            self.enter_accounting_exhaustion();
            return Err(ClosedTypeFinalizeError::IdentityExhausted);
        }
        self.reconcile_capacity_state()
    }
    fn reserve_scratch_for<T>(
        &mut self,
        lane: fn(&mut Scratch) -> &mut Vec<T>,
        len: usize,
    ) -> Result<(), ClosedTypeFinalizeError> {
        let reservation = {
            let lane = lane(&mut self.scratch);
            (lane.capacity() < len).then(|| lane.try_reserve_exact(len - lane.len()))
        };
        if let Some(reservation) = reservation {
            // Capacity is observable only after the allocator returns.  Do not
            // plan or append another scratch node until the whole session is
            // either reconciled or terminally exhausted.
            self.reconcile_capacity_state()?;
            reservation.map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        }
        Ok(())
    }
    fn record_failed_attempt(&mut self) {
        if matches!(self.accounting, AccountingState::Exhausted) {
            return;
        }
        #[cfg(test)]
        if self.control.force_capacity_excess_during_unwind {
            self.control.force_capacity_excess_during_unwind = false;
            self.enter_accounting_exhaustion();
            return;
        }
        if self.reconcile_capacity_state().is_ok() {
            advance_failure_epoch(&mut self.failure_epoch);
        }
    }
    fn checked_arena_retained_bytes(&self) -> Result<usize, ClosedTypeFinalizeError> {
        fn bytes<T>(lane: &Vec<T>) -> Result<usize, ClosedTypeFinalizeError> {
            lane.capacity()
                .checked_mul(std::mem::size_of::<T>())
                .ok_or(ClosedTypeFinalizeError::IdentityExhausted)
        }
        [
            bytes(&self.arena.positives)?,
            bytes(&self.arena.positive_children)?,
            bytes(&self.arena.negatives)?,
            bytes(&self.arena.negative_children)?,
            bytes(&self.arena.positive_effects)?,
            bytes(&self.arena.negative_effects)?,
            bytes(&self.arena.neutrals)?,
            bytes(&self.arena.recursive_bounds)?,
        ]
        .into_iter()
        .try_fold(0usize, |total, lane| {
            total
                .checked_add(lane)
                .ok_or(ClosedTypeFinalizeError::IdentityExhausted)
        })
    }
    fn checked_retained_bytes(&self) -> Result<usize, ClosedTypeFinalizeError> {
        fn bytes<T>(lane: &Vec<T>) -> Result<usize, ClosedTypeFinalizeError> {
            lane.capacity()
                .checked_mul(std::mem::size_of::<T>())
                .ok_or(ClosedTypeFinalizeError::IdentityExhausted)
        }
        let scratch = [
            bytes(&self.scratch.q)?,
            bytes(&self.scratch.r)?,
            bytes(&self.scratch.p)?,
            bytes(&self.scratch.p_children)?,
            bytes(&self.scratch.n)?,
            bytes(&self.scratch.n_children)?,
            bytes(&self.scratch.pe)?,
            bytes(&self.scratch.ne)?,
            bytes(&self.scratch.neutral)?,
            bytes(&self.scratch.bounds)?,
            bytes(&self.scratch.scheme_bounds)?,
            bytes(&self.scratch.mapped_p)?,
            bytes(&self.scratch.mapped_p_children)?,
            bytes(&self.scratch.mapped_n)?,
            bytes(&self.scratch.mapped_n_children)?,
            bytes(&self.scratch.mapped_neutral)?,
            bytes(&self.scratch.mapped_bounds)?,
        ]
        .into_iter()
        .try_fold(0usize, |total, lane| {
            total
                .checked_add(lane)
                .ok_or(ClosedTypeFinalizeError::IdentityExhausted)
        })?;
        self.checked_arena_retained_bytes()?
            .checked_add(scratch)
            .ok_or(ClosedTypeFinalizeError::IdentityExhausted)
    }
    fn plan(&mut self) -> Result<(), ClosedTypeFinalizeError> {
        let h = self
            .scratch
            .scheme
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)?;
        let base = ArenaLengths::from_arena(&self.arena);
        let p = u32::try_from(base.p).map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        let pc = u32::try_from(base.pc).map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        let n = u32::try_from(base.n).map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        let nc = u32::try_from(base.nc).map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        let pe = u32::try_from(base.pe).map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        let ne = u32::try_from(base.ne).map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        let neutral =
            u32::try_from(base.neutral).map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        let bounds =
            u32::try_from(base.bounds).map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
        checked_end(p, self.scratch.p.len())?;
        checked_end(pc, self.scratch.p_children.len())?;
        checked_end(n, self.scratch.n.len())?;
        checked_end(nc, self.scratch.n_children.len())?;
        checked_end(pe, self.scratch.pe.len())?;
        checked_end(ne, self.scratch.ne.len())?;
        checked_end(neutral, self.scratch.neutral.len())?;
        checked_end(bounds, h.bounds.len as usize)?;
        self.reserve_scratch_for(
            |scratch| &mut scratch.mapped_p_children,
            self.scratch.p_children.len(),
        )?;
        self.reserve_scratch_for(|scratch| &mut scratch.mapped_p, self.scratch.p.len())?;
        self.reserve_scratch_for(
            |scratch| &mut scratch.mapped_n_children,
            self.scratch.n_children.len(),
        )?;
        self.reserve_scratch_for(|scratch| &mut scratch.mapped_n, self.scratch.n.len())?;
        self.reserve_scratch_for(
            |scratch| &mut scratch.mapped_neutral,
            self.scratch.neutral.len(),
        )?;
        self.reserve_scratch_for(|scratch| &mut scratch.mapped_bounds, h.bounds.len as usize)?;
        for &id in &self.scratch.p_children {
            self.scratch.mapped_p_children.push(checked_add(p, id)?);
        }
        for node in &self.scratch.p {
            self.scratch.mapped_p.push(match *node {
                DP::Bottom => PlannedPNode::Bottom,
                DP::Int => PlannedPNode::Int,
                DP::Q(x) => PlannedPNode::Quantified(x),
                DP::R(x) => PlannedPNode::Recursive(x),
                DP::Function { a: x, ae, re, r } => PlannedPNode::Function {
                    a: checked_add(n, x)?,
                    ae: checked_add(ne, ae)?,
                    re: checked_add(pe, re)?,
                    r: checked_add(p, r)?,
                },
                DP::Union(range) => PlannedPNode::Union(DraftRange {
                    start: checked_add(pc, range.start)?,
                    len: range.len,
                }),
            });
        }
        for &id in &self.scratch.n_children {
            self.scratch.mapped_n_children.push(checked_add(n, id)?);
        }
        for node in &self.scratch.n {
            self.scratch.mapped_n.push(match *node {
                DN::Top => PlannedNNode::Top,
                DN::Bottom => PlannedNNode::Bottom,
                DN::Int => PlannedNNode::Int,
                DN::Q(x) => PlannedNNode::Quantified(x),
                DN::R(x) => PlannedNNode::Recursive(x),
                DN::Function { a: x, ae, re, r } => PlannedNNode::Function {
                    a: checked_add(p, x)?,
                    ae: checked_add(pe, ae)?,
                    re: checked_add(ne, re)?,
                    r: checked_add(n, r)?,
                },
                DN::Intersection(range) => PlannedNNode::Intersection(DraftRange {
                    start: checked_add(nc, range.start)?,
                    len: range.len,
                }),
            });
        }
        for &(lower, upper) in &self.scratch.neutral {
            self.scratch.mapped_neutral.push(PlannedNeutralNode {
                lower: checked_add(p, lower)?,
                upper: checked_add(n, upper)?,
            });
        }
        let selected_bounds_end =
            h.bounds
                .start
                .checked_add(h.bounds.len)
                .ok_or(ClosedTypeFinalizeError::IdentityExhausted)? as usize;
        for &selected in &self.scratch.scheme_bounds[h.bounds.start as usize..selected_bounds_end] {
            let bound = self
                .scratch
                .bounds
                .get(selected as usize)
                .ok_or(ClosedTypeFinalizeError::InvalidDraft)?;
            self.scratch.mapped_bounds.push(PlannedBound {
                binder: bound.binder,
                bounds: checked_add(neutral, bound.bounds)?,
            });
        }
        checked_add(p, h.predicate)?;
        checked_end(bounds, h.bounds.len as usize)?;
        Ok(())
    }
    fn reserve(&mut self) -> Result<(), ClosedTypeFinalizeError> {
        for lane in PERMANENT_LANES {
            #[cfg(test)]
            self.before_reserve(finalization_lane(lane), 0)?;
            let reservation = match lane {
                PermanentLane::PositiveChild => reserve(
                    &mut self.arena.positive_children,
                    self.scratch.mapped_p_children.len(),
                ),
                PermanentLane::PositiveValue => {
                    reserve(&mut self.arena.positives, self.scratch.mapped_p.len())
                }
                PermanentLane::NegativeChild => reserve(
                    &mut self.arena.negative_children,
                    self.scratch.mapped_n_children.len(),
                ),
                PermanentLane::NegativeValue => {
                    reserve(&mut self.arena.negatives, self.scratch.mapped_n.len())
                }
                PermanentLane::PositiveEffect => {
                    reserve(&mut self.arena.positive_effects, self.scratch.pe.len())
                }
                PermanentLane::NegativeEffect => {
                    reserve(&mut self.arena.negative_effects, self.scratch.ne.len())
                }
                PermanentLane::NeutralValue => {
                    reserve(&mut self.arena.neutrals, self.scratch.mapped_neutral.len())
                }
                PermanentLane::RecursiveBound => reserve(
                    &mut self.arena.recursive_bounds,
                    self.scratch.mapped_bounds.len(),
                ),
                PermanentLane::SchemeHeader => Ok(()),
            };
            // Vec may retain a larger capacity even on an allocation error.
            // Reconcile the allocator-observed totals before this lane can
            // reach commit, including the error path.
            self.reconcile_after_reservation(lane)?;
            reservation?;
        }
        Ok(())
    }
    #[cfg(test)]
    fn before_reserve(
        &mut self,
        lane: FinalizationLane,
        ordinal: usize,
    ) -> Result<(), ClosedTypeFinalizeError> {
        match self
            .control
            .before(FinalizationFailureEvent::ArenaReserve { lane, ordinal })
        {
            Ok(()) => Ok(()),
            Err(_) => Err(ClosedTypeFinalizeError::IdentityExhausted),
        }
    }
    fn commit(&mut self) -> Result<ClosedValueScheme, ClosedTypeFinalizeError> {
        let h = self
            .scratch
            .scheme
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)?;
        let (arena, scratch) = (&mut self.arena, &mut self.scratch);
        #[cfg(test)]
        let control = &mut self.control;
        #[cfg(test)]
        {
            control.commit_started = true;
        }
        let lengths = ArenaLengths::from_arena(arena);
        let brand = arena.brand;
        let mut rollback = CommitRollback {
            arena,
            lengths,
            committed: false,
        };
        macro_rules! before_write {
            ($lane:ident, $ordinal:expr) => {{
                #[cfg(test)]
                control.before(FinalizationFailureEvent::CommitWrite {
                    lane: FinalizationLane::$lane,
                    ordinal: $ordinal,
                })?;
                #[cfg(not(test))]
                let _ = $ordinal;
            }};
        }
        macro_rules! append {
            ($field:ident, $source:ident, $lane:ident) => {
                for (ordinal, value) in scratch.$source.drain(..).enumerate() {
                    before_write!($lane, ordinal);
                    #[cfg(not(test))]
                    let _ = ordinal;
                    rollback.arena.$field.push(value);
                }
            };
        }
        macro_rules! append_positive_children {
            () => {
                for (ordinal, index) in scratch.mapped_p_children.drain(..).enumerate() {
                    before_write!(PositiveChild, ordinal);
                    #[cfg(test)]
                    control.permanent_handle_write();
                    rollback.arena.positive_children.push(PositiveValueId {
                        arena: brand,
                        index,
                    });
                }
            };
        }
        macro_rules! append_positive_nodes {
            () => {
                for (ordinal, node) in scratch.mapped_p.drain(..).enumerate() {
                    before_write!(PositiveValue, ordinal);
                    #[cfg(test)]
                    control.permanent_handle_write();
                    rollback.arena.positives.push(match node {
                        PlannedPNode::Bottom => PNode::Bottom,
                        PlannedPNode::Int => PNode::Int,
                        PlannedPNode::Quantified(binder) => PNode::Quantified(QuantifierId(binder)),
                        PlannedPNode::Recursive(binder) => {
                            PNode::Recursive(RecursiveBinderId(binder))
                        }
                        PlannedPNode::Function { a, ae, re, r } => PNode::Function {
                            argument: NegativeValueId {
                                arena: brand,
                                index: a,
                            },
                            argument_effect: NegativeEffectId {
                                arena: brand,
                                index: ae,
                            },
                            result_effect: PositiveEffectId {
                                arena: brand,
                                index: re,
                            },
                            result: PositiveValueId {
                                arena: brand,
                                index: r,
                            },
                        },
                        PlannedPNode::Union(range) => PNode::Union {
                            start: range.start,
                            len: range.len,
                        },
                    });
                }
            };
        }
        macro_rules! append_negative_children {
            () => {
                for (ordinal, index) in scratch.mapped_n_children.drain(..).enumerate() {
                    before_write!(NegativeChild, ordinal);
                    #[cfg(test)]
                    control.permanent_handle_write();
                    rollback.arena.negative_children.push(NegativeValueId {
                        arena: brand,
                        index,
                    });
                }
            };
        }
        macro_rules! append_negative_nodes {
            () => {
                for (ordinal, node) in scratch.mapped_n.drain(..).enumerate() {
                    before_write!(NegativeValue, ordinal);
                    #[cfg(test)]
                    control.permanent_handle_write();
                    rollback.arena.negatives.push(match node {
                        PlannedNNode::Top => NNode::Top,
                        PlannedNNode::Bottom => NNode::Bottom,
                        PlannedNNode::Int => NNode::Int,
                        PlannedNNode::Quantified(binder) => NNode::Quantified(QuantifierId(binder)),
                        PlannedNNode::Recursive(binder) => {
                            NNode::Recursive(RecursiveBinderId(binder))
                        }
                        PlannedNNode::Function { a, ae, re, r } => NNode::Function {
                            argument: PositiveValueId {
                                arena: brand,
                                index: a,
                            },
                            argument_effect: PositiveEffectId {
                                arena: brand,
                                index: ae,
                            },
                            result_effect: NegativeEffectId {
                                arena: brand,
                                index: re,
                            },
                            result: NegativeValueId {
                                arena: brand,
                                index: r,
                            },
                        },
                        PlannedNNode::Intersection(range) => NNode::Intersection {
                            start: range.start,
                            len: range.len,
                        },
                    });
                }
            };
        }
        macro_rules! append_neutrals {
            () => {
                for (ordinal, node) in scratch.mapped_neutral.drain(..).enumerate() {
                    before_write!(NeutralValue, ordinal);
                    #[cfg(test)]
                    control.permanent_handle_write();
                    rollback.arena.neutrals.push(NeutralNode {
                        lower: PositiveValueId {
                            arena: brand,
                            index: node.lower,
                        },
                        upper: NegativeValueId {
                            arena: brand,
                            index: node.upper,
                        },
                    });
                }
            };
        }
        macro_rules! append_bounds {
            () => {
                for (ordinal, bound) in scratch.mapped_bounds.drain(..).enumerate() {
                    before_write!(RecursiveBound, ordinal);
                    #[cfg(test)]
                    control.permanent_handle_write();
                    rollback.arena.recursive_bounds.push(ClosedRecursiveBound {
                        binder: RecursiveBinderId(bound.binder),
                        bounds: NeutralValueId {
                            arena: brand,
                            index: bound.bounds,
                        },
                    });
                }
            };
        }
        let mut scheme = None;
        for lane in PERMANENT_LANES {
            match lane {
                PermanentLane::PositiveChild => {
                    append_positive_children!()
                }
                PermanentLane::PositiveValue => append_positive_nodes!(),
                PermanentLane::NegativeChild => {
                    append_negative_children!()
                }
                PermanentLane::NegativeValue => append_negative_nodes!(),
                PermanentLane::PositiveEffect => append!(positive_effects, pe, PositiveEffect),
                PermanentLane::NegativeEffect => append!(negative_effects, ne, NegativeEffect),
                PermanentLane::NeutralValue => append_neutrals!(),
                PermanentLane::RecursiveBound => append_bounds!(),
                PermanentLane::SchemeHeader => {
                    #[cfg(test)]
                    control.before(FinalizationFailureEvent::CommitWrite {
                        lane: finalization_lane(lane),
                        ordinal: 0,
                    })?;
                    #[cfg(test)]
                    control.permanent_handle_write();
                    scheme = Some(ClosedValueScheme {
                        arena: brand,
                        quantifier_count: h.q,
                        recursive_bounds_start: u32::try_from(lengths.bounds)
                            .map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?,
                        recursive_bounds_len: h.bounds.len,
                        predicate: PositiveValueId {
                            arena: brand,
                            index: checked_add(
                                u32::try_from(lengths.p)
                                    .map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?,
                                h.predicate,
                            )?,
                        },
                    });
                }
            }
        }
        rollback.committed = true;
        Ok(scheme.expect("permanent lane sequence constructs the scheme header"))
    }
    #[cfg(test)]
    fn inject_failure(&mut self, event: FinalizationFailureEvent) {
        self.control.fail = Some(event);
    }
    #[cfg(test)]
    fn inject_panic(&mut self, event: FinalizationFailureEvent) {
        self.control.panic = Some(event);
    }
    #[cfg(test)]
    fn inject_terminal_capacity_excess_after_reserve(&mut self) {
        self.control.force_capacity_excess_after_reserve = true;
    }
    #[cfg(test)]
    fn inject_terminal_scratch_capacity_excess_after_reserve(&mut self) {
        self.control.force_scratch_capacity_excess_after_reserve = true;
    }
    #[cfg(test)]
    fn inject_terminal_capacity_excess_during_unwind(&mut self) {
        self.control.force_capacity_excess_during_unwind = true;
    }
    #[cfg(test)]
    fn clear_injection(&mut self) {
        self.control.fail = None;
        self.control.panic = None;
    }
    #[cfg(test)]
    fn test_observation(&self) -> (usize, usize, usize, usize, usize) {
        (
            self.control.attempts,
            self.control.successes,
            self.control.rollbacks,
            self.control.scratch_peak_bytes,
            self.control.capacity_growths,
        )
    }
    #[cfg(test)]
    fn test_events(&self) -> &[FinalizationFailureEvent] {
        &self.control.seen
    }
    #[cfg(test)]
    fn test_lengths(&self) -> ArenaLengths {
        ArenaLengths::from_arena(&self.arena)
    }
    #[cfg(test)]
    fn test_handle_observation(&self) -> (usize, usize) {
        (
            self.control.permanent_handle_writes,
            self.control.permanent_handle_writes_before_commit,
        )
    }
    #[cfg(test)]
    fn test_staging_bytes(&self) -> usize {
        self.scratch.capacity_bytes()
    }
    #[cfg(test)]
    fn test_scratch_pushes(&self) -> usize {
        self.control.scratch_pushes
    }
    #[cfg(test)]
    fn test_retained_bytes(&self) -> usize {
        self.retained_bytes
    }
    #[cfg(test)]
    fn test_failure_epoch(&self) -> u64 {
        self.failure_epoch
    }
}
fn advance_failure_epoch(failure_epoch: &mut u64) {
    // The epoch is private test evidence. Saturation preserves failure ordering
    // without making an accounting boundary panic at its integer limit.
    *failure_epoch = failure_epoch.saturating_add(1);
}
fn enter_accounting_exhaustion(accounting: &mut AccountingState, failure_epoch: &mut u64) {
    if matches!(accounting, AccountingState::Valid) {
        *accounting = AccountingState::Exhausted;
        advance_failure_epoch(failure_epoch);
    }
}
fn reserve<T>(lane: &mut Vec<T>, additional: usize) -> Result<(), ClosedTypeFinalizeError> {
    let required = lane
        .len()
        .checked_add(additional)
        .ok_or(ClosedTypeFinalizeError::IdentityExhausted)?;
    if lane.capacity() >= required {
        return Ok(());
    }
    lane.try_reserve_exact(additional)
        .map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)
}
fn checked_add(base: u32, offset: u32) -> Result<u32, ClosedTypeFinalizeError> {
    base.checked_add(offset)
        .ok_or(ClosedTypeFinalizeError::IdentityExhausted)
}
fn checked_end(base: u32, count: usize) -> Result<(), ClosedTypeFinalizeError> {
    if count == 0 {
        return Ok(());
    }
    let last = u32::try_from(count - 1).map_err(|_| ClosedTypeFinalizeError::IdentityExhausted)?;
    checked_add(base, last).map(|_| ())
}
fn validate(s: &Scratch) -> Result<(), ClosedTypeFinalizeError> {
    let h = s.scheme.ok_or(ClosedTypeFinalizeError::InvalidDraft)?;
    if h.predicate as usize >= s.p.len()
        || h.bounds
            .start
            .checked_add(h.bounds.len)
            .map_or(true, |end| end as usize > s.scheme_bounds.len())
    {
        return Err(ClosedTypeFinalizeError::InvalidDraft);
    }
    for index in h.bounds.start..h.bounds.start + h.bounds.len {
        let bound = *s
            .scheme_bounds
            .get(index as usize)
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)?;
        let entry = s
            .bounds
            .get(bound as usize)
            .ok_or(ClosedTypeFinalizeError::InvalidDraft)?;
        if !s.r.contains(&entry.binder)
            || s.q.contains(&entry.binder)
            || entry.bounds as usize >= s.neutral.len()
            || s.scheme_bounds[h.bounds.start as usize..index as usize]
                .iter()
                .any(|prior| s.bounds[*prior as usize].binder == entry.binder)
        {
            return Err(ClosedTypeFinalizeError::InvalidDraft);
        }
    }
    let listed = |binder| {
        s.scheme_bounds[h.bounds.start as usize..(h.bounds.start + h.bounds.len) as usize]
            .iter()
            .any(|index| s.bounds[*index as usize].binder == binder)
    };
    let qok = |x| x < h.q && s.q.contains(&x);
    let rok = |x| s.r.contains(&x) && listed(x);
    for node in &s.p {
        match *node {
            DP::Q(x) if !qok(x) => return Err(ClosedTypeFinalizeError::InvalidDraft),
            DP::R(x) if !rok(x) => return Err(ClosedTypeFinalizeError::InvalidDraft),
            DP::Union(range)
                if range
                    .start
                    .checked_add(range.len)
                    .map_or(true, |end| end as usize > s.p_children.len()) =>
            {
                return Err(ClosedTypeFinalizeError::InvalidDraft);
            }
            _ => {}
        }
    }
    for node in &s.n {
        match *node {
            DN::Q(x) if !qok(x) => return Err(ClosedTypeFinalizeError::InvalidDraft),
            DN::R(x) if !rok(x) => return Err(ClosedTypeFinalizeError::InvalidDraft),
            DN::Intersection(range)
                if range
                    .start
                    .checked_add(range.len)
                    .map_or(true, |end| end as usize > s.n_children.len()) =>
            {
                return Err(ClosedTypeFinalizeError::InvalidDraft);
            }
            _ => {}
        }
    }
    Ok(())
}

fn alpha_eq(a: ClosedValueSchemeView<'_>, b: ClosedValueSchemeView<'_>) -> bool {
    if a.quantifier_count() != b.quantifier_count()
        || a.recursive_bounds().len() != b.recursive_bounds().len()
    {
        return false;
    }
    let mut q = HashMap::new();
    let mut qr = HashMap::new();
    let mut r = HashMap::new();
    let mut rr = HashMap::new();
    for (x, y) in a.recursive_bounds().iter().zip(b.recursive_bounds()) {
        if !bind(&mut r, &mut rr, x.binder().ordinal(), y.binder().ordinal())
            || !alpha_neutral(
                a,
                b,
                x.bounds(),
                y.bounds(),
                &mut q,
                &mut qr,
                &mut r,
                &mut rr,
            )
        {
            return false;
        }
    }
    alpha_p(
        a,
        b,
        a.predicate(),
        b.predicate(),
        &mut q,
        &mut qr,
        &mut r,
        &mut rr,
    )
}
fn bind(a: &mut HashMap<u32, u32>, b: &mut HashMap<u32, u32>, x: u32, y: u32) -> bool {
    match (a.get(&x), b.get(&y)) {
        (Some(xx), Some(yy)) => *xx == y && *yy == x,
        (None, None) => {
            a.insert(x, y);
            b.insert(y, x);
            true
        }
        _ => false,
    }
}
fn alpha_p(
    l: ClosedValueSchemeView<'_>,
    r: ClosedValueSchemeView<'_>,
    a: PositiveValueId,
    b: PositiveValueId,
    q: &mut HashMap<u32, u32>,
    qr: &mut HashMap<u32, u32>,
    rb: &mut HashMap<u32, u32>,
    rbr: &mut HashMap<u32, u32>,
) -> bool {
    match (l.positive_value(a), r.positive_value(b)) {
        (Ok(PositiveValueView::Bottom), Ok(PositiveValueView::Bottom))
        | (Ok(PositiveValueView::Int), Ok(PositiveValueView::Int)) => true,
        (Ok(PositiveValueView::Quantified(x)), Ok(PositiveValueView::Quantified(y))) => {
            bind(q, qr, x.ordinal(), y.ordinal())
        }
        (Ok(PositiveValueView::Recursive(x)), Ok(PositiveValueView::Recursive(y))) => {
            bind(rb, rbr, x.ordinal(), y.ordinal())
        }
        (
            Ok(PositiveValueView::Function {
                argument: a,
                argument_effect: ae,
                result_effect: re,
                result: ar,
            }),
            Ok(PositiveValueView::Function {
                argument: b,
                argument_effect: be,
                result_effect: bre,
                result: br,
            }),
        ) => {
            alpha_n(l, r, a, b, q, qr, rb, rbr)
                && alpha_ne(l, r, ae, be)
                && alpha_pe(l, r, re, bre)
                && alpha_p(l, r, ar, br, q, qr, rb, rbr)
        }
        (Ok(PositiveValueView::Union(xs)), Ok(PositiveValueView::Union(ys))) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|(x, y)| alpha_p(l, r, *x, *y, q, qr, rb, rbr))
        }
        _ => false,
    }
}
fn alpha_n(
    l: ClosedValueSchemeView<'_>,
    r: ClosedValueSchemeView<'_>,
    a: NegativeValueId,
    b: NegativeValueId,
    q: &mut HashMap<u32, u32>,
    qr: &mut HashMap<u32, u32>,
    rb: &mut HashMap<u32, u32>,
    rbr: &mut HashMap<u32, u32>,
) -> bool {
    match (l.negative_value(a), r.negative_value(b)) {
        (Ok(NegativeValueView::Top), Ok(NegativeValueView::Top))
        | (Ok(NegativeValueView::Bottom), Ok(NegativeValueView::Bottom))
        | (Ok(NegativeValueView::Int), Ok(NegativeValueView::Int)) => true,
        (Ok(NegativeValueView::Quantified(x)), Ok(NegativeValueView::Quantified(y))) => {
            bind(q, qr, x.ordinal(), y.ordinal())
        }
        (Ok(NegativeValueView::Recursive(x)), Ok(NegativeValueView::Recursive(y))) => {
            bind(rb, rbr, x.ordinal(), y.ordinal())
        }
        (
            Ok(NegativeValueView::Function {
                argument: a,
                argument_effect: ae,
                result_effect: re,
                result: ar,
            }),
            Ok(NegativeValueView::Function {
                argument: b,
                argument_effect: be,
                result_effect: bre,
                result: br,
            }),
        ) => {
            alpha_p(l, r, a, b, q, qr, rb, rbr)
                && alpha_pe(l, r, ae, be)
                && alpha_ne(l, r, re, bre)
                && alpha_n(l, r, ar, br, q, qr, rb, rbr)
        }
        (Ok(NegativeValueView::Intersection(xs)), Ok(NegativeValueView::Intersection(ys))) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|(x, y)| alpha_n(l, r, *x, *y, q, qr, rb, rbr))
        }
        _ => false,
    }
}
fn alpha_pe(
    l: ClosedValueSchemeView<'_>,
    r: ClosedValueSchemeView<'_>,
    a: PositiveEffectId,
    b: PositiveEffectId,
) -> bool {
    matches!(
        (l.positive_effect(a), r.positive_effect(b)),
        (
            Ok(PositiveEffectView::Bottom),
            Ok(PositiveEffectView::Bottom)
        )
    )
}
fn alpha_ne(
    l: ClosedValueSchemeView<'_>,
    r: ClosedValueSchemeView<'_>,
    a: NegativeEffectId,
    b: NegativeEffectId,
) -> bool {
    matches!(
        (l.negative_effect(a), r.negative_effect(b)),
        (Ok(NegativeEffectView::Empty), Ok(NegativeEffectView::Empty))
    )
}
fn alpha_neutral(
    l: ClosedValueSchemeView<'_>,
    r: ClosedValueSchemeView<'_>,
    a: NeutralValueId,
    b: NeutralValueId,
    q: &mut HashMap<u32, u32>,
    qr: &mut HashMap<u32, u32>,
    rb: &mut HashMap<u32, u32>,
    rbr: &mut HashMap<u32, u32>,
) -> bool {
    match (l.neutral_value(a), r.neutral_value(b)) {
        (
            Ok(NeutralValueView::Bounds {
                lower: al,
                upper: au,
            }),
            Ok(NeutralValueView::Bounds {
                lower: bl,
                upper: bu,
            }),
        ) => alpha_p(l, r, al, bl, q, qr, rb, rbr) && alpha_n(l, r, au, bu, q, qr, rb, rbr),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bottom<'tx>(
        finalizer: &mut ClosedTypeFinalizer<'tx>,
    ) -> Result<(), ClosedTypeFinalizeError> {
        let predicate = finalizer.positive_bottom()?;
        finalizer.set_scheme(0, &[], predicate)
    }

    fn complete_draft<'tx>(
        finalizer: &mut ClosedTypeFinalizer<'tx>,
    ) -> Result<(), ClosedTypeFinalizeError> {
        let quantifier = finalizer.quantifier(0);
        let recursive = finalizer.recursive_binder(1);
        let quantified_positive = finalizer.positive_quantified(quantifier)?;
        let recursive_positive = finalizer.positive_recursive(recursive)?;
        let quantified_negative = finalizer.negative_quantified(quantifier)?;
        let recursive_negative = finalizer.negative_recursive(recursive)?;
        let negative_int = finalizer.negative_int()?;
        let positive_effect = finalizer.positive_effect_bottom()?;
        let negative_effect = finalizer.negative_effect_empty()?;
        let positive_function = finalizer.positive_function(
            negative_int,
            negative_effect,
            positive_effect,
            recursive_positive,
        )?;
        let negative_function = finalizer.negative_function(
            quantified_positive,
            positive_effect,
            negative_effect,
            recursive_negative,
        )?;
        let predicate = finalizer.positive_union(&[
            quantified_positive,
            recursive_positive,
            positive_function,
        ])?;
        let _intersection = finalizer.negative_intersection(&[
            quantified_negative,
            recursive_negative,
            negative_function,
        ])?;
        let neutral = finalizer.neutral_bounds(recursive_positive, recursive_negative)?;
        let bound = finalizer.recursive_bound(recursive, neutral)?;
        finalizer.set_scheme(1, &[bound], predicate)
    }

    fn two_recursive_bounds<'tx>(
        finalizer: &mut ClosedTypeFinalizer<'tx>,
    ) -> Result<
        (
            DraftRecursiveBound<'tx>,
            DraftRecursiveBound<'tx>,
            DraftPositiveValueId<'tx>,
        ),
        ClosedTypeFinalizeError,
    > {
        let r0 = finalizer.recursive_binder(0);
        let r1 = finalizer.recursive_binder(1);
        let predicate = finalizer.positive_recursive(r0)?;
        let upper = finalizer.negative_top()?;
        let first_neutral = finalizer.neutral_bounds(predicate, upper)?;
        let b0 = finalizer.recursive_bound(r0, first_neutral)?;
        let unused_lower = finalizer.positive_bottom()?;
        let second_neutral = finalizer.neutral_bounds(unused_lower, upper)?;
        let b1 = finalizer.recursive_bound(r1, second_neutral)?;
        Ok((b0, b1, predicate))
    }

    #[test]
    fn session_reuses_staging_and_keeps_prior_scheme_observable() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let bottom = session
            .finalize_scheme(|f| {
                let p = f.positive_bottom()?;
                f.set_scheme(0, &[], p)
            })
            .unwrap();
        let int = session
            .finalize_scheme(|f| {
                let p = f.positive_int()?;
                f.set_scheme(0, &[], p)
            })
            .unwrap();
        let bottom_view = session.scheme_view(bottom.test_scheme()).unwrap();
        let int_view = session.scheme_view(int.test_scheme()).unwrap();
        assert!(matches!(
            bottom_view.positive_value(bottom_view.predicate()),
            Ok(PositiveValueView::Bottom)
        ));
        assert!(matches!(
            int_view.positive_value(int_view.predicate()),
            Ok(PositiveValueView::Int)
        ));
        assert!(!bottom_view.alpha_eq(int_view));
    }

    #[test]
    fn callback_and_validation_failure_publish_no_scheme() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        assert!(matches!(
            session.finalize_scheme(|_| Err(ClosedTypeFinalizeError::InvalidDraft)),
            Err(ClosedTypeFinalizeError::InvalidDraft)
        ));
        assert!(matches!(
            session.finalize_scheme(|f| {
                let q = f.quantifier(1);
                let p = f.positive_quantified(q)?;
                f.set_scheme(1, &[], p)
            }),
            Err(ClosedTypeFinalizeError::InvalidDraft)
        ));
        let scheme = session
            .finalize_scheme(|f| {
                let p = f.positive_bottom()?;
                f.set_scheme(0, &[], p)
            })
            .unwrap();
        assert!(matches!(
            session
                .scheme_view(scheme.test_scheme())
                .unwrap()
                .positive_value(
                    session
                        .scheme_view(scheme.test_scheme())
                        .unwrap()
                        .predicate()
                ),
            Ok(PositiveValueView::Bottom)
        ));
    }

    #[test]
    fn ignored_second_scheme_candidate_poisoned_the_transaction() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        assert!(matches!(
            session.finalize_scheme(|finalizer| {
                let predicate = finalizer.positive_bottom()?;
                finalizer.set_scheme(0, &[], predicate)?;
                let _ignored = finalizer.set_scheme(0, &[], predicate);
                Ok(())
            }),
            Err(ClosedTypeFinalizeError::InvalidDraft)
        ));
        assert_eq!(
            session.test_lengths(),
            ArenaLengths {
                p: 0,
                pc: 0,
                n: 0,
                nc: 0,
                pe: 0,
                ne: 0,
                neutral: 0,
                bounds: 0,
            }
        );
        assert!(session.finalize_scheme(bottom).is_ok());
    }

    #[test]
    fn exhausted_overlay_index_poison_cannot_be_ignored_by_an_infallible_draft_constructor() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let committed = session.finalize_scheme(bottom).unwrap();
        let before = session.test_lengths();
        assert!(matches!(
            session.finalize_scheme(|finalizer| {
                finalizer.inject_lane_length_overflow();
                let _unusable = finalizer.quantifier(0);
                let predicate = finalizer.positive_bottom()?;
                finalizer.set_scheme(0, &[], predicate)
            }),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        ));
        assert_eq!(session.test_lengths(), before);
        let view = session.scheme_view(committed.test_scheme()).unwrap();
        assert!(matches!(
            view.positive_value(view.predicate()),
            Ok(PositiveValueView::Bottom)
        ));
        assert!(session.finalize_scheme(bottom).is_ok());
    }

    #[test]
    fn function_field_order_and_recursive_closure_are_observable() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let scheme = session
            .finalize_scheme(|f| {
                let r = f.recursive_binder(7);
                let lower = f.positive_recursive(r)?;
                let upper = f.negative_top()?;
                let bounds = f.neutral_bounds(lower, upper)?;
                let bound = f.recursive_bound(r, bounds)?;
                let argument = f.negative_int()?;
                let argument_effect = f.negative_effect_empty()?;
                let result_effect = f.positive_effect_bottom()?;
                let result = f.positive_recursive(r)?;
                let predicate =
                    f.positive_function(argument, argument_effect, result_effect, result)?;
                f.set_scheme(0, &[bound], predicate)
            })
            .unwrap();
        let view = session.scheme_view(scheme.test_scheme()).unwrap();
        assert_eq!(view.recursive_bounds().len(), 1);
        assert!(matches!(
            view.positive_value(view.predicate()),
            Ok(PositiveValueView::Function { .. })
        ));
        assert!(view.alpha_eq(view));
    }

    #[test]
    fn scheme_bound_selection_is_subset_ordered_and_duplicate_checked() {
        let mut permutation = ClosedTypeFinalizationSession::try_new().unwrap();
        let reversed = permutation
            .finalize_scheme(|finalizer| {
                let (b0, b1, predicate) = two_recursive_bounds(finalizer)?;
                finalizer.set_scheme(0, &[b1, b0], predicate)
            })
            .unwrap();
        assert_eq!(
            permutation
                .scheme_view(reversed.test_scheme())
                .unwrap()
                .recursive_bounds()
                .iter()
                .map(|bound| bound.binder().ordinal())
                .collect::<Vec<_>>(),
            vec![1, 0]
        );

        let mut subset = ClosedTypeFinalizationSession::try_new().unwrap();
        let selected = subset
            .finalize_scheme(|finalizer| {
                let (b0, _b1, predicate) = two_recursive_bounds(finalizer)?;
                finalizer.set_scheme(0, &[b0], predicate)
            })
            .unwrap();
        assert_eq!(
            subset
                .scheme_view(selected.test_scheme())
                .unwrap()
                .recursive_bounds()
                .iter()
                .map(|bound| bound.binder().ordinal())
                .collect::<Vec<_>>(),
            vec![0]
        );

        let mut duplicate = ClosedTypeFinalizationSession::try_new().unwrap();
        assert!(matches!(
            duplicate.finalize_scheme(|finalizer| {
                let (b0, _b1, predicate) = two_recursive_bounds(finalizer)?;
                finalizer.set_scheme(0, &[b0, b0], predicate)
            }),
            Err(ClosedTypeFinalizeError::InvalidDraft)
        ));
    }

    #[test]
    fn every_injected_finalization_event_rolls_back_and_retry_preserves_committed_handles() {
        let mut probe = ClosedTypeFinalizationSession::try_new().unwrap();
        probe.finalize_scheme(complete_draft).unwrap();
        let events = probe.test_events().to_vec();
        let expected = vec![
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::Quantifier,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::RecursiveBinder,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::PositiveValue,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::PositiveValue,
                ordinal: 1,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NegativeValue,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NegativeValue,
                ordinal: 1,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NegativeValue,
                ordinal: 2,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::PositiveEffect,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NegativeEffect,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::PositiveValue,
                ordinal: 2,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NegativeValue,
                ordinal: 3,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::PositiveChild,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::PositiveChild,
                ordinal: 1,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::PositiveChild,
                ordinal: 2,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::PositiveValue,
                ordinal: 3,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NegativeChild,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NegativeChild,
                ordinal: 1,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NegativeChild,
                ordinal: 2,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NegativeValue,
                ordinal: 4,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::NeutralValue,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::RecursiveBound,
                ordinal: 0,
            },
            FinalizationFailureEvent::OverlayWrite {
                lane: FinalizationLane::SchemeHeader,
                ordinal: 0,
            },
        ];
        let mut expected = expected;
        expected.extend(PERMANENT_LANES.into_iter().map(|lane| {
            FinalizationFailureEvent::ArenaReserve {
                lane: finalization_lane(lane),
                ordinal: 0,
            }
        }));
        expected.extend(
            [
                (FinalizationLane::PositiveChild, 3),
                (FinalizationLane::PositiveValue, 4),
                (FinalizationLane::NegativeChild, 3),
                (FinalizationLane::NegativeValue, 5),
                (FinalizationLane::PositiveEffect, 1),
                (FinalizationLane::NegativeEffect, 1),
                (FinalizationLane::NeutralValue, 1),
                (FinalizationLane::RecursiveBound, 1),
                (FinalizationLane::SchemeHeader, 1),
            ]
            .into_iter()
            .flat_map(|(lane, count)| {
                (0..count)
                    .map(move |ordinal| FinalizationFailureEvent::CommitWrite { lane, ordinal })
            }),
        );
        assert_eq!(
            events, expected,
            "complete-draft finalization event sequence"
        );

        for event in events {
            let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
            let committed = session.finalize_scheme(bottom).unwrap();
            let before = session.test_lengths();
            session.inject_failure(event);
            let expected = match event {
                FinalizationFailureEvent::ArenaReserve { .. } => {
                    ClosedTypeFinalizeError::IdentityExhausted
                }
                FinalizationFailureEvent::OverlayWrite { .. }
                | FinalizationFailureEvent::CommitWrite { .. } => {
                    ClosedTypeFinalizeError::InvalidDraft
                }
            };
            assert!(
                matches!(session.finalize_scheme(complete_draft), Err(error) if error == expected)
            );
            assert_eq!(
                session.test_lengths(),
                before,
                "{event:?} changed logical arena state"
            );
            assert_eq!(session.test_handle_observation().1, 0);
            let view = session.scheme_view(committed.test_scheme()).unwrap();
            assert!(matches!(
                view.positive_value(view.predicate()),
                Ok(PositiveValueView::Bottom)
            ));
            session.clear_injection();
            let retry = session.finalize_scheme(complete_draft).unwrap();
            let mut expected_session = ClosedTypeFinalizationSession::try_new().unwrap();
            let expected_scheme = expected_session.finalize_scheme(complete_draft).unwrap();
            assert!(
                session
                    .scheme_view(committed.test_scheme())
                    .unwrap()
                    .alpha_eq(session.scheme_view(committed.test_scheme()).unwrap())
            );
            assert!(
                session.scheme_view(retry.test_scheme()).unwrap().alpha_eq(
                    expected_session
                        .scheme_view(expected_scheme.test_scheme())
                        .unwrap()
                )
            );
            let (permanent_handle_writes, precommit_handle_writes) =
                session.test_handle_observation();
            assert!(permanent_handle_writes > 0);
            assert_eq!(precommit_handle_writes, 0);
        }
    }

    #[test]
    fn commit_unwind_rolls_back_and_reuses_the_same_flat_staging_lanes() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let committed = session.finalize_scheme(bottom).unwrap();
        let before = session.test_lengths();
        session.inject_panic(FinalizationFailureEvent::CommitWrite {
            lane: FinalizationLane::PositiveValue,
            ordinal: 0,
        });
        assert!(
            catch_unwind(AssertUnwindSafe(|| session.finalize_scheme(complete_draft))).is_err()
        );
        assert_eq!(session.test_lengths(), before);
        assert_eq!(session.test_handle_observation().1, 0);
        assert!(matches!(
            session
                .scheme_view(committed.test_scheme())
                .unwrap()
                .positive_value(
                    session
                        .scheme_view(committed.test_scheme())
                        .unwrap()
                        .predicate()
                ),
            Ok(PositiveValueView::Bottom)
        ));
        session.clear_injection();
        let first = session.finalize_scheme(bottom).unwrap();
        let staging_after_first = session.test_staging_bytes();
        for _ in 0..63 {
            session.finalize_scheme(bottom).unwrap();
            assert_eq!(session.test_staging_bytes(), staging_after_first);
        }
        let before_large = session.test_staging_bytes();
        let larger = session.finalize_scheme(complete_draft).unwrap();
        assert!(session.test_staging_bytes() >= before_large);
        assert!(
            session
                .scheme_view(first.test_scheme())
                .unwrap()
                .alpha_eq(session.scheme_view(first.test_scheme()).unwrap())
        );
        assert!(session.scheme_view(larger.test_scheme()).is_ok());
        let (_attempts, successes, rollbacks, scratch_peak, capacity_growths) =
            session.test_observation();
        assert!(successes >= 65);
        assert!(rollbacks >= 1);
        assert!(scratch_peak >= session.test_staging_bytes());
        assert!(capacity_growths > 0);
    }

    #[test]
    fn later_reservation_failure_retains_earlier_physical_capacity_without_logical_publication() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let committed = session.finalize_scheme(bottom).unwrap();
        let logical_before = session.test_lengths();
        let capacity_before = session.test_retained_bytes();
        session.inject_failure(FinalizationFailureEvent::ArenaReserve {
            lane: FinalizationLane::NegativeValue,
            ordinal: 0,
        });
        assert!(matches!(
            session.finalize_scheme(complete_draft),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        ));
        assert_eq!(session.test_lengths(), logical_before);
        assert!(session.test_retained_bytes() > capacity_before);
        assert!(matches!(
            session
                .scheme_view(committed.test_scheme())
                .unwrap()
                .positive_value(
                    session
                        .scheme_view(committed.test_scheme())
                        .unwrap()
                        .predicate()
                ),
            Ok(PositiveValueView::Bottom)
        ));
        session.clear_injection();
        assert!(session.finalize_scheme(complete_draft).is_ok());
    }

    #[test]
    fn accounting_checkpoints_are_continuous_within_a_success_epoch() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let (_, first) = session.finalize_scheme(bottom).unwrap().into_parts();
        let (_, second) = session
            .finalize_scheme(complete_draft)
            .unwrap()
            .into_parts();
        assert!(first.peak_bytes_during_call() >= first.retained_bytes_before());
        assert!(first.peak_bytes_during_call() >= first.retained_bytes_after());
        assert!(second.peak_bytes_during_call() >= second.retained_bytes_before());
        assert!(second.peak_bytes_during_call() >= second.retained_bytes_after());
        assert_eq!(second.retained_bytes_before(), first.retained_bytes_after());
    }

    #[test]
    fn finish_receipt_drops_staging_but_keeps_the_closed_arena() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let (scheme, checkpoint) = session
            .finalize_scheme(complete_draft)
            .unwrap()
            .into_parts();
        let (arena, receipt) = session.finish().unwrap().into_parts();
        assert_eq!(
            receipt.retained_bytes_before_finish(),
            checkpoint.retained_bytes_after()
        );
        assert!(receipt.retained_bytes_after_finish() <= receipt.retained_bytes_before_finish());
        assert!(arena.scheme_view(&scheme).is_ok());
    }

    #[test]
    fn terminal_actual_capacity_excess_prevents_logical_commit_and_finish() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let lengths_before = session.test_lengths();
        session.inject_terminal_capacity_excess_after_reserve();

        assert!(matches!(
            session.finalize_scheme(complete_draft),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        ));
        assert_eq!(session.test_lengths(), lengths_before);

        let mut callback_ran = false;
        assert!(matches!(
            session.finalize_scheme(|_| {
                callback_ran = true;
                Ok(())
            }),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        ));
        assert!(!callback_ran);
        assert!(matches!(
            session.finish(),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        ));
    }

    #[test]
    fn scratch_terminal_capacity_excess_advances_epoch_once_without_publication() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let lengths_before = session.test_lengths();
        let handles_before = session.test_handle_observation();
        let scratch_pushes_before = session.test_scratch_pushes();
        let epoch_before = session.test_failure_epoch();
        session.inject_terminal_scratch_capacity_excess_after_reserve();

        assert!(matches!(
            session.finalize_scheme(bottom),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        ));
        assert_eq!(session.test_lengths(), lengths_before);
        assert_eq!(session.test_handle_observation(), handles_before);
        assert_eq!(session.test_scratch_pushes(), scratch_pushes_before);
        assert_eq!(session.test_failure_epoch(), epoch_before + 1);
        assert!(
            session
                .test_events()
                .iter()
                .all(|event| !matches!(event, FinalizationFailureEvent::CommitWrite { .. }))
        );

        let mut callback_ran = false;
        assert!(matches!(
            session.finalize_scheme(|_| {
                callback_ran = true;
                Ok(())
            }),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        ));
        assert!(!callback_ran);
        assert_eq!(session.test_failure_epoch(), epoch_before + 1);
        assert!(matches!(
            session.finish(),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        ));
    }

    #[test]
    fn terminal_excess_during_unwind_preserves_the_original_panic() {
        let mut session = ClosedTypeFinalizationSession::try_new().unwrap();
        let lengths_before = session.test_lengths();
        session.inject_panic(FinalizationFailureEvent::CommitWrite {
            lane: FinalizationLane::PositiveValue,
            ordinal: 0,
        });
        session.inject_terminal_capacity_excess_during_unwind();

        let panic = catch_unwind(AssertUnwindSafe(|| session.finalize_scheme(complete_draft)));
        let payload = panic.expect_err("injected commit unwind resumes after rollback");
        assert_eq!(
            payload.downcast_ref::<&str>().copied(),
            Some("injected finalization commit unwind"),
            "terminal reconciliation preserves the original distinguishable panic payload"
        );
        assert_eq!(session.test_lengths(), lengths_before);
        assert_eq!(
            session.test_observation().2,
            1,
            "commit unwind rolls back exactly once before terminal accounting is recorded"
        );
        assert!(matches!(
            session.finish(),
            Err(ClosedTypeFinalizeError::IdentityExhausted)
        ));
    }

    #[test]
    fn checkpoint_public_debug_and_equality_ignore_private_failure_epoch() {
        let earlier = ClosedTypeAccountingCheckpoint {
            retained_bytes_before: 1,
            retained_bytes_after: 2,
            peak_bytes_during_call: 3,
            epoch: 4,
        };
        let later_epoch = ClosedTypeAccountingCheckpoint {
            epoch: 5,
            ..earlier
        };
        assert_eq!(earlier, later_epoch);
        let debug = format!("{earlier:?}");
        assert!(!debug.contains("epoch"));
        assert!(debug.contains("retained_bytes_before"));
    }
}
