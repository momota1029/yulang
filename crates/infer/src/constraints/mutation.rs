//! Activation-scoped mutation journal for method-role dirty scheduling.
//!
//! The constraint machine owns the low-level vocabulary and outbox. Higher analysis layers may
//! publish the same typed mutations, but the constraint core never depends on analysis
//! orchestration. Journaling is inactive by default and mutation sites pay only an activation
//! check until a forced method-role pass opens the collector.

use std::cell::Cell;
use std::rc::Rc;

use poly::expr::{DefId, SelectId};
use poly::types::TypeVar;
use rustc_hash::FxHashSet;
use smallvec::SmallVec;

use crate::role_solve::RoleResolutionKey;

pub(crate) type RolePath = Vec<String>;

/// Mutable resources which can affect one method-role owner solve.
///
/// New solver reads must extend this enum and the independent shadow-oracle coverage test before
/// scheduling may treat them as clean.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DependencyKey {
    SccRoot(DefId),
    OwnerRawRoles(DefId),
    OwnerSelections(DefId),
    Selection(SelectId),
    ConstraintBounds(TypeVar),
    ConstraintNeighbors(TypeVar),
    ConstraintSubtractFacts(TypeVar),
    ConstraintLevel(TypeVar),
    ConstraintBirthLevel(TypeVar),
    ConstraintPrePopFamilies(TypeVar),
    #[allow(
        dead_code,
        reason = "Stage 3 emits deterministic method-taint projection diffs"
    )]
    MethodTaint(TypeVar),
    CandidateBucket(RolePath),
    AppliedResolution(RoleResolutionKey),
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct MutationSerial(u64);

impl MutationSerial {
    #[cfg(test)]
    pub(crate) const fn new(value: u64) -> Self {
        Self(value)
    }

    pub(crate) fn checked_next(self) -> Option<Self> {
        self.0.checked_add(1).map(Self)
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct MutationGeneration(u64);

impl MutationGeneration {
    #[cfg(test)]
    pub(crate) const fn new(value: u64) -> Self {
        Self(value)
    }

    pub(crate) fn checked_next(self) -> Option<Self> {
        self.0.checked_add(1).map(Self)
    }
}

#[allow(
    dead_code,
    reason = "the complete fail-closed vocabulary is consumed across Stages 2-4"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum InvalidateAllReason {
    UnrecognizedMutation { site: &'static str },
    JournalOverflow,
    MutationSerialOverflow,
    MutationGenerationOverflow,
    AuditFenceDisagreement { site: &'static str },
    ContractVersionMismatch,
    JournalTruncated,
}

/// Journal item published by an authoritative production mutator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MethodRoleMutation {
    Changed {
        serial: MutationSerial,
        key: DependencyKey,
    },
    InvalidateAll {
        serial: MutationSerial,
        reason: InvalidateAllReason,
    },
}

/// Bounded mutation outbox with a fail-closed coarse generation.
///
/// Stage 5 selects an absolute production cap from measurements. Stage 2 uses an unbounded cap,
/// but records only while a forced method-role pass has activated the outbox.
#[derive(Debug)]
pub(crate) struct MethodRoleMutationOutbox {
    activation: Rc<Cell<bool>>,
    last_serial: MutationSerial,
    generation: MutationGeneration,
    capacity: usize,
    owner_eligibility: bool,
    mutations: Vec<MethodRoleMutation>,
}

impl Clone for MethodRoleMutationOutbox {
    fn clone(&self) -> Self {
        Self {
            activation: Rc::new(Cell::new(false)),
            last_serial: self.last_serial,
            generation: self.generation,
            capacity: self.capacity,
            owner_eligibility: self.owner_eligibility,
            mutations: self.mutations.clone(),
        }
    }
}

impl MethodRoleMutationOutbox {
    pub(crate) fn new() -> Self {
        Self::with_capacity(usize::MAX)
    }

    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            activation: Rc::new(Cell::new(false)),
            last_serial: MutationSerial::default(),
            generation: MutationGeneration::default(),
            capacity,
            owner_eligibility: true,
            mutations: Vec::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn with_state(
        capacity: usize,
        last_serial: MutationSerial,
        generation: MutationGeneration,
    ) -> Self {
        Self {
            activation: Rc::new(Cell::new(false)),
            last_serial,
            generation,
            capacity,
            owner_eligibility: true,
            mutations: Vec::new(),
        }
    }

    /// Begin one forced-pass journal window.
    ///
    /// The returned guard owns no borrow of the outbox, so the solver can mutate it normally. Its
    /// drop path disables recording during unwinding as well as ordinary completion.
    pub(crate) fn activate(&self) -> MethodRoleMutationActivation {
        assert!(
            !self.activation.replace(true),
            "method-role mutation journal must not nest"
        );
        MethodRoleMutationActivation {
            activation: Rc::clone(&self.activation),
            active: true,
        }
    }

    #[inline]
    pub(crate) fn is_active(&self) -> bool {
        self.activation.get()
    }

    pub(crate) fn generation(&self) -> MutationGeneration {
        self.generation
    }

    pub(crate) fn owner_eligibility(&self) -> bool {
        self.owner_eligibility
    }

    #[cfg(test)]
    pub(crate) fn mutations(&self) -> &[MethodRoleMutation] {
        &self.mutations
    }

    pub(crate) fn take(&mut self) -> Vec<MethodRoleMutation> {
        std::mem::take(&mut self.mutations)
    }

    pub(crate) fn record(&mut self, key: DependencyKey) {
        if self.begin_record(1).is_some() {
            let serial = self.last_serial;
            self.mutations
                .push(MethodRoleMutation::Changed { serial, key });
        }
    }

    pub(crate) fn record_many(&mut self, keys: impl IntoIterator<Item = DependencyKey>) {
        if !self.accepts_mutations() {
            return;
        }
        let mut keys = keys.into_iter().collect::<SmallVec<[_; 4]>>();
        if keys.len() <= 8 {
            let mut index = 0;
            while index < keys.len() {
                if keys[..index].contains(&keys[index]) {
                    keys.remove(index);
                } else {
                    index += 1;
                }
            }
        } else {
            let mut seen = FxHashSet::default();
            keys.retain(|key| seen.insert(key.clone()));
        }
        if self.begin_record(keys.len()).is_none() {
            return;
        }
        let serial = self.last_serial;
        self.mutations.extend(
            keys.into_iter()
                .map(|key| MethodRoleMutation::Changed { serial, key }),
        );
    }

    pub(crate) fn drain_into(&mut self, target: &mut Self) -> bool {
        if self.mutations.is_empty() || !target.accepts_mutations() {
            return false;
        }
        let had_mutations = true;
        target.absorb_iter(self.mutations.drain(..));
        had_mutations
    }

    pub(crate) fn audit_generation(
        &mut self,
        before: MutationGeneration,
        observable_changed: bool,
        site: &'static str,
    ) {
        if self.accepts_mutations() && observable_changed && self.generation == before {
            self.fail_closed(InvalidateAllReason::AuditFenceDisagreement { site });
        }
    }

    pub(crate) fn invalidate_all(&mut self, reason: InvalidateAllReason) {
        self.fail_closed(reason);
    }

    #[inline]
    fn accepts_mutations(&self) -> bool {
        self.is_active() && self.owner_eligibility
    }

    fn begin_record(&mut self, key_count: usize) -> Option<()> {
        if !self.accepts_mutations() || key_count == 0 {
            return None;
        }
        let Some(serial) = self.last_serial.checked_next() else {
            self.fail_closed(InvalidateAllReason::MutationSerialOverflow);
            return None;
        };
        let Some(generation) = self.generation.checked_next() else {
            self.fail_closed(InvalidateAllReason::MutationGenerationOverflow);
            return None;
        };
        let Some(next_len) = self.mutations.len().checked_add(key_count) else {
            self.fail_closed(InvalidateAllReason::JournalOverflow);
            return None;
        };
        if next_len > self.capacity {
            self.fail_closed(InvalidateAllReason::JournalOverflow);
            return None;
        }
        self.last_serial = serial;
        self.generation = generation;
        Some(())
    }

    fn absorb_iter(&mut self, mutations: impl IntoIterator<Item = MethodRoleMutation>) {
        let mut pending_serial = None;
        let mut pending_keys = SmallVec::<[DependencyKey; 4]>::new();
        for mutation in mutations {
            match mutation {
                MethodRoleMutation::Changed { serial, key } => {
                    if pending_serial.is_some_and(|pending| pending != serial) {
                        self.record_many(pending_keys.drain(..));
                    }
                    pending_serial = Some(serial);
                    pending_keys.push(key);
                }
                MethodRoleMutation::InvalidateAll { reason, .. } => {
                    self.record_many(pending_keys.drain(..));
                    self.fail_closed(reason);
                    return;
                }
            }
        }
        self.record_many(pending_keys.drain(..));
    }

    fn fail_closed(&mut self, mut reason: InvalidateAllReason) {
        if !self.accepts_mutations() {
            return;
        }
        let serial = match self.last_serial.checked_next() {
            Some(serial) => {
                self.last_serial = serial;
                serial
            }
            None => {
                reason = InvalidateAllReason::MutationSerialOverflow;
                self.last_serial
            }
        };
        match self.generation.checked_next() {
            Some(generation) => self.generation = generation,
            None => reason = InvalidateAllReason::MutationGenerationOverflow,
        }
        self.owner_eligibility = false;
        self.mutations.clear();
        self.mutations
            .push(MethodRoleMutation::InvalidateAll { serial, reason });
    }
}

impl Default for MethodRoleMutationOutbox {
    fn default() -> Self {
        Self::new()
    }
}

/// Non-borrowing activation guard for one outbox.
#[derive(Debug)]
pub(crate) struct MethodRoleMutationActivation {
    activation: Rc<Cell<bool>>,
    active: bool,
}

impl MethodRoleMutationActivation {
    pub(crate) fn finish(mut self) {
        self.deactivate();
    }

    fn deactivate(&mut self) {
        if self.active {
            assert!(
                self.activation.replace(false),
                "method-role mutation journal activation was lost"
            );
            self.active = false;
        }
    }
}

impl Drop for MethodRoleMutationActivation {
    fn drop(&mut self) {
        self.deactivate();
    }
}
