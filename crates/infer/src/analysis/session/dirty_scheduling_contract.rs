//! Test contract for owner-level dirty scheduling.
//!
//! Stage 2 promotes the typed vocabulary and activation-scoped outbox to `constraints::mutation`.
//! This independent matrix still describes every effective mutation kind, but it neither makes an
//! owner-skip decision nor duplicates the production journal implementation.

use std::cell::RefCell;

use poly::expr::{DefId, SelectId};
use poly::types::TypeVar;

use crate::compact::CompactRoleConstraint;
pub(crate) use crate::constraints::mutation::DependencyKey;
use crate::constraints::mutation::{
    InvalidateAllReason, MethodRoleMutation, MethodRoleMutationOutbox, MutationGeneration,
    MutationSerial, RolePath,
};
use crate::role_solve::RoleResolutionKey;

impl DependencyKey {
    pub(crate) fn kind(&self) -> DependencyKeyKind {
        match self {
            Self::SccRoot(_) => DependencyKeyKind::SccRoot,
            Self::OwnerRawRoles(_) => DependencyKeyKind::OwnerRawRoles,
            Self::OwnerSelections(_) => DependencyKeyKind::OwnerSelections,
            Self::Selection(_) => DependencyKeyKind::Selection,
            Self::ConstraintBounds(_) => DependencyKeyKind::ConstraintBounds,
            Self::ConstraintNeighbors(_) => DependencyKeyKind::ConstraintNeighbors,
            Self::ConstraintSubtractFacts(_) => DependencyKeyKind::ConstraintSubtractFacts,
            Self::ConstraintLevel(_) => DependencyKeyKind::ConstraintLevel,
            Self::ConstraintBirthLevel(_) => DependencyKeyKind::ConstraintBirthLevel,
            Self::ConstraintPrePopFamilies(_) => DependencyKeyKind::ConstraintPrePopFamilies,
            Self::MethodTaint(_) => DependencyKeyKind::MethodTaint,
            Self::CandidateBucket(_) => DependencyKeyKind::CandidateBucket,
            Self::AppliedResolution(_) => DependencyKeyKind::AppliedResolution,
        }
    }
}

#[repr(usize)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum DependencyKeyKind {
    SccRoot,
    OwnerRawRoles,
    OwnerSelections,
    Selection,
    ConstraintBounds,
    ConstraintNeighbors,
    ConstraintSubtractFacts,
    ConstraintLevel,
    ConstraintBirthLevel,
    ConstraintPrePopFamilies,
    MethodTaint,
    CandidateBucket,
    AppliedResolution,
}

impl DependencyKeyKind {
    pub(crate) const ALL: [Self; 13] = [
        Self::SccRoot,
        Self::OwnerRawRoles,
        Self::OwnerSelections,
        Self::Selection,
        Self::ConstraintBounds,
        Self::ConstraintNeighbors,
        Self::ConstraintSubtractFacts,
        Self::ConstraintLevel,
        Self::ConstraintBirthLevel,
        Self::ConstraintPrePopFamilies,
        Self::MethodTaint,
        Self::CandidateBucket,
        Self::AppliedResolution,
    ];
    pub(crate) const fn index(self) -> usize {
        self as usize
    }
}

/// Effective observable mutation kinds present in the current session implementation.
///
/// These are resource changes, not call sites. A compound call such as upper-bound insertion can
/// perform a bounds change, neighbor transitions, and level lowering; Stage 2 must publish every
/// effective resource change represented here.
#[repr(usize)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum KnownMutationKind {
    LowerBoundAdded,
    UpperBoundAdded,
    EvidenceLowerAdded,
    EvidenceUpperAdded,
    EvidenceLowerPromotedAndRemoved,
    EvidenceUpperPromotedAndRemoved,
    UpperRowPruned,
    RowEffectUpperStoredWithoutReplay,
    NeighborAdded,
    NeighborRemoved,
    ConstraintLevelLowered,
    TypeVarRegistered,
    SubtractFactAdded,
    PrePopFamiliesChanged,
    SelectionAdded,
    SelectionRemoved,
    SelectionReplaced,
    SelectionReparented,
    OwnerRawRoleAdded,
    SccRootRegistered,
    SccOpenComponentRemoved,
    CandidateRegistered,
    CandidatePrerequisitesExtended,
    MethodTaintProjectionChanged,
    AppliedResolutionInserted,
}

impl KnownMutationKind {
    pub(crate) const ALL: [Self; 25] = [
        Self::LowerBoundAdded,
        Self::UpperBoundAdded,
        Self::EvidenceLowerAdded,
        Self::EvidenceUpperAdded,
        Self::EvidenceLowerPromotedAndRemoved,
        Self::EvidenceUpperPromotedAndRemoved,
        Self::UpperRowPruned,
        Self::RowEffectUpperStoredWithoutReplay,
        Self::NeighborAdded,
        Self::NeighborRemoved,
        Self::ConstraintLevelLowered,
        Self::TypeVarRegistered,
        Self::SubtractFactAdded,
        Self::PrePopFamiliesChanged,
        Self::SelectionAdded,
        Self::SelectionRemoved,
        Self::SelectionReplaced,
        Self::SelectionReparented,
        Self::OwnerRawRoleAdded,
        Self::SccRootRegistered,
        Self::SccOpenComponentRemoved,
        Self::CandidateRegistered,
        Self::CandidatePrerequisitesExtended,
        Self::MethodTaintProjectionChanged,
        Self::AppliedResolutionInserted,
    ];
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum KnownMutation {
    LowerBoundAdded {
        var: TypeVar,
    },
    UpperBoundAdded {
        var: TypeVar,
    },
    EvidenceLowerAdded {
        var: TypeVar,
    },
    EvidenceUpperAdded {
        var: TypeVar,
    },
    EvidenceLowerPromotedAndRemoved {
        var: TypeVar,
    },
    EvidenceUpperPromotedAndRemoved {
        var: TypeVar,
    },
    UpperRowPruned {
        source: TypeVar,
    },
    RowEffectUpperStoredWithoutReplay {
        source: TypeVar,
    },
    NeighborAdded {
        left: TypeVar,
        right: TypeVar,
    },
    NeighborRemoved {
        left: TypeVar,
        right: TypeVar,
    },
    ConstraintLevelLowered {
        var: TypeVar,
    },
    TypeVarRegistered {
        var: TypeVar,
    },
    SubtractFactAdded {
        effect: TypeVar,
    },
    PrePopFamiliesChanged {
        var: TypeVar,
    },
    SelectionAdded {
        select: SelectId,
        parent: DefId,
    },
    SelectionRemoved {
        select: SelectId,
        old_parent: DefId,
    },
    SelectionReplaced {
        select: SelectId,
        parent: DefId,
    },
    SelectionReparented {
        select: SelectId,
        old_parent: DefId,
        new_parent: DefId,
    },
    OwnerRawRoleAdded {
        owner: DefId,
    },
    SccRootRegistered {
        owner: DefId,
    },
    SccOpenComponentRemoved {
        owners: Vec<DefId>,
    },
    CandidateRegistered {
        role: RolePath,
    },
    CandidatePrerequisitesExtended {
        candidate_roles: Vec<RolePath>,
    },
    MethodTaintProjectionChanged {
        var: TypeVar,
    },
    AppliedResolutionInserted {
        key: RoleResolutionKey,
    },
}

impl KnownMutation {
    pub(crate) fn kind(&self) -> KnownMutationKind {
        match self {
            Self::LowerBoundAdded { .. } => KnownMutationKind::LowerBoundAdded,
            Self::UpperBoundAdded { .. } => KnownMutationKind::UpperBoundAdded,
            Self::EvidenceLowerAdded { .. } => KnownMutationKind::EvidenceLowerAdded,
            Self::EvidenceUpperAdded { .. } => KnownMutationKind::EvidenceUpperAdded,
            Self::EvidenceLowerPromotedAndRemoved { .. } => {
                KnownMutationKind::EvidenceLowerPromotedAndRemoved
            }
            Self::EvidenceUpperPromotedAndRemoved { .. } => {
                KnownMutationKind::EvidenceUpperPromotedAndRemoved
            }
            Self::UpperRowPruned { .. } => KnownMutationKind::UpperRowPruned,
            Self::RowEffectUpperStoredWithoutReplay { .. } => {
                KnownMutationKind::RowEffectUpperStoredWithoutReplay
            }
            Self::NeighborAdded { .. } => KnownMutationKind::NeighborAdded,
            Self::NeighborRemoved { .. } => KnownMutationKind::NeighborRemoved,
            Self::ConstraintLevelLowered { .. } => KnownMutationKind::ConstraintLevelLowered,
            Self::TypeVarRegistered { .. } => KnownMutationKind::TypeVarRegistered,
            Self::SubtractFactAdded { .. } => KnownMutationKind::SubtractFactAdded,
            Self::PrePopFamiliesChanged { .. } => KnownMutationKind::PrePopFamiliesChanged,
            Self::SelectionAdded { .. } => KnownMutationKind::SelectionAdded,
            Self::SelectionRemoved { .. } => KnownMutationKind::SelectionRemoved,
            Self::SelectionReplaced { .. } => KnownMutationKind::SelectionReplaced,
            Self::SelectionReparented { .. } => KnownMutationKind::SelectionReparented,
            Self::OwnerRawRoleAdded { .. } => KnownMutationKind::OwnerRawRoleAdded,
            Self::SccRootRegistered { .. } => KnownMutationKind::SccRootRegistered,
            Self::SccOpenComponentRemoved { .. } => KnownMutationKind::SccOpenComponentRemoved,
            Self::CandidateRegistered { .. } => KnownMutationKind::CandidateRegistered,
            Self::CandidatePrerequisitesExtended { .. } => {
                KnownMutationKind::CandidatePrerequisitesExtended
            }
            Self::MethodTaintProjectionChanged { .. } => {
                KnownMutationKind::MethodTaintProjectionChanged
            }
            Self::AppliedResolutionInserted { .. } => KnownMutationKind::AppliedResolutionInserted,
        }
    }

    fn dependency_keys(self) -> Vec<DependencyKey> {
        let mut keys = Vec::new();
        match self {
            Self::LowerBoundAdded { var }
            | Self::UpperBoundAdded { var }
            | Self::EvidenceLowerAdded { var }
            | Self::EvidenceUpperAdded { var }
            | Self::EvidenceLowerPromotedAndRemoved { var }
            | Self::EvidenceUpperPromotedAndRemoved { var } => {
                push_unique_key(&mut keys, DependencyKey::ConstraintBounds(var));
            }
            Self::UpperRowPruned { source }
            | Self::RowEffectUpperStoredWithoutReplay { source } => {
                push_unique_key(&mut keys, DependencyKey::ConstraintBounds(source));
            }
            Self::NeighborAdded { left, right } | Self::NeighborRemoved { left, right } => {
                push_unique_key(&mut keys, DependencyKey::ConstraintNeighbors(left));
                push_unique_key(&mut keys, DependencyKey::ConstraintNeighbors(right));
            }
            Self::ConstraintLevelLowered { var } => {
                push_unique_key(&mut keys, DependencyKey::ConstraintLevel(var));
            }
            Self::TypeVarRegistered { var } => {
                push_unique_key(&mut keys, DependencyKey::ConstraintLevel(var));
                push_unique_key(&mut keys, DependencyKey::ConstraintBirthLevel(var));
            }
            Self::SubtractFactAdded { effect } => {
                push_unique_key(&mut keys, DependencyKey::ConstraintSubtractFacts(effect));
            }
            Self::PrePopFamiliesChanged { var } => {
                push_unique_key(&mut keys, DependencyKey::ConstraintPrePopFamilies(var));
            }
            Self::SelectionAdded { select, parent } => {
                push_unique_key(&mut keys, DependencyKey::Selection(select));
                push_unique_key(&mut keys, DependencyKey::OwnerSelections(parent));
            }
            Self::SelectionRemoved { select, old_parent } => {
                push_unique_key(&mut keys, DependencyKey::Selection(select));
                push_unique_key(&mut keys, DependencyKey::OwnerSelections(old_parent));
            }
            Self::SelectionReplaced { select, parent } => {
                push_unique_key(&mut keys, DependencyKey::Selection(select));
                push_unique_key(&mut keys, DependencyKey::OwnerSelections(parent));
            }
            Self::SelectionReparented {
                select,
                old_parent,
                new_parent,
            } => {
                push_unique_key(&mut keys, DependencyKey::Selection(select));
                push_unique_key(&mut keys, DependencyKey::OwnerSelections(old_parent));
                push_unique_key(&mut keys, DependencyKey::OwnerSelections(new_parent));
            }
            Self::OwnerRawRoleAdded { owner } => {
                push_unique_key(&mut keys, DependencyKey::OwnerRawRoles(owner));
            }
            Self::SccRootRegistered { owner } => {
                push_unique_key(&mut keys, DependencyKey::SccRoot(owner));
            }
            Self::SccOpenComponentRemoved { owners } => {
                for owner in owners {
                    push_unique_key(&mut keys, DependencyKey::SccRoot(owner));
                }
            }
            Self::CandidateRegistered { role } => {
                push_unique_key(&mut keys, DependencyKey::CandidateBucket(role));
            }
            Self::CandidatePrerequisitesExtended { candidate_roles } => {
                for role in candidate_roles {
                    push_unique_key(&mut keys, DependencyKey::CandidateBucket(role));
                }
            }
            Self::MethodTaintProjectionChanged { var } => {
                push_unique_key(&mut keys, DependencyKey::MethodTaint(var));
            }
            Self::AppliedResolutionInserted { key } => {
                push_unique_key(&mut keys, DependencyKey::AppliedResolution(key));
            }
        }
        keys
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ContractMutation {
    Known(KnownMutation),
    Unrecognized { site: &'static str },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MutationContractExpectation {
    Changed(Vec<DependencyKey>),
    InvalidateAll(InvalidateAllReason),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MutationContractRow {
    pub(crate) site: &'static str,
    pub(crate) mutation: ContractMutation,
    pub(crate) expected: MutationContractExpectation,
}

impl MutationContractRow {
    fn changed(site: &'static str, mutation: KnownMutation, expected: Vec<DependencyKey>) -> Self {
        Self {
            site,
            mutation: ContractMutation::Known(mutation),
            expected: MutationContractExpectation::Changed(expected),
        }
    }

    fn invalidate_all(site: &'static str, reason: InvalidateAllReason) -> Self {
        Self {
            site,
            mutation: ContractMutation::Unrecognized { site },
            expected: MutationContractExpectation::InvalidateAll(reason),
        }
    }
}

/// Deterministic inventory of current effective mutation kinds and their Stage 2 target events.
pub(crate) fn mutation_contract_matrix() -> Vec<MutationContractRow> {
    let var = TypeVar(10);
    let other_var = TypeVar(11);
    let owner = DefId(20);
    let other_owner = DefId(21);
    let select = SelectId(30);
    let role_a = role_path("RoleA");
    let role_b = role_path("RoleB");
    let applied = sample_role_resolution_key("AppliedRole");

    vec![
        MutationContractRow::changed(
            "TypeBounds::add_lower",
            KnownMutation::LowerBoundAdded { var },
            vec![DependencyKey::ConstraintBounds(var)],
        ),
        MutationContractRow::changed(
            "TypeBounds::add_upper",
            KnownMutation::UpperBoundAdded { var },
            vec![DependencyKey::ConstraintBounds(var)],
        ),
        MutationContractRow::changed(
            "apply_bound_replay_evidence_actions/lower",
            KnownMutation::EvidenceLowerAdded { var },
            vec![DependencyKey::ConstraintBounds(var)],
        ),
        MutationContractRow::changed(
            "apply_bound_replay_evidence_actions/upper",
            KnownMutation::EvidenceUpperAdded { var },
            vec![DependencyKey::ConstraintBounds(var)],
        ),
        MutationContractRow::changed(
            "TypeBounds::add_lower/evidence-promotion",
            KnownMutation::EvidenceLowerPromotedAndRemoved { var },
            vec![DependencyKey::ConstraintBounds(var)],
        ),
        MutationContractRow::changed(
            "TypeBounds::add_upper/evidence-promotion",
            KnownMutation::EvidenceUpperPromotedAndRemoved { var },
            vec![DependencyKey::ConstraintBounds(var)],
        ),
        MutationContractRow::changed(
            "prune_upper_rows_subsumed_by_reduced_upper",
            KnownMutation::UpperRowPruned { source: var },
            vec![DependencyKey::ConstraintBounds(var)],
        ),
        MutationContractRow::changed(
            "row_effect::store_upper_bound_without_replay",
            KnownMutation::RowEffectUpperStoredWithoutReplay { source: var },
            vec![DependencyKey::ConstraintBounds(var)],
        ),
        MutationContractRow::changed(
            "record_var_neighbor/absent-to-present",
            KnownMutation::NeighborAdded {
                left: var,
                right: other_var,
            },
            vec![
                DependencyKey::ConstraintNeighbors(var),
                DependencyKey::ConstraintNeighbors(other_var),
            ],
        ),
        MutationContractRow::changed(
            "unrecord_var_neighbor/present-to-absent",
            KnownMutation::NeighborRemoved {
                left: var,
                right: other_var,
            },
            vec![
                DependencyKey::ConstraintNeighbors(var),
                DependencyKey::ConstraintNeighbors(other_var),
            ],
        ),
        MutationContractRow::changed(
            "TypeLevels::lower_to",
            KnownMutation::ConstraintLevelLowered { var },
            vec![DependencyKey::ConstraintLevel(var)],
        ),
        MutationContractRow::changed(
            "TypeLevels::register",
            KnownMutation::TypeVarRegistered { var },
            vec![
                DependencyKey::ConstraintLevel(var),
                DependencyKey::ConstraintBirthLevel(var),
            ],
        ),
        MutationContractRow::changed(
            "SubtractTable::record",
            KnownMutation::SubtractFactAdded { effect: var },
            vec![DependencyKey::ConstraintSubtractFacts(var)],
        ),
        MutationContractRow::changed(
            "record_pre_pop_effect_families",
            KnownMutation::PrePopFamiliesChanged { var },
            vec![DependencyKey::ConstraintPrePopFamilies(var)],
        ),
        MutationContractRow::changed(
            "register_selection_use/add",
            KnownMutation::SelectionAdded {
                select,
                parent: owner,
            },
            vec![
                DependencyKey::Selection(select),
                DependencyKey::OwnerSelections(owner),
            ],
        ),
        MutationContractRow::changed(
            "remove_unresolved_selection",
            KnownMutation::SelectionRemoved {
                select,
                old_parent: owner,
            },
            vec![
                DependencyKey::Selection(select),
                DependencyKey::OwnerSelections(owner),
            ],
        ),
        MutationContractRow::changed(
            "register_selection_use/replace",
            KnownMutation::SelectionReplaced {
                select,
                parent: owner,
            },
            vec![
                DependencyKey::Selection(select),
                DependencyKey::OwnerSelections(owner),
            ],
        ),
        MutationContractRow::changed(
            "register_selection_use/reparent",
            KnownMutation::SelectionReparented {
                select,
                old_parent: owner,
                new_parent: other_owner,
            },
            vec![
                DependencyKey::Selection(select),
                DependencyKey::OwnerSelections(owner),
                DependencyKey::OwnerSelections(other_owner),
            ],
        ),
        MutationContractRow::changed(
            "RoleConstraintTable::insert",
            KnownMutation::OwnerRawRoleAdded { owner },
            vec![DependencyKey::OwnerRawRoles(owner)],
        ),
        MutationContractRow::changed(
            "SccMachine::register_def",
            KnownMutation::SccRootRegistered { owner },
            vec![DependencyKey::SccRoot(owner)],
        ),
        MutationContractRow::changed(
            "ComponentGraph::remove_ready_component",
            KnownMutation::SccOpenComponentRemoved {
                owners: vec![owner, other_owner],
            },
            vec![
                DependencyKey::SccRoot(owner),
                DependencyKey::SccRoot(other_owner),
            ],
        ),
        MutationContractRow::changed(
            "register_role_impl_candidate",
            KnownMutation::CandidateRegistered {
                role: role_a.clone(),
            },
            vec![DependencyKey::CandidateBucket(role_a.clone())],
        ),
        MutationContractRow::changed(
            "extend_role_impl_prerequisites",
            KnownMutation::CandidatePrerequisitesExtended {
                candidate_roles: vec![role_a.clone(), role_b.clone()],
            },
            vec![
                DependencyKey::CandidateBucket(role_a),
                DependencyKey::CandidateBucket(role_b),
            ],
        ),
        MutationContractRow::changed(
            "method-taint deterministic projection diff",
            KnownMutation::MethodTaintProjectionChanged { var },
            vec![DependencyKey::MethodTaint(var)],
        ),
        MutationContractRow::changed(
            "applied_method_role_resolutions::insert",
            KnownMutation::AppliedResolutionInserted {
                key: applied.clone(),
            },
            vec![DependencyKey::AppliedResolution(applied)],
        ),
        MutationContractRow::invalidate_all(
            "unrecognized mutation fallback",
            InvalidateAllReason::UnrecognizedMutation {
                site: "unrecognized mutation fallback",
            },
        ),
    ]
}

/// Bounded test journal which proves recognized mutations cannot fall through silently.
#[derive(Debug)]
pub(crate) struct MutationContractHarness {
    last_serial: MutationSerial,
    capacity: usize,
    failed_closed: bool,
    journal: Vec<MethodRoleMutation>,
}

impl MutationContractHarness {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            last_serial: MutationSerial::default(),
            capacity,
            failed_closed: false,
            journal: Vec::new(),
        }
    }

    #[cfg(test)]
    fn with_last_serial(capacity: usize, last_serial: MutationSerial) -> Self {
        Self {
            last_serial,
            capacity,
            failed_closed: false,
            journal: Vec::new(),
        }
    }

    pub(crate) fn record(&mut self, mutation: ContractMutation) -> Vec<MethodRoleMutation> {
        if self.failed_closed {
            return self.journal.clone();
        }
        let Some(serial) = self.last_serial.checked_next() else {
            return self.invalidate_all(
                self.last_serial,
                InvalidateAllReason::MutationSerialOverflow,
            );
        };
        self.last_serial = serial;

        let events = match mutation {
            ContractMutation::Known(mutation) => mutation
                .dependency_keys()
                .into_iter()
                .map(|key| MethodRoleMutation::Changed { serial, key })
                .collect::<Vec<_>>(),
            ContractMutation::Unrecognized { site } => {
                return self
                    .invalidate_all(serial, InvalidateAllReason::UnrecognizedMutation { site });
            }
        };
        let Some(next_len) = self.journal.len().checked_add(events.len()) else {
            return self.invalidate_all(serial, InvalidateAllReason::JournalOverflow);
        };
        if next_len > self.capacity {
            return self.invalidate_all(serial, InvalidateAllReason::JournalOverflow);
        }
        self.journal.extend(events.iter().cloned());
        events
    }

    pub(crate) fn journal(&self) -> &[MethodRoleMutation] {
        &self.journal
    }

    fn invalidate_all(
        &mut self,
        serial: MutationSerial,
        reason: InvalidateAllReason,
    ) -> Vec<MethodRoleMutation> {
        let event = MethodRoleMutation::InvalidateAll { serial, reason };
        self.failed_closed = true;
        self.journal.clear();
        self.journal.push(event.clone());
        vec![event]
    }
}

/// Session-owned read recorder prototype for the six constraint reads and explicit solve reads.
///
/// This is ordinary session-local state, not TLS. Inactive reads allocate nothing and record
/// nothing. It accepts only already-observed typed keys, so it has no API for reconstructing or
/// polling a complete owner fingerprint before an eligibility decision.
#[derive(Debug, Default)]
pub(crate) struct SessionLocalOwnerReadCollector {
    active: RefCell<Option<CapturedOwnerReads>>,
}

impl SessionLocalOwnerReadCollector {
    pub(crate) fn activate(&self) -> OwnerReadCapture<'_> {
        assert!(
            self.active
                .borrow_mut()
                .replace(CapturedOwnerReads::default())
                .is_none(),
            "owner read capture must not nest"
        );
        OwnerReadCapture {
            collector: self,
            active: true,
        }
    }

    pub(crate) fn record(&self, key: DependencyKey) {
        let mut active = self.active.borrow_mut();
        let Some(reads) = active.as_mut() else {
            return;
        };
        reads.insert(key);
    }

    pub(crate) fn record_constraint_bounds(&self, var: TypeVar) {
        self.record(DependencyKey::ConstraintBounds(var));
    }

    pub(crate) fn record_constraint_neighbors(&self, var: TypeVar) {
        self.record(DependencyKey::ConstraintNeighbors(var));
    }

    pub(crate) fn record_constraint_subtract_facts(&self, var: TypeVar) {
        self.record(DependencyKey::ConstraintSubtractFacts(var));
    }

    pub(crate) fn record_constraint_level(&self, var: TypeVar) {
        self.record(DependencyKey::ConstraintLevel(var));
    }

    pub(crate) fn record_constraint_birth_level(&self, var: TypeVar) {
        self.record(DependencyKey::ConstraintBirthLevel(var));
    }

    pub(crate) fn record_constraint_pre_pop_families(&self, var: TypeVar) {
        self.record(DependencyKey::ConstraintPrePopFamilies(var));
    }

    fn take_active(&self) -> CapturedOwnerReads {
        self.active
            .borrow_mut()
            .take()
            .expect("owner read capture must be active")
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct CapturedOwnerReads {
    dependencies: Vec<DependencyKey>,
}

impl CapturedOwnerReads {
    pub(crate) fn dependencies(&self) -> &[DependencyKey] {
        &self.dependencies
    }

    fn insert(&mut self, key: DependencyKey) {
        push_unique_key(&mut self.dependencies, key);
    }
}

pub(crate) struct OwnerReadCapture<'a> {
    collector: &'a SessionLocalOwnerReadCollector,
    active: bool,
}

impl OwnerReadCapture<'_> {
    pub(crate) fn finish(mut self) -> CapturedOwnerReads {
        let reads = self.collector.take_active();
        self.active = false;
        reads
    }
}

impl Drop for OwnerReadCapture<'_> {
    fn drop(&mut self) {
        if self.active {
            self.collector.active.borrow_mut().take();
        }
    }
}

fn push_unique_key(keys: &mut Vec<DependencyKey>, key: DependencyKey) {
    if !keys.contains(&key) {
        keys.push(key);
    }
}

fn role_path(name: &str) -> RolePath {
    vec![name.to_owned()]
}

fn sample_role_resolution_key(name: &str) -> RoleResolutionKey {
    let demand = CompactRoleConstraint {
        role: role_path(name),
        inputs: Vec::new(),
        associated: Vec::new(),
    };
    RoleResolutionKey {
        demand: demand.clone(),
        candidate: demand,
    }
}

#[cfg(test)]
mod tests;
