//! Role constraints の raw table と infer-local variance metadata。
//!
//! lowering / annotation から来た role predicate は、まず solver arena 上の `PosId` / `NegId`
//! の不変引数として保持する。compact / role 解決は、この raw constraint を毎回現状の bounds から
//! collect し直して進める。

use std::ops::Deref;

use poly::expr::DefId;
pub use poly::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate, RoleImplTable,
};
use rustc_hash::FxHashMap;

use crate::constraints::mutation::{
    DependencyKey, MethodRoleMutationActivation, MethodRoleMutationOutbox,
    MethodRoleMutationSubscriptions, MutationGeneration,
};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RoleEpoch(u64);

impl RoleEpoch {
    pub fn as_u64(self) -> u64 {
        self.0
    }

    fn bump(&mut self) {
        self.0 = self.0.saturating_add(1);
    }
}

#[derive(Debug, Clone, Default)]
pub struct RoleConstraintTable {
    table: poly::roles::RoleConstraintTable,
    epoch: RoleEpoch,
    owner_epochs: FxHashMap<DefId, RoleEpoch>,
    mutations: MethodRoleMutationOutbox,
}

impl RoleConstraintTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, owner: DefId, constraint: RoleConstraint) {
        let journal_active = self.mutations.is_active();
        let audit = journal_active.then(|| self.mutations.generation());
        self.table.insert(owner, constraint);
        self.epoch.bump();
        self.owner_epochs.insert(owner, self.epoch);
        if let Some(audit) = audit {
            self.mutations.record(DependencyKey::OwnerRawRoles(owner));
            self.mutations
                .audit_generation(audit, true, "RoleConstraintTable::insert");
        }
    }

    pub fn for_owner(&self, owner: DefId) -> &[RoleConstraint] {
        self.table.for_owner(owner)
    }

    pub fn epoch(&self) -> RoleEpoch {
        self.epoch
    }

    pub fn epoch_for_owner(&self, owner: DefId) -> RoleEpoch {
        self.owner_epochs.get(&owner).copied().unwrap_or_default()
    }

    pub(crate) fn activate_method_role_mutations(&self) -> MethodRoleMutationActivation {
        self.mutations.activate()
    }

    pub(crate) fn method_role_mutation_generation(&self) -> MutationGeneration {
        self.mutations.generation()
    }

    pub(crate) fn method_role_mutation_emission_generation(&self) -> MutationGeneration {
        self.mutations.emission_generation()
    }

    pub(crate) fn set_method_role_mutation_subscriptions(
        &mut self,
        subscriptions: MethodRoleMutationSubscriptions,
    ) {
        self.mutations.set_subscriptions(subscriptions);
    }

    pub(crate) fn drain_method_role_mutations_into(
        &mut self,
        target: &mut MethodRoleMutationOutbox,
    ) -> bool {
        self.mutations.drain_into(target)
    }

    #[cfg(test)]
    pub(crate) fn method_role_mutation_journal_active(&self) -> bool {
        self.mutations.is_active()
    }
}

/// Session role candidates plus the authoritative `impl_def -> role bucket` index.
///
/// Read-only deref keeps existing solver calls on the raw table interface. Mutations stay on this
/// wrapper, so candidate registration and prerequisite changes cannot bypass bucket invalidation.
#[derive(Debug, Default)]
pub(crate) struct IndexedRoleImplTable {
    table: RoleImplTable,
    impl_role_buckets: FxHashMap<DefId, Vec<Vec<String>>>,
    mutations: MethodRoleMutationOutbox,
    #[cfg(test)]
    snapshot_characterization_generation: u64,
}

impl IndexedRoleImplTable {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn insert(&mut self, candidate: RoleImplCandidate) {
        #[cfg(test)]
        self.advance_snapshot_characterization_generation();
        let journal_active = self.mutations.is_active();
        let audit = journal_active.then(|| self.mutations.generation());
        let indexed_or_observed_role =
            (candidate.impl_def.is_some() || journal_active).then(|| candidate.role.clone());
        if let Some(impl_def) = candidate.impl_def {
            let role = indexed_or_observed_role
                .as_ref()
                .expect("impl candidates retain their role bucket");
            let buckets = self.impl_role_buckets.entry(impl_def).or_default();
            if !buckets.contains(role) {
                buckets.push(role.clone());
            }
        }
        self.table.insert(candidate);
        if let Some(audit) = audit {
            self.mutations.record(DependencyKey::CandidateBucket(
                indexed_or_observed_role.expect("active journals capture the candidate role"),
            ));
            self.mutations
                .audit_generation(audit, true, "IndexedRoleImplTable::insert");
        }
    }

    pub(crate) fn extend_prerequisites_for_impl(
        &mut self,
        impl_def: DefId,
        prerequisites: impl IntoIterator<Item = RoleConstraint>,
    ) {
        let prerequisites = prerequisites.into_iter().collect::<Vec<_>>();
        if prerequisites.is_empty() {
            return;
        }
        #[cfg(test)]
        self.advance_snapshot_characterization_generation();
        let journal_active = self.mutations.is_active();
        let roles = journal_active.then(|| self.role_buckets_for_impl(impl_def).to_vec());
        let audit = journal_active.then(|| self.mutations.generation());
        self.table
            .extend_prerequisites_for_impl(impl_def, prerequisites);
        if let (Some(roles), Some(audit)) = (roles, audit) {
            let observable_changed = !roles.is_empty();
            self.mutations
                .record_many(roles.into_iter().map(DependencyKey::CandidateBucket));
            self.mutations.audit_generation(
                audit,
                observable_changed,
                "IndexedRoleImplTable::extend_prerequisites_for_impl",
            );
        }
    }

    pub(crate) fn add_method_for_impl(
        &mut self,
        impl_def: DefId,
        requirement: DefId,
        implementation: DefId,
    ) {
        #[cfg(test)]
        self.advance_snapshot_characterization_generation();
        let journal_active = self.mutations.is_active();
        let roles = journal_active.then(|| self.role_buckets_for_impl(impl_def).to_vec());
        let audit = journal_active.then(|| self.mutations.generation());
        self.table
            .add_method_for_impl(impl_def, requirement, implementation);
        if let (Some(roles), Some(audit)) = (roles, audit) {
            let observable_changed = !roles.is_empty();
            // Candidate methods are not read by the current role solver. Conservatively
            // publishing the bucket closes this direct production mutation API for future reads.
            self.mutations
                .record_many(roles.into_iter().map(DependencyKey::CandidateBucket));
            self.mutations.audit_generation(
                audit,
                observable_changed,
                "IndexedRoleImplTable::add_method_for_impl",
            );
        }
    }

    pub(crate) fn role_buckets_for_impl(&self, impl_def: DefId) -> &[Vec<String>] {
        self.impl_role_buckets
            .get(&impl_def)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub(crate) fn activate_method_role_mutations(&self) -> MethodRoleMutationActivation {
        self.mutations.activate()
    }

    pub(crate) fn method_role_mutation_generation(&self) -> MutationGeneration {
        self.mutations.generation()
    }

    pub(crate) fn method_role_mutation_emission_generation(&self) -> MutationGeneration {
        self.mutations.emission_generation()
    }

    pub(crate) fn set_method_role_mutation_subscriptions(
        &mut self,
        subscriptions: MethodRoleMutationSubscriptions,
    ) {
        self.mutations.set_subscriptions(subscriptions);
    }

    pub(crate) fn drain_method_role_mutations_into(
        &mut self,
        target: &mut MethodRoleMutationOutbox,
    ) -> bool {
        self.mutations.drain_into(target)
    }

    #[cfg(test)]
    pub(crate) fn method_role_mutation_journal_active(&self) -> bool {
        self.mutations.is_active()
    }

    #[cfg(test)]
    pub(crate) fn snapshot_characterization_generation(&self) -> u64 {
        self.snapshot_characterization_generation
    }

    #[cfg(test)]
    fn advance_snapshot_characterization_generation(&mut self) {
        self.snapshot_characterization_generation = self
            .snapshot_characterization_generation
            .checked_add(1)
            .expect("test-only candidate generation must not overflow");
    }
}

impl Deref for IndexedRoleImplTable {
    type Target = RoleImplTable;

    fn deref(&self) -> &Self::Target {
        &self.table
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn role_constraint_table_tracks_owner_epoch() {
        let mut table = RoleConstraintTable::new();
        let owner = DefId(0);
        let other = DefId(1);
        let constraint = RoleConstraint {
            role: vec!["Display".into()],
            inputs: Vec::new(),
            associated: Vec::new(),
        };

        assert_eq!(table.epoch().as_u64(), 0);
        assert_eq!(table.epoch_for_owner(owner).as_u64(), 0);

        table.insert(owner, constraint);

        assert!(table.epoch().as_u64() > 0);
        assert_eq!(table.epoch_for_owner(owner), table.epoch());
        assert_eq!(table.epoch_for_owner(other).as_u64(), 0);
    }

    #[test]
    fn snapshot_candidate_generation_covers_every_mutable_table_api() {
        let mut table = IndexedRoleImplTable::new();
        let impl_def = DefId(7);
        let initial = table.snapshot_characterization_generation();
        table.insert(RoleImplCandidate {
            impl_def: Some(impl_def),
            role: vec!["Display".into()],
            inputs: Vec::new(),
            associated: Vec::new(),
            prerequisites: Vec::new(),
            methods: Vec::new(),
        });
        let after_insert = table.snapshot_characterization_generation();
        assert!(
            after_insert > initial,
            "candidate addition/order must advance"
        );

        table.extend_prerequisites_for_impl(
            impl_def,
            [RoleConstraint {
                role: vec!["Prerequisite".into()],
                inputs: Vec::new(),
                associated: Vec::new(),
            }],
        );
        let after_prerequisite = table.snapshot_characterization_generation();
        assert!(
            after_prerequisite > after_insert,
            "recursive prerequisite extension must advance"
        );

        table.add_method_for_impl(impl_def, DefId(8), DefId(9));
        assert!(
            table.snapshot_characterization_generation() > after_prerequisite,
            "the only remaining mutable candidate API is conservatively guarded"
        );
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoleInputVariance {
    Unused,
    Covariant,
    Contravariant,
    Invariant,
}

impl RoleInputVariance {
    pub fn record(self, occurrence: RoleInputOccurrence) -> Self {
        match (self, occurrence) {
            (Self::Invariant, _) | (_, RoleInputOccurrence::Invariant) => Self::Invariant,
            (Self::Unused, RoleInputOccurrence::Covariant) => Self::Covariant,
            (Self::Unused, RoleInputOccurrence::Contravariant) => Self::Contravariant,
            (Self::Covariant, RoleInputOccurrence::Covariant) => Self::Covariant,
            (Self::Contravariant, RoleInputOccurrence::Contravariant) => Self::Contravariant,
            (Self::Covariant, RoleInputOccurrence::Contravariant)
            | (Self::Contravariant, RoleInputOccurrence::Covariant) => Self::Invariant,
        }
    }

    pub fn flipped_for_where(self) -> Self {
        match self {
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
            Self::Unused | Self::Invariant => self,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoleInputOccurrence {
    Covariant,
    Contravariant,
    Invariant,
}

impl RoleInputOccurrence {
    pub fn flipped(self) -> Self {
        match self {
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
            Self::Invariant => Self::Invariant,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct RoleInputVarianceTable {
    variances: FxHashMap<Vec<String>, Vec<RoleInputVariance>>,
}

impl RoleInputVarianceTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, role: impl Into<Vec<String>>, variances: Vec<RoleInputVariance>) {
        self.variances.insert(role.into(), variances);
    }

    pub fn for_role(&self, role: &[String]) -> Option<&[RoleInputVariance]> {
        self.variances.get(role).map(Vec::as_slice)
    }

    pub fn input_or_invariant(&self, role: &[String], index: usize) -> RoleInputVariance {
        self.for_role(role)
            .and_then(|variances| variances.get(index).copied())
            .unwrap_or(RoleInputVariance::Invariant)
    }
}
