//! Role constraints の raw table と infer-local variance metadata。
//!
//! lowering / annotation から来た role predicate は、まず solver arena 上の `PosId` / `NegId`
//! の不変引数として保持する。compact / role 解決は、この raw constraint を毎回現状の bounds から
//! collect し直して進める。

use poly::expr::DefId;
pub use poly::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate, RoleImplTable,
};
use rustc_hash::FxHashMap;

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
}

impl RoleConstraintTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, owner: DefId, constraint: RoleConstraint) {
        self.table.insert(owner, constraint);
        self.epoch.bump();
        self.owner_epochs.insert(owner, self.epoch);
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
