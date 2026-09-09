//! Source-file facade owns the Root product and frozen-header reconciliation setup.

use crate::{OperatorTable, recovery_record::CommittedRecoveryRecord};

pub(crate) struct RootCandidate {
    pub(crate) green: rowan::GreenNode,
    pub(crate) committed_recoveries: Vec<CommittedRecoveryRecord>,
}

pub(crate) fn parse_root_candidate(
    source: &str,
    operators: &OperatorTable,
    frozen: &[CommittedRecoveryRecord],
) -> RootCandidate {
    crate::cursor::parse_root(source, operators, frozen)
}
