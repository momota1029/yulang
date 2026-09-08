//! Source-file facade owns the Root product and frozen-header reconciliation setup.

use crate::{
    OperatorTable, cst_output::CstOutput, cursor::Recover,
    recovery_record::CommittedRecoveryRecord, root_statement::parse_root_statements,
    syntax_kind::SyntaxKind,
};

pub(crate) struct RootCandidate {
    pub(crate) green: rowan::GreenNode,
    pub(crate) committed_recoveries: Vec<CommittedRecoveryRecord>,
}

pub(crate) fn parse_root_candidate(
    source: &str,
    operators: &OperatorTable,
    frozen: &[CommittedRecoveryRecord],
) -> RootCandidate {
    let mut remaining = source;
    let mut recover = Recover::new(operators);
    let mut output = CstOutput::reconcile_scoped(frozen);
    output.start_node(SyntaxKind::Root.into());
    parse_root_statements(source.len(), &mut remaining, &mut recover, &mut output);
    output.finish_node();
    let (green, committed_recoveries) = output.finish_with_recoveries();
    RootCandidate {
        green,
        committed_recoveries,
    }
}
