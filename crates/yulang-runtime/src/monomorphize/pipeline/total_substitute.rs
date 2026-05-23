use super::type_graph::{
    TypeGraphBuildReport, TypeGraphLowerSnapshotReport, TypeGraphTypeVarLowerReport,
    TypeGraphUpperSupplementReport, build_type_graph,
};
use super::*;

#[derive(Debug, Clone, Default)]
pub(super) struct TotalSubstituteReport {
    pub(super) graph: TypeGraphBuildReport,
    pub(super) lower_snapshot: TypeGraphLowerSnapshotReport,
    pub(super) upper_supplement: TypeGraphUpperSupplementReport,
    pub(super) type_vars: TypeGraphTypeVarLowerReport,
    pub(super) final_defaults: FillHolesReport,
    pub(super) applied_slots: usize,
    pub(super) upper_supplemented_slots: usize,
}

pub(super) fn total_substitute_module_preview(module: &Module) -> TotalSubstituteReport {
    let (type_graph, graph) = build_type_graph(module);
    let lower_solution = type_graph.solve_lower_snapshot();
    let upper_solution = type_graph.solve_upper_supplements(&lower_solution);
    let upper_supplemented_slots = upper_solution.candidate_count();
    let final_defaults = type_graph.solve_final_defaults(&lower_solution, &upper_solution);
    let upper_supplement = upper_solution.report;
    let applied_slots = lower_solution.candidate_count();
    let lower_snapshot = lower_solution.report;
    let type_var_solution = type_graph.solve_type_var_lowers();
    let _recursive_lower_substitutions = type_var_solution.substitution_count();
    let type_vars = type_var_solution.report;
    TotalSubstituteReport {
        graph,
        lower_snapshot,
        upper_supplement,
        type_vars,
        final_defaults,
        applied_slots,
        upper_supplemented_slots,
    }
}
