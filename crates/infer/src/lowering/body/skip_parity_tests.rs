use super::*;

use super::stage0_tests::{fixture_source, repository_std_loaded};
use crate::analysis::{
    with_owner_dirty_scheduler_skips_for_new_sessions, with_shadow_dirty_oracle_for_new_sessions,
};
use poly::expr::SelectId;

#[test]
fn stage4_markdown_scheduled_compile_matches_always_solve() {
    assert_paired_source(
        "markdown",
        &fixture_source("std_prefix_yumark_markdown_workload.yu"),
    );
}

#[test]
fn stage4_html_scheduled_compile_matches_always_solve() {
    assert_paired_source(
        "html",
        &fixture_source("std_prefix_yumark_html_fallback.yu"),
    );
}

#[test]
fn stage4_repository_std_scheduled_compile_matches_always_solve() {
    assert_paired_source("repository-std-only", "use std::prelude::*\nmod std;\n");
}

#[test]
fn stage4_showcase_scheduled_compile_matches_always_solve() {
    let showcase = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("examples/showcase.yu"),
    )
    .expect("read repository showcase");
    assert_paired_source(
        "repository-showcase",
        &format!("use std::prelude::*\nmod std;\n{showcase}"),
    );
}

#[test]
fn stage4_early_fallback_real_std_census_matches_with_scheduling() {
    let loaded = repository_std_loaded("use std::prelude::*\nmod std;\n");
    let production = lower_loaded_files_with_early_resolution(&loaded, false);
    let always = with_shadow_dirty_oracle_for_new_sessions(|| {
        lower_loaded_files_with_early_resolution(&loaded, true)
    });
    let scheduled = with_shadow_dirty_oracle_for_new_sessions(|| {
        with_owner_dirty_scheduler_skips_for_new_sessions(|| {
            lower_loaded_files_with_early_resolution(&loaded, true)
        })
    });

    assert_early_fallback_census("always-solve", &loaded, &production, &always);
    assert_early_fallback_census("scheduled", &loaded, &production, &scheduled);
    assert_paired_lowering("early-fallback-real-std", always, scheduled);
}

#[test]
fn stage4_rename_and_module_move_variants_keep_structured_scheduling() {
    let renamed_from = paired_source_witness(
        "metamorphic-rename-before",
        concat!(
            "use std::prelude::*\n",
            "mod std;\n",
            "mod container:\n",
            "  pub value = 1\n",
            "my selected = container::value\n",
        ),
    );
    let renamed_to = paired_source_witness(
        "metamorphic-rename-after",
        concat!(
            "use std::prelude::*\n",
            "mod std;\n",
            "mod container:\n",
            "  pub renamed = 1\n",
            "my selected = container::renamed\n",
        ),
    );
    let moved = paired_source_witness(
        "metamorphic-module-move",
        concat!(
            "use std::prelude::*\n",
            "mod std;\n",
            "mod moved:\n",
            "  pub value = 1\n",
            "my selected = moved::value\n",
        ),
    );

    assert_eq!(renamed_to.resolved_refs, renamed_from.resolved_refs);
    assert_eq!(moved.resolved_refs, renamed_from.resolved_refs);
    assert_eq!(renamed_to.scheduler_counts, renamed_from.scheduler_counts);
    assert_eq!(moved.scheduler_counts, renamed_from.scheduler_counts);
}

fn assert_paired_source(case: &str, source: &str) {
    let _ = paired_source_witness(case, source);
}

fn paired_source_witness(case: &str, source: &str) -> PairedSourceWitness {
    let loaded = repository_std_loaded(source);
    let always = with_shadow_dirty_oracle_for_new_sessions(|| {
        lower_loaded_files(&loaded).expect("lower always-solve Stage 4 fixture")
    });
    let scheduled = with_shadow_dirty_oracle_for_new_sessions(|| {
        with_owner_dirty_scheduler_skips_for_new_sessions(|| {
            lower_loaded_files(&loaded).expect("lower scheduled Stage 4 fixture")
        })
    });
    let scheduler = scheduled
        .session
        .owner_dirty_scheduler_report()
        .expect("scheduled pair must carry a scheduler report");
    let witness = PairedSourceWitness {
        resolved_refs: scheduled.session.poly.refs().to_vec(),
        scheduler_counts: (
            scheduler.forced_passes,
            scheduler.owner_checks,
            scheduler.real_solves,
            scheduler.clean_skips,
            scheduler.changed_mutations,
        ),
    };
    assert_paired_lowering(case, always, scheduled);
    witness
}

#[derive(Debug, PartialEq, Eq)]
struct PairedSourceWitness {
    resolved_refs: Vec<Option<DefId>>,
    scheduler_counts: (usize, usize, usize, usize, usize),
}

fn lower_loaded_files_with_early_resolution(files: &[LoadedFile], enabled: bool) -> BodyLowering {
    let loaded = LoadedFileCsts::new(files).expect("index early-fallback Stage 4 files");
    let lower =
        lower_loaded_file_csts_module_map(&loaded).expect("lower early-fallback module map");
    let mut lowerer = BodyLowerer::new(lower);
    lowerer.set_candidate_independent_fallback_early_resolution_enabled(enabled);
    for file in loaded.by_depth() {
        let module = lowerer
            .modules
            .module_by_path(&file.module_path)
            .expect("loaded early-fallback module path");
        let previous_source_file =
            std::mem::replace(&mut lowerer.source_file, file.module_path.clone());
        lowerer.lower_block(&file.cst, module);
        lowerer.source_file = previous_source_file;
    }
    lowerer.lower_synthetic_act_copy_bodies_for_test();
    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    lowerer.finish()
}

fn assert_early_fallback_census(
    mode: &str,
    files: &[LoadedFile],
    production: &BodyLowering,
    early: &BodyLowering,
) {
    use crate::role_impl_conformance::{
        ActualMethodConformanceView, ActualMethodConformanceViewUnavailable,
        RoleImplMethodActualSurface, RoleImplMethodProvision,
    };

    assert!(
        production.errors.is_empty(),
        "{mode}: {:?}",
        production.errors
    );
    assert_eq!(
        early.errors, production.errors,
        "{mode}: diagnostics changed"
    );
    let infix = repository_std_infix_method_defs(
        files,
        &production.modules,
        production.role_impl_conformance_contracts(),
    );
    assert_eq!(infix.len(), 21, "{mode}: infix-method census drifted");

    let mut explicit = 0usize;
    let mut captured = 0usize;
    let mut helped = Vec::new();
    for contract in production.role_impl_conformance_contracts() {
        let early_contract = early
            .role_impl_conformance_contracts()
            .iter()
            .find(|candidate| candidate.impl_def == contract.impl_def)
            .expect("matching early-fallback contract");
        for method in &contract.methods {
            let RoleImplMethodProvision::Explicit { implementations } = &method.provision else {
                continue;
            };
            for implementation in implementations {
                explicit += 1;
                let before = contract.actual_method_view(implementation.def);
                let after = early_contract.actual_method_view(implementation.def);
                assert_eq!(before.is_some(), after.is_some(), "{mode}");
                let (Some(before), Some(after)) = (before, after) else {
                    continue;
                };
                captured += 1;
                if before.surface != after.surface {
                    assert!(
                        infix.contains(&implementation.def),
                        "{mode}: non-infix method changed: {:?}",
                        implementation.def,
                    );
                    helped.push(implementation.def);
                }
            }
        }
    }
    helped.sort_by_key(|def| def.0);
    assert_eq!(explicit, 133, "{mode}: explicit method census drifted");
    assert_eq!(captured, 129, "{mode}: captured method census drifted");
    assert_eq!(helped.len(), 7, "{mode}: helped-method census drifted");

    let parse_error = production
        .role_impl_conformance_contracts()
        .iter()
        .find(|contract| {
            contract
                .role
                .ends_with(&["text".into(), "parse".into(), "ParseError".into()])
        })
        .expect("ParseError contract");
    let early_parse_error = early
        .role_impl_conformance_contracts()
        .iter()
        .find(|contract| contract.impl_def == parse_error.impl_def)
        .expect("early ParseError contract");
    let merge = parse_error
        .methods
        .iter()
        .find(|method| method.name == "merge")
        .expect("ParseError.merge");
    let RoleImplMethodProvision::Explicit { implementations } = &merge.provision else {
        panic!("ParseError.merge must remain explicit")
    };
    let [implementation] = implementations.as_slice() else {
        panic!("ParseError.merge must retain one implementation")
    };
    let RoleImplMethodActualSurface::Receiver(before) = &parse_error
        .actual_method_view(implementation.def)
        .expect("production ParseError.merge view")
        .surface
    else {
        panic!("ParseError.merge must remain a receiver method")
    };
    let RoleImplMethodActualSurface::Receiver(after) = &early_parse_error
        .actual_method_view(implementation.def)
        .expect("early ParseError.merge view")
        .surface
    else {
        panic!("early ParseError.merge must remain a receiver method")
    };
    assert_eq!(
        before.value,
        ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::OrdinarySccBlocker,
        ),
        "{mode}: production ParseError.merge behavior drifted",
    );
    assert_eq!(
        after.value,
        ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::NonAtomicSurface,
        ),
        "{mode}: early ParseError.merge behavior drifted",
    );
}

fn repository_std_infix_method_defs(
    files: &[LoadedFile],
    modules: &ModuleTable,
    contracts: &[crate::role_impl_conformance::RoleImplConformanceContract],
) -> FxHashSet<DefId> {
    let loaded = LoadedFileCsts::new(files).expect("index repository std census files");
    let mut infix = FxHashSet::default();
    for contract in contracts {
        for method in &contract.methods {
            let crate::role_impl_conformance::RoleImplMethodProvision::Explicit { implementations } =
                &method.provision
            else {
                continue;
            };
            for implementation in implementations {
                let span = modules
                    .def_source_span(implementation.def)
                    .expect("repository std method source span");
                let file = loaded
                    .by_depth()
                    .find(|file| file.module_path == span.file)
                    .expect("repository std method source file");
                let binding = file
                    .cst
                    .descendants()
                    .filter(|node| node.kind() == parser::lex::SyntaxKind::Binding)
                    .filter(|node| {
                        let range = node.text_range();
                        u32::from(range.start()) as usize <= span.range.start
                            && u32::from(range.end()) as usize >= span.range.end
                    })
                    .min_by_key(|node| node.text_range().len());
                if binding.is_some_and(|binding| {
                    binding
                        .descendants()
                        .any(|node| node.kind() == parser::lex::SyntaxKind::InfixNode)
                }) {
                    infix.insert(implementation.def);
                }
            }
        }
    }
    infix
}

fn assert_paired_lowering(case: &str, mut always: BodyLowering, mut scheduled: BodyLowering) {
    let always_oracle = always
        .session
        .shadow_dirty_oracle_report()
        .expect("always-solve pair must retain the independent exact oracle");
    assert!(
        always_oracle.mismatches.is_empty(),
        "{case}: independent always-solve oracle mismatch: {:#?}",
        always_oracle.mismatches,
    );
    assert_eq!(
        always_oracle.root_unavailable_outcomes
            + always_oracle.no_progress_outcomes
            + always_oracle.progress_outcomes,
        always_oracle.owner_checks,
        "{case}: always-solve oracle must observe every real owner solve",
    );

    let scheduled_oracle = scheduled
        .session
        .shadow_dirty_oracle_report()
        .expect("scheduled pair must retain the independent exact oracle");
    assert!(
        scheduled_oracle.mismatches.is_empty(),
        "{case}: independent scheduled oracle mismatch: {:#?}",
        scheduled_oracle.mismatches,
    );
    let scheduler = scheduled
        .session
        .owner_dirty_scheduler_report()
        .expect("scheduled pair must carry the journal scheduler");
    assert!(
        scheduler.clean_skips > 0,
        "{case}: no owner solve was skipped"
    );
    assert_eq!(
        scheduler.real_solves + scheduler.clean_skips,
        scheduler.owner_checks,
        "{case}: each owner check must be exactly one real solve or terminal reuse",
    );
    assert!(
        scheduler.mismatches.is_empty(),
        "{case}: journal terminal mismatch: {:#?}",
        scheduler.mismatches,
    );
    assert!(
        scheduler.permissive_divergences.is_empty(),
        "{case}: journal scheduler was more permissive than the exact oracle: {:#?}",
        scheduler.permissive_divergences,
    );

    let always = SemanticParitySnapshot::capture(&mut always);
    let scheduled = SemanticParitySnapshot::capture(&mut scheduled);
    always.assert_eq(case, &scheduled);
}

struct SemanticParitySnapshot {
    finalized_schemes: Vec<(DefId, String, String)>,
    infer_role_candidates: Vec<String>,
    poly_role_candidates: Vec<String>,
    unresolved_selections: Vec<(SelectId, SelectionUse)>,
    scc_outcomes: Vec<(DefId, bool, Option<TypeVar>, String)>,
    scc_stats: crate::scc::SccStats,
    scc_events: Vec<crate::scc::SccEvent>,
    lowering_errors: Vec<BodyLoweringError>,
    diagnostics: crate::check::PolyCheckReport,
    role_impl_conformance: Vec<crate::role_impl_conformance::RoleImplConformanceContract>,
    poly_dump: String,
    poly_raw_dump: String,
    namespace: crate::CompiledNamespaceSurface,
    lowering_surface: crate::CompiledLoweringSurface,
    runtime_arena_dump: String,
    runtime_raw_arena_dump: String,
    runtime_boundary: crate::CompiledBoundaryInterface,
    runtime_labels: DumpLabels,
    runtime_modules: Vec<crate::CompiledRuntimeModuleDef>,
    runtime_values: Vec<crate::CompiledRuntimeValueDef>,
}

impl SemanticParitySnapshot {
    fn capture(output: &mut BodyLowering) -> Self {
        let finalized_schemes = finalized_scheme_snapshot(output);
        let infer_role_candidates = role_candidate_snapshot(
            output.session.infer.constraints().types(),
            output.session.role_impls.iter(),
        );
        let poly_role_candidates = role_candidate_snapshot(
            &output.session.poly.typ,
            output.session.poly.role_impls.iter(),
        );
        let mut unresolved_selections = output
            .session
            .selections
            .iter()
            .map(|(select, use_site)| (select, *use_site))
            .collect::<Vec<_>>();
        unresolved_selections.sort_by_key(|(select, _)| select.0);

        let mut defs = output
            .session
            .poly
            .defs
            .iter()
            .map(|(def, _)| def)
            .collect::<Vec<_>>();
        defs.sort_by_key(|def| def.0);
        let scc_outcomes = defs
            .into_iter()
            .map(|def| {
                (
                    def,
                    output.session.scc.is_quantified(def),
                    output.session.scc.root_of(def),
                    format!("{:?}", output.session.scc.fetch_of(def)),
                )
            })
            .collect();
        let scc_stats = output.session.scc.stats();

        let lowering_errors = output.errors.clone();
        let diagnostics = crate::check::summarize_lowering(output);
        let role_impl_conformance = output.role_impl_conformance_contracts().to_vec();
        let poly_dump = poly::dump::dump_arena_with_labels(&output.session.poly, &output.labels);
        let poly_raw_dump =
            poly::dump::dump_arena_raw_with_labels(&output.session.poly, &output.labels);
        let namespace = crate::CompiledNamespaceSurface::from_module_table(&output.modules);
        let lowering_surface =
            crate::CompiledLoweringSurface::from_module_table(&output.modules, &namespace);
        let runtime =
            crate::CompiledRuntimeSurface::from_lowering_with_namespace(output, &namespace);
        let runtime_arena_dump =
            poly::dump::dump_arena_with_labels(&runtime.arena, &runtime.labels);
        let runtime_raw_arena_dump =
            poly::dump::dump_arena_raw_with_labels(&runtime.arena, &runtime.labels);
        let scc_events = output.session.take_scc_events();

        Self {
            finalized_schemes,
            infer_role_candidates,
            poly_role_candidates,
            unresolved_selections,
            scc_outcomes,
            scc_stats,
            scc_events,
            lowering_errors,
            diagnostics,
            role_impl_conformance,
            poly_dump,
            poly_raw_dump,
            namespace,
            lowering_surface,
            runtime_arena_dump,
            runtime_raw_arena_dump,
            runtime_boundary: runtime.boundary,
            runtime_labels: runtime.labels,
            runtime_modules: runtime.modules,
            runtime_values: runtime.values,
        }
    }

    fn assert_eq(&self, case: &str, scheduled: &Self) {
        assert_eq!(
            scheduled.finalized_schemes, self.finalized_schemes,
            "{case}: finalized schemes diverged"
        );
        assert_eq!(
            scheduled.infer_role_candidates, self.infer_role_candidates,
            "{case}: infer role candidates diverged"
        );
        assert_eq!(
            scheduled.poly_role_candidates, self.poly_role_candidates,
            "{case}: finalized role candidates diverged"
        );
        assert_eq!(
            scheduled.unresolved_selections, self.unresolved_selections,
            "{case}: unresolved selections diverged"
        );
        assert_eq!(
            scheduled.scc_outcomes, self.scc_outcomes,
            "{case}: SCC terminal outcomes diverged"
        );
        assert_eq!(
            scheduled.scc_stats, self.scc_stats,
            "{case}: SCC scheduling counters diverged"
        );
        assert_eq!(
            scheduled.scc_events, self.scc_events,
            "{case}: SCC events diverged"
        );
        assert_eq!(
            scheduled.lowering_errors, self.lowering_errors,
            "{case}: lowering errors diverged"
        );
        assert_eq!(
            scheduled.diagnostics, self.diagnostics,
            "{case}: diagnostics diverged"
        );
        assert_eq!(
            scheduled.role_impl_conformance, self.role_impl_conformance,
            "{case}: role-impl conformance outcomes diverged"
        );
        assert_text_eq(
            case,
            "poly surface dump",
            &self.poly_dump,
            &scheduled.poly_dump,
        );
        assert_text_eq(
            case,
            "poly raw dump",
            &self.poly_raw_dump,
            &scheduled.poly_raw_dump,
        );
        assert_eq!(
            scheduled.namespace, self.namespace,
            "{case}: compiled namespace surface diverged"
        );
        assert_eq!(
            scheduled.lowering_surface, self.lowering_surface,
            "{case}: compiled lowering surface diverged"
        );
        assert_text_eq(
            case,
            "compiled runtime arena",
            &self.runtime_arena_dump,
            &scheduled.runtime_arena_dump,
        );
        assert_text_eq(
            case,
            "compiled runtime raw arena",
            &self.runtime_raw_arena_dump,
            &scheduled.runtime_raw_arena_dump,
        );
        assert_eq!(
            scheduled.runtime_boundary, self.runtime_boundary,
            "{case}: compiled runtime boundary diverged"
        );
        assert_eq!(
            scheduled.runtime_labels, self.runtime_labels,
            "{case}: compiled runtime labels diverged"
        );
        assert_eq!(
            scheduled.runtime_modules, self.runtime_modules,
            "{case}: compiled runtime modules diverged"
        );
        assert_eq!(
            scheduled.runtime_values, self.runtime_values,
            "{case}: compiled runtime values diverged"
        );
    }
}

fn finalized_scheme_snapshot(output: &BodyLowering) -> Vec<(DefId, String, String)> {
    let mut schemes = output
        .session
        .poly
        .defs
        .iter()
        .filter_map(|(def, item)| match item {
            Def::Let {
                scheme: Some(scheme),
                ..
            } => Some((
                def,
                poly::dump::format_scheme(&output.session.poly.typ, scheme),
                poly::dump::dump_scheme_raw(&output.session.poly.typ, scheme),
            )),
            Def::Mod { .. } | Def::Let { .. } | Def::Arg => None,
        })
        .collect::<Vec<_>>();
    schemes.sort_by_key(|(def, _, _)| def.0);
    schemes
}

fn role_candidate_snapshot<'a>(
    types: &poly::types::TypeArena,
    candidates: impl Iterator<Item = &'a RoleImplCandidate>,
) -> Vec<String> {
    let mut candidates = candidates
        .map(|candidate| format_role_candidate(types, candidate))
        .collect::<Vec<_>>();
    candidates.sort();
    candidates
}

fn format_role_candidate(types: &poly::types::TypeArena, candidate: &RoleImplCandidate) -> String {
    let format_arg = |arg: &RoleConstraintArg| {
        format!(
            "{} <: {}",
            poly::dump::format_pos(types, arg.lower),
            poly::dump::format_neg(types, arg.upper),
        )
    };
    let inputs = candidate.inputs.iter().map(format_arg).collect::<Vec<_>>();
    let associated = candidate
        .associated
        .iter()
        .map(|associated| format!("{}={}", associated.name, format_arg(&associated.value)))
        .collect::<Vec<_>>();
    let prerequisites = candidate
        .prerequisites
        .iter()
        .map(|prerequisite| {
            let inputs = prerequisite
                .inputs
                .iter()
                .map(format_arg)
                .collect::<Vec<_>>();
            let associated = prerequisite
                .associated
                .iter()
                .map(|associated| format!("{}={}", associated.name, format_arg(&associated.value)))
                .collect::<Vec<_>>();
            format!(
                "{}({inputs:?}; {associated:?})",
                prerequisite.role.join("::")
            )
        })
        .collect::<Vec<_>>();
    format!(
        "impl={:?} {}({inputs:?}; {associated:?}) where {prerequisites:?} methods={:?}",
        candidate.impl_def,
        candidate.role.join("::"),
        candidate.methods,
    )
}

fn assert_text_eq(case: &str, dimension: &str, always: &str, scheduled: &str) {
    if always == scheduled {
        return;
    }
    let line = always
        .lines()
        .zip(scheduled.lines())
        .position(|(always, scheduled)| always != scheduled)
        .unwrap_or_else(|| always.lines().count().min(scheduled.lines().count()));
    let always_line = always.lines().nth(line).unwrap_or("<end>");
    let scheduled_line = scheduled.lines().nth(line).unwrap_or("<end>");
    panic!(
        "{case}: {dimension} diverged at line {}\nalways: {always_line}\nscheduled: {scheduled_line}",
        line + 1,
    );
}
