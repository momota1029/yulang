//! Finalize a runtime IR module: instantiate principals into a fresh
//! monomorphic graph per call site, solve, emit mono bindings, rewrite call
//! sites, materialize substitutions, and run post-passes.
//!
//! This file holds the top-level pipeline entry points and the main
//! fixed-point loop. The phase-specific work is split across submodules:
//!
//! - [`apply_spine`] — collect apply spines from every expression, build a
//!   monomorphic `TypeGraph` per spine and solve it.
//! - [`debug_invariants`] — optional developer diagnostics for finalized IR
//!   shape checks.
//! - [`lowered_to_finalized`] — convert lowered runtime IR into the finalized
//!   runtime shape before specialization starts.
//! - [`legacy_runtime`] — adapt finalized runtime IR back to legacy runtime IR.
//! - [`role`] — close associated types from role impls and rewrite role-method
//!   call sites once impls become reachable.
//! - [`rewrite`] — emit mono `Binding`s and rewrite `Var`/`Apply` spines to
//!   the new aliases.
//! - [`materialize`] — apply substitutions to expressions, evidence, and
//!   apply-arg shapes (thunk wrapping).
//! - [`local_types`] — refresh local reference types after a specialization
//!   changes lambda parameter shapes.
//! - [`cast`] — semantic-cast lattice + Coerce-node normalization.
//! - [`postpass`] — one-shot finishing passes (`fill_*`, `prune_*`,
//!   `normalize_*`) and the shared runtime-type-shape helpers.

mod apply_spine;
mod cast;
mod debug_invariants;
mod legacy_runtime;
mod local_types;
mod lowered_to_finalized;
mod materialize;
mod pattern_types;
mod postpass;
mod rewrite;
mod role;

pub use apply_spine::{collect_root_graph_inputs, solve_root_graphs};

// Re-exports so sibling submodules can still address shared helpers as
// `super::X` rather than `super::postpass::X`.
pub(crate) use postpass::{
    core_type_has_unknown, core_type_is_closed, finalized_apply_spine_arg_effects,
    finalized_effect_boundaries_from_principal, narrow_runtime_type_in_place, path_from_name,
    reachable_paths, refine_runtime_spine_return, runtime_function_param, runtime_type_has_unknown,
    runtime_type_is_closed, runtime_type_to_core, unit_type,
};

use std::collections::HashSet;

use yulang_runtime_ir::{FinalizedModule as Module, LoweredModule};

use crate::{
    MonomorphizeError, MonomorphizeInstanceCache, MonomorphizeOutput, MonomorphizeReport,
    MonomorphizeResult, RootGraphSolution,
};

pub trait IntoFinalizeRuntimeModule {
    fn into_finalize_runtime_module(self) -> Module;
}

impl IntoFinalizeRuntimeModule for LoweredModule {
    fn into_finalize_runtime_module(self) -> Module {
        lowered_to_finalized::from_lowered_module(self)
    }
}

impl IntoFinalizeRuntimeModule for Module {
    fn into_finalize_runtime_module(self) -> Module {
        self
    }
}

pub fn finalize_module<M: IntoFinalizeRuntimeModule>(
    module: M,
) -> MonomorphizeResult<MonomorphizeOutput> {
    let mut cache = MonomorphizeInstanceCache::default();
    finalize_module_with_cache(module, &mut cache)
}

pub fn monomorphize_module<M: IntoFinalizeRuntimeModule>(
    module: M,
) -> Result<Module, MonomorphizeError> {
    Ok(monomorphize_module_with_report(module.into_finalize_runtime_module())?.module)
}

pub fn monomorphize_to_legacy_runtime_module<M: IntoFinalizeRuntimeModule>(
    module: M,
) -> Result<yulang_runtime_types::Module, MonomorphizeError> {
    Ok(legacy_runtime::from_finalized_module(monomorphize_module(
        module,
    )?))
}

pub fn monomorphize_module_with_report(
    module: Module,
) -> Result<MonomorphizeOutput, MonomorphizeError> {
    let output = finalize_module(module)?;
    debug_invariants::validate(&output.module);
    Ok(output)
}

pub fn finalize_module_with_cache<M: IntoFinalizeRuntimeModule>(
    module: M,
    cache: &mut MonomorphizeInstanceCache,
) -> MonomorphizeResult<MonomorphizeOutput> {
    let mut module = module.into_finalize_runtime_module();
    let root_graph_inputs = collect_root_graph_inputs(&module);
    let root_graph_solutions = solve_monomorphic_instances(&mut module, cache)?;
    finish_monomorphized_module(&mut module, &root_graph_solutions);
    Ok(MonomorphizeOutput {
        module,
        report: MonomorphizeReport {
            root_graph_inputs,
            root_graph_solutions,
            cache_profile: cache.profile(),
        },
    })
}

fn solve_monomorphic_instances(
    module: &mut Module,
    cache: &mut MonomorphizeInstanceCache,
) -> MonomorphizeResult<Vec<RootGraphSolution>> {
    role::rewrite_root_role_method_calls(module);
    let cast_order = cast::type_cast_order(&module.role_impls);
    let mut root_graph_solutions = solve_root_graphs(module, &cast_order)?;
    let mut scanned_binding_bodies = HashSet::new();
    let mut applied_solution_count = 0;
    loop {
        rewrite::canonicalize_aliases(&mut root_graph_solutions);
        let emitted = rewrite::append_monomorphic_bindings(module, &root_graph_solutions, cache)?;
        let unapplied_solutions = &root_graph_solutions[applied_solution_count..];
        rewrite::rewrite_root_exprs(module, unapplied_solutions)?;
        rewrite::rewrite_binding_exprs(module, unapplied_solutions)?;
        applied_solution_count = root_graph_solutions.len();
        let role_rewrites = role::rewrite_role_method_calls(module);

        let solution_count = root_graph_solutions.len();
        apply_spine::collect_root_expr_graphs(module, &cast_order, &mut root_graph_solutions)?;
        let scan_targets = apply_spine::next_binding_body_scan_targets(
            module,
            &emitted,
            &mut scanned_binding_bodies,
        );
        apply_spine::collect_binding_body_graphs(
            module,
            &scan_targets,
            &cast_order,
            &mut root_graph_solutions,
        )?;
        if emitted.is_empty()
            && scan_targets.is_empty()
            && !role_rewrites
            && root_graph_solutions.len() == solution_count
        {
            break;
        }
    }
    Ok(root_graph_solutions)
}

fn finish_monomorphized_module(module: &mut Module, root_graph_solutions: &[RootGraphSolution]) {
    postpass::monomorphize_phantom_nullary_variant_bindings(module);
    postpass::normalize_materialized_module(module);
    cast::normalize_semantic_cast_coercions(module);
    // Fill local Var types first (using enclosing-binder scope), so the apply
    // evidence pass sees concrete arg/callee types when reconciling.
    postpass::fill_local_var_types(module);
    postpass::fill_apply_evidence_types(module);
    // Run scope walk again — apply reconciliation may have concretized
    // pattern/handler types that earlier scope walk skipped.
    postpass::fill_local_var_types(module);
    postpass::normalize_materialized_module(module);
    cast::normalize_semantic_cast_coercions(module);
    postpass::inline_small_direct_calls(module);
    postpass::fill_local_var_types(module);
    postpass::normalize_materialized_module(module);
    cast::normalize_semantic_cast_coercions(module);
    postpass::eliminate_immediate_thunk_forces(module);
    postpass::prune_specialized_polymorphic_bindings(module, root_graph_solutions);
    postpass::prune_unreachable_bindings(module);
    postpass::prune_unbound_binding_roots(module);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    use crate::{
        MonomorphizeInstanceArtifactCache, RootGraphInput, RootGraphRoot, graph::TypeCastOrder,
    };
    use yulang_runtime_ir::{
        FinalizedBinding as Binding, FinalizedExpr as Expr, FinalizedExprKind as ExprKind,
        FinalizedModule as Module, FinalizedPattern as Pattern, Root, RuntimeType,
    };
    use yulang_sources::{
        CompiledSourceFileIdentity, CompiledUnitDependency, CompiledUnitManifest,
        SourceCompilationUnitOrigin, SourceOrigin,
    };
    use yulang_typed_ir as typed_ir;

    #[test]
    fn closed_root_expr_becomes_root_graph_input() {
        let ty = RuntimeType::Value(typed_ir::Type::Tuple(Vec::new()));
        let module = Module {
            path: path("test"),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(ExprKind::Tuple(Vec::new()), ty.clone())],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        assert_eq!(
            collect_root_graph_inputs(&module),
            vec![RootGraphInput {
                root: RootGraphRoot::Expr(0),
                known_type: Some(ty),
            }]
        );
    }

    #[test]
    fn open_root_expr_does_not_make_fake_any_input() {
        let module = Module {
            path: path("test"),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Tuple(Vec::new()),
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        assert_eq!(collect_root_graph_inputs(&module)[0].known_type, None);
    }

    #[test]
    fn reachable_paths_ignore_block_local_shadowing_top_level_binding() {
        let name = path("text");
        let int = RuntimeType::Value(int_type());
        let module = Module {
            path: path("test"),
            bindings: vec![Binding {
                name: name.clone(),
                type_params: vec![typed_ir::TypeVar("a".into())],
                scheme: typed_ir::Scheme {
                    requirements: Vec::new(),
                    body: typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                },
                body: Expr::typed(ExprKind::Var(path("source")), RuntimeType::Unknown),
            }],
            root_exprs: vec![Expr::typed(
                ExprKind::Block {
                    stmts: vec![yulang_runtime_ir::FinalizedStmt::Let {
                        pattern: Pattern::Bind {
                            name: typed_ir::Name("text".into()),
                            ty: int.clone(),
                        },
                        value: Expr::typed(ExprKind::Lit(typed_ir::Lit::Int("1".into())), int),
                    }],
                    tail: Some(Box::new(Expr::typed(
                        ExprKind::Var(name.clone()),
                        RuntimeType::Unknown,
                    ))),
                },
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        assert!(!reachable_paths(&module).contains(&name));
    }

    #[test]
    fn root_apply_solves_id_one_graph() {
        let int = int_type();
        let module = Module {
            path: path("test"),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(ExprKind::Var(path("id")), RuntimeType::Unknown)),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Value(int.clone()),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 1);
        let solution = &output.report.root_graph_solutions[0];
        assert_eq!(solution.binding, path("id"));
        assert_eq!(solution.result_type, RuntimeType::Value(int.clone()));
        assert!(solution.graph.is_complete());
        assert_eq!(solution.graph.substitutions()[0].ty, int);
        assert_eq!(solution.alias, path(&["id", "mono0"]));
        assert_eq!(output.module.bindings.len(), 1);
        assert_eq!(output.module.bindings[0].name, path(&["id", "mono0"]));
        assert!(output.module.bindings[0].type_params.is_empty());
        assert_eq!(
            simple_apply_callee_path(&output.module.root_exprs[0]),
            Some(path(&["id", "mono0"]))
        );
        assert_eq!(
            output.module.root_exprs[0].ty,
            RuntimeType::Value(int.clone())
        );
    }

    #[test]
    fn root_apply_top_callee_param_annotation_does_not_force_top_solution() {
        let int = int_type();
        let module = Module {
            path: path("test"),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("id")),
                        RuntimeType::Fun {
                            param: Box::new(RuntimeType::Value(typed_ir::Type::Any)),
                            ret: Box::new(RuntimeType::Value(int.clone())),
                        },
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Value(int.clone()),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::Value(int.clone()),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_module(module).unwrap();
        let solution = &output.report.root_graph_solutions[0];

        assert_eq!(solution.binding, path("id"));
        assert_eq!(solution.graph.substitutions()[0].ty, int);
    }

    #[test]
    fn apply_arg_evidence_overrides_runtime_top_arg_for_principal_solution() {
        let int = int_type();
        let module = Module {
            path: path("test"),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(ExprKind::Var(path("id")), RuntimeType::Unknown)),
                    arg: Box::new(Expr::typed(
                        ExprKind::Var(path("x")),
                        RuntimeType::Value(typed_ir::Type::Any),
                    )),
                    evidence: Some(typed_ir::ApplyEvidence {
                        callee_source_edge: None,
                        arg_source_edge: Some(0),
                        callee: typed_ir::TypeBounds::default(),
                        expected_callee: None,
                        arg: typed_ir::TypeBounds {
                            lower: None,
                            upper: Some(Box::new(int.clone())),
                        },
                        expected_arg: Some(typed_ir::TypeBounds {
                            lower: None,
                            upper: Some(Box::new(int.clone())),
                        }),
                        result: typed_ir::TypeBounds::exact(int.clone()),
                        principal_callee: Some(typed_ir::Type::Fun {
                            param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                            param_effect: Box::new(typed_ir::Type::Never),
                            ret_effect: Box::new(typed_ir::Type::Never),
                            ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                        }),
                        substitutions: vec![typed_ir::TypeSubstitution {
                            var: typed_ir::TypeVar("a".into()),
                            ty: int.clone(),
                        }],
                        substitution_candidates: Vec::new(),
                        role_method: false,
                        principal_elaboration: None,
                    }),
                    instantiation: None,
                },
                RuntimeType::Value(int.clone()),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_module(module).unwrap();
        let solution = &output.report.root_graph_solutions[0];

        assert_eq!(solution.binding, path("id"));
        assert_eq!(solution.graph.substitutions()[0].ty, int);
    }

    #[test]
    fn local_scope_type_overrides_stale_var_annotation_in_apply_arg() {
        let int = int_type();
        let original = typed_ir::TypeVar("a".into());
        let stale = RuntimeType::Value(typed_ir::Type::Named {
            path: path("list"),
            args: vec![typed_ir::TypeArg::Type(typed_ir::Type::Var(original))],
        });
        let concrete = RuntimeType::Value(typed_ir::Type::Named {
            path: path("list"),
            args: vec![typed_ir::TypeArg::Type(int.clone())],
        });
        let local_path = path("xs");
        let mut local_types = HashMap::new();
        local_types.insert(local_path.clone(), concrete.clone());
        let expr = Expr::typed(ExprKind::Var(local_path), stale);

        assert_eq!(apply_spine::expr_lower_type(&expr, &local_types), concrete);
    }

    #[test]
    fn apply_arg_graphs_use_solved_callee_param_for_lambda_body() {
        let e = typed_ir::TypeVar("e".into());
        let fs = named_core("Fs", Vec::new());
        let text = named_core("Text", Vec::new());
        let unit = unit_type();
        let lines_fs = named_core("Lines", vec![fs.clone()]);
        let lines_e = named_core("Lines", vec![typed_ir::Type::Var(e.clone())]);
        let ref_fs_text = named_core("Ref", vec![fs.clone(), text.clone()]);
        let ref_unknown_text = named_core("Ref", vec![typed_ir::Type::Unknown, text.clone()]);
        let ref_e_text = named_core("Ref", vec![typed_ir::Type::Var(e.clone()), text.clone()]);
        let use_ref = Binding {
            name: path("use_ref"),
            type_params: vec![e.clone()],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: core_fun(ref_e_text.clone(), typed_ir::Type::Never, unit.clone()),
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        };
        let for_each = Binding {
            name: path("for_each"),
            type_params: vec![e.clone()],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: core_fun(
                    lines_e,
                    typed_ir::Type::Never,
                    core_fun(
                        core_fun(ref_e_text, typed_ir::Type::Never, unit.clone()),
                        typed_ir::Type::Never,
                        unit.clone(),
                    ),
                ),
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        };
        let line = typed_ir::Name("line".into());
        let root = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(Expr::typed(
                            ExprKind::Var(path("for_each")),
                            RuntimeType::Unknown,
                        )),
                        arg: Box::new(Expr::typed(
                            ExprKind::Var(path("lines")),
                            RuntimeType::Value(lines_fs),
                        )),
                        evidence: None,
                        instantiation: None,
                    },
                    RuntimeType::Unknown,
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lambda {
                        param: line.clone(),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(path("use_ref")),
                                    RuntimeType::Unknown,
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Var(typed_ir::Path::from_name(line)),
                                    RuntimeType::Value(ref_unknown_text.clone()),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::Value(unit.clone()),
                        )),
                    },
                    RuntimeType::Fun {
                        param: Box::new(RuntimeType::Value(ref_unknown_text)),
                        ret: Box::new(RuntimeType::Value(unit.clone())),
                    },
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Value(unit),
        );
        let module = Module {
            path: path("test"),
            bindings: vec![use_ref, for_each],
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let solutions = solve_root_graphs(&module, &TypeCastOrder::default()).unwrap();
        eprintln!("{solutions:#?}");
        let use_ref_solution = solutions
            .iter()
            .find(|solution| solution.binding == path("use_ref"))
            .expect("lambda body apply should be solved");

        assert!(
            use_ref_solution
                .type_substitutions
                .iter()
                .any(|subst| { subst.var == e && subst.ty == fs }),
            "{use_ref_solution:#?}"
        );
        assert_eq!(
            use_ref_solution.result_type,
            RuntimeType::Value(unit_type())
        );
        assert_eq!(
            use_ref_solution.callee_type,
            RuntimeType::Fun {
                param: Box::new(RuntimeType::Value(ref_fs_text)),
                ret: Box::new(RuntimeType::Value(unit_type())),
            }
        );
    }

    #[test]
    fn block_let_local_uses_collected_initializer_result_for_following_apply() {
        let e = typed_ir::TypeVar("e".into());
        let fs = named_core("Fs", Vec::new());
        let loop_eff = named_core("Loop", Vec::new());
        let text = named_core("Text", Vec::new());
        let unit = unit_type();
        let lines_fs = named_core("Lines", vec![fs.clone()]);
        let lines_e = named_core("Lines", vec![typed_ir::Type::Var(e.clone())]);
        let ref_fs_text = named_core("Ref", vec![fs.clone(), text.clone()]);
        let ref_loop_text = named_core("Ref", vec![loop_eff, text.clone()]);
        let ref_unknown_text = named_core("Ref", vec![typed_ir::Type::Unknown, text.clone()]);
        let ref_e_text = named_core("Ref", vec![typed_ir::Type::Var(e.clone()), text.clone()]);
        let project = Binding {
            name: path("project"),
            type_params: vec![e.clone()],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: core_fun(
                    ref_e_text.clone(),
                    typed_ir::Type::Never,
                    core_fun(unit.clone(), typed_ir::Type::Never, ref_e_text.clone()),
                ),
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        };
        let use_ref = Binding {
            name: path("use_ref"),
            type_params: vec![e.clone()],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: core_fun(ref_e_text.clone(), typed_ir::Type::Never, unit.clone()),
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        };
        let for_each = Binding {
            name: path("for_each"),
            type_params: vec![e.clone()],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: core_fun(
                    lines_e,
                    typed_ir::Type::Never,
                    core_fun(
                        core_fun(ref_e_text, typed_ir::Type::Never, unit.clone()),
                        typed_ir::Type::Never,
                        unit.clone(),
                    ),
                ),
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        };
        let line = typed_ir::Name("line".into());
        let slice = typed_ir::Name("slice".into());
        let line_path = typed_ir::Path::from_name(line.clone());
        let slice_path = typed_ir::Path::from_name(slice.clone());
        let project_line = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path("project")),
                    RuntimeType::Unknown,
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Var(line_path),
                    RuntimeType::Value(ref_unknown_text.clone()),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Unknown,
        );
        let project_slice = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(project_line),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::Value(unit.clone()),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Value(ref_loop_text),
        );
        let lambda_body = Expr::typed(
            ExprKind::Block {
                stmts: vec![yulang_runtime_ir::FinalizedStmt::Let {
                    pattern: Pattern::Bind {
                        name: slice,
                        ty: RuntimeType::Unknown,
                    },
                    value: project_slice,
                }],
                tail: Some(Box::new(Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(Expr::typed(
                            ExprKind::Var(path("use_ref")),
                            RuntimeType::Unknown,
                        )),
                        arg: Box::new(Expr::typed(ExprKind::Var(slice_path), RuntimeType::Unknown)),
                        evidence: None,
                        instantiation: None,
                    },
                    RuntimeType::Value(unit.clone()),
                ))),
            },
            RuntimeType::Value(unit.clone()),
        );
        let root = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(Expr::typed(
                            ExprKind::Var(path("for_each")),
                            RuntimeType::Unknown,
                        )),
                        arg: Box::new(Expr::typed(
                            ExprKind::Var(path("lines")),
                            RuntimeType::Value(lines_fs),
                        )),
                        evidence: None,
                        instantiation: None,
                    },
                    RuntimeType::Unknown,
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lambda {
                        param: line,
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(lambda_body),
                    },
                    RuntimeType::Fun {
                        param: Box::new(RuntimeType::Value(ref_unknown_text)),
                        ret: Box::new(RuntimeType::Value(unit.clone())),
                    },
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Value(unit.clone()),
        );
        let module = Module {
            path: path("test"),
            bindings: vec![project, use_ref, for_each],
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let solutions = solve_root_graphs(&module, &TypeCastOrder::default()).unwrap();
        let use_ref_solution = solutions
            .iter()
            .find(|solution| solution.binding == path("use_ref"))
            .expect("let-local use should be solved");

        assert!(
            use_ref_solution
                .type_substitutions
                .iter()
                .any(|subst| { subst.var == e && subst.ty == fs }),
            "{use_ref_solution:#?}"
        );
        assert_eq!(
            use_ref_solution.callee_type,
            RuntimeType::Fun {
                param: Box::new(RuntimeType::Value(ref_fs_text)),
                ret: Box::new(RuntimeType::Value(unit)),
            }
        );
    }

    #[test]
    fn root_apply_result_type_bounds_open_return_var() {
        let int = int_type();
        let bool_ty = bool_type();
        let module = Module {
            path: path("test"),
            bindings: vec![poly_return_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("poly_return")),
                        RuntimeType::Unknown,
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Value(int.clone()),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::Value(bool_ty.clone()),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let solutions = solve_root_graphs(&module, &TypeCastOrder::default()).unwrap();

        assert_eq!(solutions.len(), 1);
        let substitutions = &solutions[0].type_substitutions;
        assert!(substitutions.iter().any(|substitution| {
            substitution.var == typed_ir::TypeVar("a".into()) && substitution.ty == int
        }));
        assert!(substitutions.iter().any(|substitution| {
            substitution.var == typed_ir::TypeVar("b".into()) && substitution.ty == bool_ty
        }));
        assert!(solutions[0].graph.is_complete());
    }

    #[test]
    fn finalize_instance_cache_surface_reuses_materialized_binding() {
        let mut cache = MonomorphizeInstanceCache::default();
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let first = finalize_module_with_cache(module.clone(), &mut cache).unwrap();
        assert_eq!(first.report.cache_profile.inserts, 1);
        assert_eq!(cache.to_surface().instances.len(), 1);

        let second = finalize_module_with_cache(module.clone(), &mut cache).unwrap();
        assert!(second.report.cache_profile.hits >= 1);
        assert_eq!(second.module.bindings[0].name, path(&["id", "mono0"]));

        let surface = cache.to_surface();
        let mut restored = MonomorphizeInstanceCache::from_surface(surface);
        let third = finalize_module_with_cache(module, &mut restored).unwrap();
        assert_eq!(third.report.cache_profile.hits, 1);
        assert_eq!(third.module.bindings[0].name, path(&["id", "mono0"]));

        let mut stale_surface = cache.to_surface();
        stale_surface.format_version += 1;
        assert!(
            MonomorphizeInstanceCache::from_surface(stale_surface)
                .to_surface()
                .instances
                .is_empty()
        );
    }

    #[test]
    fn finalize_instance_artifact_cache_rehydrates_solver_cache() {
        let root = artifact_cache_root("solver-rehydrate");
        let _ = std::fs::remove_dir_all(&root);
        let artifact_cache = MonomorphizeInstanceArtifactCache::new(&root);
        let manifests = vec![compiled_manifest(0, 11), compiled_manifest(1, 29)];
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let mut first_cache = MonomorphizeInstanceCache::default();
        let first = finalize_module_with_cache(module.clone(), &mut first_cache).unwrap();
        assert_eq!(first.report.cache_profile.inserts, 1);
        artifact_cache
            .write_cache_for_manifests(&manifests, &first_cache)
            .unwrap();

        let mut restored = artifact_cache.read_cache_for_manifests(&manifests);
        let second = finalize_module_with_cache(module, &mut restored).unwrap();
        let _ = std::fs::remove_dir_all(&root);

        assert_eq!(second.report.cache_profile.hits, 1);
        assert_eq!(second.module.bindings[0].name, path(&["id", "mono0"]));
    }

    #[test]
    fn root_tuple_solves_two_id_uses_separately() {
        let int = int_type();
        let bool_ty = bool_type();
        let module = Module {
            path: path("test"),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Tuple(vec![
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Value(int.clone()),
                    )),
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Bool(true)),
                        RuntimeType::Value(bool_ty.clone()),
                    )),
                ]),
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 2);
        assert_eq!(
            output.report.root_graph_solutions[0].result_type,
            RuntimeType::Value(int.clone())
        );
        assert_eq!(
            output.report.root_graph_solutions[1].result_type,
            RuntimeType::Value(bool_ty.clone())
        );
        assert_eq!(
            output.report.root_graph_solutions[0].graph.substitutions()[0].ty,
            int
        );
        assert_eq!(
            output.report.root_graph_solutions[1].graph.substitutions()[0].ty,
            bool_ty
        );
        assert_eq!(output.module.bindings.len(), 2);
        assert_eq!(output.module.bindings[0].name, path(&["id", "mono0"]));
        assert_eq!(output.module.bindings[1].name, path(&["id", "mono1"]));
        let ExprKind::Tuple(items) = &output.module.root_exprs[0].kind else {
            panic!("root should stay a tuple");
        };
        assert_eq!(
            simple_apply_callee_path(&items[0]),
            Some(path(&["id", "mono0"]))
        );
        assert_eq!(
            simple_apply_callee_path(&items[1]),
            Some(path(&["id", "mono1"]))
        );
        assert_eq!(items[0].ty, RuntimeType::Value(int.clone()));
        assert_eq!(items[1].ty, RuntimeType::Value(bool_ty.clone()));
    }

    #[test]
    fn repeated_same_instance_reuses_one_alias() {
        let int = int_type();
        let module = Module {
            path: path("test"),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Tuple(vec![
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Value(int.clone()),
                    )),
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("2".into())),
                        RuntimeType::Value(int.clone()),
                    )),
                ]),
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 2);
        assert_eq!(
            output.report.root_graph_solutions[0].alias,
            output.report.root_graph_solutions[1].alias
        );
        assert_eq!(output.module.bindings.len(), 1);
        assert_eq!(output.module.bindings[0].name, path(&["id", "mono0"]));
        let ExprKind::Tuple(items) = &output.module.root_exprs[0].kind else {
            panic!("root should stay a tuple");
        };
        assert_eq!(
            simple_apply_callee_path(&items[0]),
            Some(path(&["id", "mono0"]))
        );
        assert_eq!(
            simple_apply_callee_path(&items[1]),
            Some(path(&["id", "mono0"]))
        );
    }

    #[test]
    fn source_my_id_x_eq_x_id_1_solves_root_graph() {
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 1);
        let solution = &output.report.root_graph_solutions[0];
        assert!(solution.graph.is_complete());
        assert!(matches!(solution.result_type, RuntimeType::Value(_)));
    }

    #[test]
    fn source_my_id_x_eq_x_two_roots_solve_separate_graphs() {
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\nid true\n");

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 2);
        assert!(
            output
                .report
                .root_graph_solutions
                .iter()
                .all(|solution| solution.graph.is_complete())
        );
        assert_ne!(
            output.report.root_graph_solutions[0].result_type,
            output.report.root_graph_solutions[1].result_type
        );
        assert!(output.module.bindings.iter().any(|binding| {
            binding.name == path(&["id", "mono0"]) && binding.type_params.is_empty()
        }));
        assert!(output.module.bindings.iter().any(|binding| {
            binding.name == path(&["id", "mono1"]) && binding.type_params.is_empty()
        }));
    }

    #[test]
    fn finalized_source_id_1_runs_on_vm() {
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "1".into()
            ))]
        );
    }

    #[test]
    fn finalize_monomorphize_module_returns_valid_mainline_output() {
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let module = monomorphize_module(module).unwrap();
        yulang_vm::compile_vm_module(module).unwrap();
    }

    #[test]
    fn finalized_source_solves_polymorphic_call_inside_monomorphic_body() {
        let module = runtime_module_from_source_without_std("my id x = x\nmy f y = id y\nf 1\n");

        let output = finalize_module(module).unwrap();
        let solved_aliases = output
            .report
            .root_graph_solutions
            .iter()
            .map(|solution| solution.alias.clone())
            .collect::<Vec<_>>();
        assert!(solved_aliases.contains(&path(&["f", "mono0"])));
        assert!(solved_aliases.contains(&path(&["id", "mono1"])));
        assert!(
            output
                .module
                .bindings
                .iter()
                .all(|binding| binding.type_params.is_empty())
        );

        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "1".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_first_1_true_from_apply_constraints() {
        let module = runtime_module_from_source_without_std("my first x y = x\nfirst 1 true\n");

        let output = finalize_module(module).unwrap();
        let solution = &output.report.root_graph_solutions[0];
        assert_eq!(
            solution.result_type,
            RuntimeType::Value(typed_ir::Type::Named {
                path: path("int"),
                args: Vec::new(),
            })
        );
        assert!(
            output
                .module
                .bindings
                .iter()
                .all(|binding| binding.type_params.is_empty())
        );

        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "1".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_twice_id_1() {
        let module = runtime_module_from_source_without_std(
            "my id x = x\nmy twice f x = f (f x)\ntwice id 1\n",
        );

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "1".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_flip_pair_1_2() {
        let module = runtime_module_from_source_without_std(
            "my pair x y = (x, y)\nmy flip f x y = f y x\nflip pair 1 2\n",
        );

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Tuple(vec![
                yulang_vm::VmValue::Int("2".into()),
                yulang_vm::VmValue::Int("1".into()),
            ]))]
        );
    }

    #[test]
    fn finalized_source_runs_if_int_float_join() {
        let module =
            runtime_module_from_source_without_std("my x = if true { 1 } else { 2.0 }\nx\n");

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Float(
                "1.0".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_nested_lexical_block() {
        let module = runtime_module_from_source_without_std(
            r#"{
    my x = 1
    {
        my y = 2
        y
    }
}
"#,
        );

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "2".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_polymorphic_body_with_lexical_block() {
        let module = runtime_module_from_source_without_std(
            r#"my f x = {
    my y = x
    y
}
f 3
"#,
        );

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "3".into()
            ))]
        );
    }

    #[test]
    fn materialize_block_type_from_tail_before_deciding_bind_here() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let thunk = RuntimeType::Thunk {
            effect: typed_ir::Type::Never,
            value: Box::new(RuntimeType::Value(int.clone())),
        };
        let stale_block = Expr::typed(
            ExprKind::Block {
                stmts: Vec::new(),
                tail: Some(Box::new(Expr::typed(
                    ExprKind::Thunk {
                        effect: typed_ir::Type::Never,
                        value: RuntimeType::Value(int.clone()),
                        expr: Box::new(Expr::typed(
                            ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                            RuntimeType::Value(int.clone()),
                        )),
                    },
                    thunk.clone(),
                ))),
            },
            RuntimeType::Value(int.clone()),
        );
        let bind_here = Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(stale_block),
            },
            RuntimeType::Value(int),
        );

        let materialized = materialize::materialize_expr(bind_here, &[]);
        let ExprKind::BindHere { expr } = materialized.kind else {
            panic!("bind_here should be kept when the materialized block tail is a thunk");
        };

        assert_eq!(expr.ty, thunk);
    }

    #[test]
    fn materialize_apply_arg_preserves_thunk_until_runtime_force() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let unit = unit_type();
        let thunk_ty = RuntimeType::Thunk {
            effect: typed_ir::Type::Never,
            value: Box::new(RuntimeType::Value(int.clone())),
        };
        let apply = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path("f")),
                    RuntimeType::Fun {
                        param: Box::new(RuntimeType::Value(int.clone())),
                        ret: Box::new(RuntimeType::Value(unit.clone())),
                    },
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Thunk {
                        effect: typed_ir::Type::Never,
                        value: RuntimeType::Value(int.clone()),
                        expr: Box::new(Expr::typed(
                            ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                            RuntimeType::Value(int),
                        )),
                    },
                    thunk_ty.clone(),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Value(unit),
        );

        let materialized = materialize::materialize_expr(apply, &[]);
        let ExprKind::Apply { arg, .. } = materialized.kind else {
            panic!("expected apply expression");
        };

        assert!(matches!(arg.ty, RuntimeType::Thunk { .. }));
        assert!(matches!(arg.kind, ExprKind::Thunk { .. }));
    }

    #[test]
    fn materialize_add_id_preserves_thunk_operand_boundary() {
        let int = int_type();
        let unit = unit_type();
        let flip = typed_ir::Type::Named {
            path: path("flip"),
            args: Vec::new(),
        };
        let thunk_ty = RuntimeType::Thunk {
            effect: flip.clone(),
            value: Box::new(RuntimeType::Value(int.clone())),
        };
        let apply = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path("f")),
                    RuntimeType::Fun {
                        param: Box::new(RuntimeType::Value(unit.clone())),
                        ret: Box::new(RuntimeType::Value(int.clone())),
                    },
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::Value(unit),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Value(int.clone()),
        );
        let add_id = Expr::typed(
            ExprKind::AddId {
                id: yulang_runtime_ir::EffectIdRef::Peek,
                allowed: flip,
                active: true,
                thunk: Box::new(apply),
            },
            RuntimeType::Value(int),
        );

        let materialized = materialize::materialize_expr(add_id, &[]);
        let ExprKind::AddId { thunk, .. } = materialized.kind else {
            panic!("expected add_id expression");
        };

        assert_eq!(materialized.ty, thunk_ty);
        assert_eq!(thunk.ty, thunk_ty);
        assert!(matches!(thunk.kind, ExprKind::Thunk { .. }));
    }

    #[test]
    fn materialize_apply_instantiation_args() {
        let original = typed_ir::TypeVar("a".into());
        let target = typed_ir::TypeVar("b".into());
        let int = int_type();
        let apply = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(ExprKind::Var(path("id")), RuntimeType::Unknown)),
                arg: Box::new(Expr::typed(
                    ExprKind::Tuple(Vec::new()),
                    RuntimeType::Unknown,
                )),
                evidence: None,
                instantiation: Some(yulang_runtime_ir::TypeInstantiation {
                    target: path("id"),
                    args: vec![yulang_runtime_ir::TypeSubstitution {
                        var: target.clone(),
                        ty: typed_ir::Type::Var(original.clone()),
                    }],
                }),
            },
            RuntimeType::Value(typed_ir::Type::Var(original.clone())),
        );

        let materialized = materialize::materialize_expr(
            apply,
            &[typed_ir::TypeSubstitution {
                var: original,
                ty: int.clone(),
            }],
        );

        let ExprKind::Apply {
            instantiation: Some(instantiation),
            ..
        } = materialized.kind
        else {
            panic!("expected materialized apply instantiation");
        };

        assert_eq!(
            instantiation.args,
            vec![yulang_runtime_ir::TypeSubstitution {
                var: target,
                ty: int,
            }]
        );
    }

    #[test]
    fn materialize_thunk_keeps_own_value_under_non_thunk_expected() {
        let var = typed_ir::TypeVar("a".into());
        let unit = unit_type();
        let tuple = typed_ir::Type::Tuple(vec![unit.clone(), unit.clone()]);
        let thunk = Expr::typed(
            ExprKind::Thunk {
                effect: typed_ir::Type::Never,
                value: RuntimeType::Value(typed_ir::Type::Var(var.clone())),
                expr: Box::new(Expr::typed(
                    ExprKind::Var(path("x")),
                    RuntimeType::Value(typed_ir::Type::Var(var.clone())),
                )),
            },
            RuntimeType::Thunk {
                effect: typed_ir::Type::Never,
                value: Box::new(RuntimeType::Value(typed_ir::Type::Var(var.clone()))),
            },
        );

        let materialized = materialize::materialize_expr_with_expected(
            thunk,
            &[typed_ir::TypeSubstitution {
                var,
                ty: tuple.clone(),
            }],
            Some(&RuntimeType::Value(unit)),
        );

        let RuntimeType::Thunk { value, .. } = materialized.ty else {
            panic!("expected thunk type");
        };
        assert_eq!(*value, RuntimeType::Value(tuple));
    }

    #[test]
    fn refresh_local_expr_types_forces_select_base_after_param_thunk_specialization() {
        let field = typed_ir::Name("raw".into());
        let int = int_type();
        let record = typed_ir::Type::Record(typed_ir::RecordType {
            fields: vec![typed_ir::RecordField {
                name: field.clone(),
                value: int.clone(),
                optional: false,
            }],
            spread: None,
        });
        let value_record = RuntimeType::Value(record);
        let thunk_record = RuntimeType::Thunk {
            effect: typed_ir::Type::Never,
            value: Box::new(value_record.clone()),
        };
        let select = Expr::typed(
            ExprKind::Select {
                base: Box::new(Expr::typed(ExprKind::Var(path("x")), value_record.clone())),
                field,
            },
            RuntimeType::Value(int.clone()),
        );
        let lambda = Expr::typed(
            ExprKind::Lambda {
                param: typed_ir::Name("x".into()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(select),
            },
            RuntimeType::Fun {
                param: Box::new(thunk_record.clone()),
                ret: Box::new(RuntimeType::Value(int)),
            },
        );

        let refreshed = local_types::refresh_local_expr_types(lambda);
        let ExprKind::Lambda { body, .. } = refreshed.kind else {
            panic!("expected lambda");
        };
        let ExprKind::Select { base, .. } = body.kind else {
            panic!("expected select body");
        };
        let ExprKind::BindHere { expr } = base.kind else {
            panic!("expected select base to force the thunk parameter");
        };

        assert_eq!(base.ty, value_record);
        assert_eq!(expr.ty, thunk_record);
        let ExprKind::Var(var_path) = expr.kind else {
            panic!("expected forced select base to keep the original variable");
        };
        assert_eq!(var_path, path("x"));
    }

    #[test]
    fn refresh_local_expr_types_forces_coerce_operand_after_param_thunk_specialization() {
        let int = int_type();
        let value_int = RuntimeType::Value(int.clone());
        let thunk_int = RuntimeType::Thunk {
            effect: typed_ir::Type::Never,
            value: Box::new(value_int.clone()),
        };
        let coerce = Expr::typed(
            ExprKind::Coerce {
                from: int.clone(),
                to: int.clone(),
                expr: Box::new(Expr::typed(ExprKind::Var(path("x")), value_int.clone())),
            },
            value_int.clone(),
        );
        let lambda = Expr::typed(
            ExprKind::Lambda {
                param: typed_ir::Name("x".into()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(coerce),
            },
            RuntimeType::Fun {
                param: Box::new(thunk_int.clone()),
                ret: Box::new(value_int.clone()),
            },
        );

        let refreshed = local_types::refresh_local_expr_types(lambda);
        let ExprKind::Lambda { body, .. } = refreshed.kind else {
            panic!("expected lambda");
        };
        let ExprKind::Coerce { expr, .. } = body.kind else {
            panic!("expected coerce body");
        };
        assert_eq!(expr.ty, value_int);
        let ExprKind::BindHere { expr } = expr.kind else {
            panic!("expected coerce operand to force the thunk parameter");
        };

        assert_eq!(expr.ty, thunk_int);
        let ExprKind::Var(var_path) = expr.kind else {
            panic!("expected forced coerce operand to keep the original variable");
        };
        assert_eq!(var_path, path("x"));
    }

    #[test]
    fn materialize_apply_arg_prefers_closed_callee_param_over_stale_evidence() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let float = typed_ir::Type::Named {
            path: path("float"),
            args: Vec::new(),
        };
        let unit = unit_type();
        let apply = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path("f")),
                    RuntimeType::Fun {
                        param: Box::new(RuntimeType::Value(float.clone())),
                        ret: Box::new(RuntimeType::Value(unit.clone())),
                    },
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                    RuntimeType::Value(int.clone()),
                )),
                evidence: Some(typed_ir::ApplyEvidence {
                    callee_source_edge: None,
                    arg_source_edge: None,
                    callee: typed_ir::TypeBounds::default(),
                    expected_callee: None,
                    arg: typed_ir::TypeBounds::exact(int.clone()),
                    expected_arg: Some(typed_ir::TypeBounds::exact(int.clone())),
                    result: typed_ir::TypeBounds::exact(unit.clone()),
                    principal_callee: None,
                    substitutions: Vec::new(),
                    substitution_candidates: Vec::new(),
                    role_method: false,
                    principal_elaboration: None,
                }),
                instantiation: None,
            },
            RuntimeType::Value(unit),
        );

        let materialized = materialize::materialize_expr(apply, &[]);
        let ExprKind::Apply { arg, .. } = materialized.kind else {
            panic!("expected apply expression");
        };
        let ExprKind::Coerce { from, to, expr } = arg.kind else {
            panic!("expected arg to be coerced to callee param");
        };

        assert_eq!(from, int);
        assert_eq!(to, float);
        assert!(matches!(expr.kind, ExprKind::Lit(typed_ir::Lit::Int(_))));
    }

    #[test]
    fn materialize_apply_result_prefers_closed_callee_return_over_result_evidence() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let float = typed_ir::Type::Named {
            path: path("float"),
            args: Vec::new(),
        };
        let int_to_int = typed_ir::Type::Fun {
            param: Box::new(int.clone()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(int.clone()),
        };
        let stale_result = typed_ir::Type::Fun {
            param: Box::new(float),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(int.clone()),
        };
        let inner = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path("add")),
                    RuntimeType::Fun {
                        param: Box::new(RuntimeType::Value(int.clone())),
                        ret: Box::new(RuntimeType::Value(int_to_int.clone())),
                    },
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                    RuntimeType::Value(int.clone()),
                )),
                evidence: Some(typed_ir::ApplyEvidence {
                    callee_source_edge: None,
                    arg_source_edge: None,
                    callee: typed_ir::TypeBounds::default(),
                    expected_callee: None,
                    arg: typed_ir::TypeBounds::exact(int.clone()),
                    expected_arg: Some(typed_ir::TypeBounds::exact(int.clone())),
                    result: typed_ir::TypeBounds::exact(stale_result),
                    principal_callee: None,
                    substitutions: Vec::new(),
                    substitution_candidates: Vec::new(),
                    role_method: false,
                    principal_elaboration: None,
                }),
                instantiation: None,
            },
            RuntimeType::Unknown,
        );
        let outer = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(inner),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("2".into())),
                    RuntimeType::Value(int.clone()),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Unknown,
        );

        let materialized = materialize::materialize_expr(outer, &[]);
        let ExprKind::Apply { callee, arg, .. } = materialized.kind else {
            panic!("expected outer apply");
        };

        assert_eq!(
            callee.ty,
            RuntimeType::Fun {
                param: Box::new(RuntimeType::Value(int.clone())),
                ret: Box::new(RuntimeType::Value(int)),
            }
        );
        assert!(matches!(arg.kind, ExprKind::Lit(typed_ir::Lit::Int(_))));
    }

    #[test]
    fn materialize_if_branches_to_join_result() {
        let result = typed_ir::TypeVar("result".into());
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let user_id = typed_ir::Type::Named {
            path: path("user_id"),
            args: Vec::new(),
        };
        let if_expr = Expr::typed(
            ExprKind::If {
                cond: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Bool(true)),
                    RuntimeType::Unknown,
                )),
                then_branch: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                    RuntimeType::Value(int.clone()),
                )),
                else_branch: Box::new(Expr::typed(
                    ExprKind::Var(path("fallback")),
                    RuntimeType::Value(user_id.clone()),
                )),
                evidence: Some(yulang_runtime_ir::JoinEvidence {
                    result: typed_ir::Type::Var(result.clone()),
                }),
            },
            RuntimeType::Value(typed_ir::Type::Var(result.clone())),
        );

        let materialized = materialize::materialize_expr(
            if_expr,
            &[typed_ir::TypeSubstitution {
                var: result,
                ty: user_id.clone(),
            }],
        );

        assert_eq!(materialized.ty, RuntimeType::Value(user_id.clone()));
        let ExprKind::If {
            then_branch,
            else_branch,
            evidence,
            ..
        } = materialized.kind
        else {
            panic!("expected if expression");
        };
        assert_eq!(evidence.expect("join evidence").result, user_id.clone());
        assert_eq!(else_branch.ty, RuntimeType::Value(user_id.clone()));
        let ExprKind::Coerce { from, to, expr } = then_branch.kind else {
            panic!("expected then branch to be coerced to join result");
        };
        assert_eq!(from, int);
        assert_eq!(to, user_id);
        assert!(matches!(expr.kind, ExprKind::Lit(typed_ir::Lit::Int(_))));
    }

    #[test]
    fn semantic_cast_normalization_expands_closed_coerce_to_cast_call() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let user_id = typed_ir::Type::Named {
            path: path("user_id"),
            args: Vec::new(),
        };
        let method = path("cast_int_to_user_id");
        let coerce = Expr::typed(
            ExprKind::Coerce {
                from: int.clone(),
                to: user_id.clone(),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                    RuntimeType::Value(int.clone()),
                )),
            },
            RuntimeType::Value(user_id.clone()),
        );
        let mut module = Module {
            path: path("test"),
            bindings: Vec::new(),
            root_exprs: vec![coerce],
            roots: vec![Root::Expr(0)],
            role_impls: vec![typed_ir::RoleImplGraphNode {
                role: path("Cast"),
                inputs: vec![typed_ir::TypeBounds::exact(int.clone())],
                associated_types: vec![typed_ir::RecordField {
                    name: typed_ir::Name("to".into()),
                    value: typed_ir::TypeBounds::exact(user_id.clone()),
                    optional: false,
                }],
                members: vec![typed_ir::RecordField {
                    name: typed_ir::Name("cast".into()),
                    value: method.clone(),
                    optional: false,
                }],
            }],
        };

        cast::normalize_semantic_cast_coercions(&mut module);

        let ExprKind::Apply { callee, arg, .. } = &module.root_exprs[0].kind else {
            panic!("expected semantic cast call");
        };
        assert!(matches!(arg.kind, ExprKind::Lit(typed_ir::Lit::Int(_))));
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected cast method callee");
        };
        assert_eq!(callee_path, &method);
        assert_eq!(module.root_exprs[0].ty, RuntimeType::Value(user_id));
    }

    #[test]
    fn runtime_function_projection_preserves_thunk_effect_slots() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let bool_ty = typed_ir::Type::Named {
            path: path("bool"),
            args: Vec::new(),
        };
        let arg_effect = typed_ir::Type::Named {
            path: path("arg_effect"),
            args: Vec::new(),
        };
        let ret_effect = typed_ir::Type::Named {
            path: path("ret_effect"),
            args: Vec::new(),
        };

        let projected = runtime_type_to_core(RuntimeType::Fun {
            param: Box::new(RuntimeType::Thunk {
                effect: arg_effect.clone(),
                value: Box::new(RuntimeType::Value(int.clone())),
            }),
            ret: Box::new(RuntimeType::Thunk {
                effect: ret_effect.clone(),
                value: Box::new(RuntimeType::Value(bool_ty.clone())),
            }),
        });

        assert_eq!(
            projected,
            typed_ir::Type::Fun {
                param: Box::new(int),
                param_effect: Box::new(arg_effect),
                ret_effect: Box::new(ret_effect),
                ret: Box::new(bool_ty),
            }
        );
    }

    #[test]
    fn materialize_handle_type_from_materialized_evidence() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let stale_unit = RuntimeType::Value(unit_type());
        let handle = Expr::typed(
            ExprKind::Handle {
                body: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    stale_unit.clone(),
                )),
                arms: Vec::new(),
                evidence: yulang_runtime_ir::JoinEvidence {
                    result: typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                },
                handler: yulang_runtime_ir::HandleEffect {
                    consumes: Vec::new(),
                    residual_before: None,
                    residual_after: None,
                },
            },
            stale_unit,
        );

        let materialized = materialize::materialize_expr(
            handle,
            &[typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int.clone(),
            }],
        );

        assert_eq!(materialized.ty, RuntimeType::Value(int.clone()));
        let ExprKind::Handle { evidence, .. } = materialized.kind else {
            panic!("expected handle expression");
        };
        assert_eq!(evidence.result, int);
    }

    #[test]
    fn cached_std_runtime_ir_cache_can_enter_runtime_finalize() {
        let cache_start = std::time::Instant::now();
        let cached =
            runtime_module_from_source_with_std_dependency_cache_large_stack("\"hello\".println\n");
        let cache_read = cache_start.elapsed();

        assert!(!cached.dependency_manifests.is_empty());

        let finalize_start = std::time::Instant::now();
        let output = finalize_module(cached.module).unwrap();
        let finalize = finalize_start.elapsed();
        eprintln!(
            "cached std runtime-ir finalize profile: cache_read={:?} finalize={:?}",
            cache_read, finalize
        );

        assert_eq!(output.module.root_exprs.len(), 1);
    }

    #[test]
    fn cached_std_finalize_runs_ref_scalar_assignment() {
        let results = finalized_int_values_from_std_dependency_cache(
            r#"{
    my $x = 10
    &x = 11
    $x
}
"#,
        );

        assert_eq!(results, vec!["11".to_string()]);
    }

    #[test]
    fn cached_std_finalize_compiles_ref_assignment_from_ref_read() {
        assert_std_dependency_cache_ref_source_finalizes_to_vm_input(
            r#"{
    my $x = 13
    my $y = 0

    &y = $x

    $y
}
"#,
        );
    }

    #[test]
    fn legacy_runtime_and_finalize_match_small_sources_without_std() {
        for case in [
            RuntimeOracleCase {
                name: "identity",
                source: "my id x = x\nid 1\n",
            },
            RuntimeOracleCase {
                name: "lexical block",
                source: r#"my f x = {
    my y = x
    y
}
f 3
"#,
            },
            RuntimeOracleCase {
                name: "first argument",
                source: "my first x y = x\nfirst 1 true\n",
            },
            RuntimeOracleCase {
                name: "tuple payload",
                source: "my pair x y = (x, y)\npair 1 true\n",
            },
        ] {
            assert_legacy_and_finalize_match_without_std(case);
        }
    }

    #[test]
    fn cached_std_legacy_runtime_and_finalize_match_playground_core_examples() {
        for case in [
            RuntimeOracleCase {
                name: "prelude operators",
                source: r#"1 + 2
2 * 3
1 == 1
1 < 2
2 <= 2
"#,
            },
            RuntimeOracleCase {
                name: "undet list",
                source: r#"(each [1, 2, 3] + each [4, 5, 6]).list
"#,
            },
            RuntimeOracleCase {
                name: "undet once range",
                source: r#"{
    my a = each 1..
    guard: a == 3
    a
}.once
"#,
            },
        ] {
            assert_legacy_and_finalize_match_with_std_dependency_cache(case);
        }
    }

    #[test]
    fn cached_std_legacy_runtime_and_finalize_match_playground_state_examples() {
        for case in [
            RuntimeOracleCase {
                name: "ref list assignment",
                source: r#"{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}
"#,
            },
            RuntimeOracleCase {
                name: "console output",
                source: r#"println "hello"
1 + 2
"#,
            },
            RuntimeOracleCase {
                name: "callback hygiene",
                source: r#"// Callback effects are hygienic:
// a callback's return is not captured by g's local sub.

use std::*
use std::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \i -> if i == 0: return i
    println b.show
    2
"#,
            },
        ] {
            assert_legacy_and_finalize_match_with_std_dependency_cache(case);
        }
    }

    #[test]
    fn cached_std_legacy_runtime_and_finalize_match_playground_tour() {
        assert_legacy_and_finalize_match_with_std_dependency_cache(RuntimeOracleCase {
            name: "playground tour",
            source: playground_tour_source(),
        });
    }

    #[test]
    fn control_vm_legacy_runtime_and_finalize_match_small_sources_without_std() {
        for case in [
            RuntimeOracleCase {
                name: "identity",
                source: "my id x = x\nid 1\n",
            },
            RuntimeOracleCase {
                name: "lexical block",
                source: r#"my f x = {
    my y = x
    y
}
f 3
"#,
            },
            RuntimeOracleCase {
                name: "tuple payload",
                source: "my pair x y = (x, y)\npair 1 true\n",
            },
        ] {
            assert_legacy_and_finalize_match_without_std_on_vm(case, OracleVm::Control);
        }
    }

    #[test]
    fn cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples() {
        for case in [
            RuntimeOracleCase {
                name: "prelude operators",
                source: r#"1 + 2
2 * 3
1 == 1
"#,
            },
            RuntimeOracleCase {
                name: "ref list assignment",
                source: r#"{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}
"#,
            },
            RuntimeOracleCase {
                name: "callback hygiene",
                source: r#"// Callback effects are hygienic:
// a callback's return is not captured by g's local sub.

use std::*
use std::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \i -> if i == 0: return i
    println b.show
    2
"#,
            },
        ] {
            assert_legacy_and_finalize_match_with_std_dependency_cache_on_vm(
                case,
                OracleVm::Control,
            );
        }
    }

    #[test]
    fn cached_std_legacy_runtime_and_finalize_match_examples() {
        for case in example_oracle_cases() {
            assert_legacy_and_finalize_match_with_std_dependency_cache(case);
        }
    }

    #[test]
    fn cached_std_finalize_accepts_showcase_example() {
        assert_std_dependency_cache_ref_source_finalizes_to_vm_input(&playground_source(
            include_str!("../../../../examples/showcase.yu"),
        ));
    }

    #[test]
    fn cached_std_finalize_accepts_refs_example() {
        // The legacy monomorphizer still loses the `+` receiver through the
        // compiled dependency path; keep this as a finalize-only mainline gate.
        assert_std_dependency_cache_ref_source_finalizes_to_vm_input(&playground_source(
            include_str!("../../../../examples/02_refs.yu"),
        ));
    }

    #[test]
    fn cached_std_finalize_runs_playground_core_examples() {
        for case in [
            PlaygroundCase {
                name: "undet list",
                source: r#"(each [1, 2, 3] + each [4, 5, 6]).list
"#,
                stdout: "",
                results: &["[5, 6, 7, 6, 7, 8, 7, 8, 9]"],
            },
            PlaygroundCase {
                name: "undet once range",
                source: r#"{
    my a = each 1..
    guard: a == 3
    a
}.once
"#,
                stdout: "",
                results: &["just 3"],
            },
            PlaygroundCase {
                name: "undet pythagorean",
                source: r#"({
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
}).once
"#,
                stdout: "",
                results: &["just (3, 4, 5)"],
            },
            PlaygroundCase {
                name: "prelude operators",
                source: r#"1 + 2
2 * 3
1 == 1
1 < 2
2 <= 2
"#,
                stdout: "",
                results: &["3", "6", "true", "true", "true"],
            },
            PlaygroundCase {
                name: "multiple roots",
                source: r#"1 + 2
3 + 4
"#,
                stdout: "",
                results: &["3", "7"],
            },
        ] {
            assert_playground_case_finalizes(case);
        }
    }

    #[test]
    fn cold_std_finalize_runs_range_each_sum_without_prewarmed_cache() {
        let source = playground_source("((1..3).each + (1..3).each).list\n");
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_cold_std_dependency_cache_large_stack(
                &source,
                "cold-range-each",
            );
            let output = finalize_module(cached.module)
                .unwrap_or_else(|error| panic!("cold range each finalize failed: {error:?}"));
            let vm = yulang_vm::compile_vm_module(output.module)
                .unwrap_or_else(|error| panic!("cold range each VM compile failed: {error:?}"));
            let host_output = yulang_vm::eval_roots_with_basic_host(&vm)
                .unwrap_or_else(|error| panic!("cold range each VM eval failed: {error:?}"));
            let actual = host_output
                .results
                .iter()
                .map(format_vm_result)
                .collect::<Vec<_>>();
            assert_eq!(actual, ["[2, 3, 4, 3, 4, 5, 4, 5, 6]"]);
        });
    }

    #[test]
    fn cached_std_finalize_runs_playground_state_and_host_examples() {
        for case in [
            PlaygroundCase {
                name: "ref list assignment",
                source: r#"{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}
"#,
                stdout: "",
                results: &["[2, 6, 4]"],
            },
            PlaygroundCase {
                name: "console output",
                source: r#"println "hello"
1 + 2
"#,
                stdout: "hello\n",
                results: &["()", "3"],
            },
            PlaygroundCase {
                name: "callback hygiene",
                source: r#"// Callback effects are hygienic:
// a callback's return is not captured by g's local sub.

use std::*
use std::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \i -> if i == 0: return i
    println b.show
    2
"#,
                stdout: "",
                results: &["0"],
            },
        ] {
            assert_playground_case_finalizes(case);
        }
    }

    #[test]
    fn cached_std_finalize_runs_playground_tour() {
        assert_playground_case_finalizes(PlaygroundCase {
            name: "playground tour",
            source: playground_tour_source(),
            stdout: "",
            results: &["7", "[2, 6, 4]", "5", "just 18"],
        });
    }

    #[test]
    fn std_no_cache_finalize_runs_reported_graph_unification_regressions() {
        for case in [
            PlaygroundCase {
                name: "handler function preserves effectful argument boundary",
                source: r#"act log:
    pub put: str -> ()

my collect_logs(comp: [_] _) = catch comp:
    log::put _, k -> k ()
    v -> v

collect_logs: log::put "a"
"#,
                stdout: "",
                results: &["()"],
            },
            PlaygroundCase {
                name: "handler function with state preserves effectful argument boundary",
                source: r#"act log:
    pub put: str -> ()

my collect_logs(comp: [_] _) =
    my $count = 0
    catch comp:
        log::put _, k ->
            &count = $count + 1
            k ()
        v -> v
    $count

collect_logs: log::put "a"
"#,
                stdout: "",
                results: &["1"],
            },
            PlaygroundCase {
                name: "record pattern field receiver feeds role method",
                source: r#"my f { port: p } = p.show
f { port: 8080 }
"#,
                stdout: "",
                results: &["\"8080\""],
            },
            PlaygroundCase {
                name: "record default field receiver feeds role method",
                source: r#"my f { port = 80 } = port.show
f {}
"#,
                stdout: "",
                results: &["\"80\""],
            },
            PlaygroundCase {
                name: "list index raw preserves callback function element",
                source: r#"use std::flow::*

our f() = return 0

our g h = sub:
    my hs = [h]
    ((std::list::index_raw hs) 0)()
    return 1

sub:
    my b = g f
    2
"#,
                stdout: "",
                results: &["0"],
            },
        ] {
            assert_std_source_no_cache_finalizes_to_results(case);
        }
    }

    // TODO: re-enable once the synthetic `error`/`Throw` role resolution
    // closes the role-method bound in finalize (or at runtime). Currently
    // `fail e` / `e.throw` inside `fs_err::wrap:` leaves the apply graph for
    // `#op:prefix:fail` with an unresolved `Throw<_, throws = γ>` constraint,
    // so finalize either raises `IncompleteGraph` (with `fail`) or the VM
    // sees the role method as an unhandled request (with explicit `.throw`).
    #[test]
    #[ignore = "tracked: synthetic error wrap leaves Throw role unresolved in finalize"]
    fn std_no_cache_finalize_runs_error_wrap_fail_flow_regressions() {
        for case in [
            PlaygroundCase {
                name: "error wrap fail flow keeps carrier and payload apart",
                source: r#"error fs_err:
    not_found str

my read_or_throw(p: str): [fs_err] str =
    fail fs_err::not_found p

my safe_read(p: str): result str fs_err = fs_err::wrap:
    read_or_throw p

safe_read "missing"
"#,
                stdout: "",
                results: &["err not_found \"missing\""],
            },
            PlaygroundCase {
                name: "inline conditional wrap keeps error carrier and payload apart",
                source: r#"error fail_err:
    bad str

fail_err::wrap:
    if true: fail fail_err::bad "x"
    else: 1
"#,
                stdout: "",
                results: &["err bad \"x\""],
            },
        ] {
            assert_std_source_no_cache_finalizes_to_results(case);
        }
    }

    #[test]
    #[ignore = "diagnostic: report typed/untyped expression coverage"]
    fn rina_finalize_type_coverage_report() {
        let src = r#"{
    my $x = 0
    {
        &x = 9
    }
    $x
}
"#
        .to_string();
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&src);
            let output = finalize_module(cached.module).unwrap();
            let mut stats = TypeCoverageStats::default();
            for binding in &output.module.bindings {
                stats.set_owner(format!("binding {:?}", binding.name));
                walk_expr_for_coverage(&binding.body, &mut stats);
            }
            for (i, expr) in output.module.root_exprs.iter().enumerate() {
                stats.set_owner(format!("root_expr[{i}]"));
                walk_expr_for_coverage(expr, &mut stats);
            }
            eprintln!("=== type coverage report ===");
            eprintln!("total: {}", stats.total);
            eprintln!("concrete: {}", stats.concrete);
            eprintln!("with Unknown: {}", stats.with_unknown);
            eprintln!("with Var: {}", stats.with_var);
            eprintln!("by kind missing concrete:");
            let mut entries: Vec<_> = stats.by_kind_unconcrete.iter().collect();
            entries.sort_by_key(|(k, _)| k.to_string());
            for (kind, count) in entries {
                eprintln!("  {kind}: {count}");
            }
            eprintln!("by owner missing concrete:");
            let mut owner_entries: Vec<_> = stats.by_owner_unconcrete.iter().collect();
            owner_entries.sort_by_key(|(o, _)| *o);
            for (owner, count) in owner_entries {
                eprintln!("  {owner}: {count}");
            }
            eprintln!("=== first 40 unconcrete samples ===");
            for (i, sample) in stats.samples.iter().enumerate().take(40) {
                eprintln!("  [{i}] {sample}");
            }
        });
    }

    #[derive(Default)]
    struct TypeCoverageStats {
        total: usize,
        concrete: usize,
        with_unknown: usize,
        with_var: usize,
        by_kind_unconcrete: std::collections::BTreeMap<&'static str, usize>,
        by_owner_unconcrete: std::collections::BTreeMap<String, usize>,
        samples: Vec<String>,
        current_owner: String,
    }

    impl TypeCoverageStats {
        fn set_owner(&mut self, owner: String) {
            self.current_owner = owner;
        }
    }

    fn expr_kind_tag(expr: &Expr) -> &'static str {
        match &expr.kind {
            ExprKind::Var(_) => "Var",
            ExprKind::EffectOp(_) => "EffectOp",
            ExprKind::PrimitiveOp(_) => "PrimitiveOp",
            ExprKind::Lit(_) => "Lit",
            ExprKind::Lambda { .. } => "Lambda",
            ExprKind::Apply { .. } => "Apply",
            ExprKind::If { .. } => "If",
            ExprKind::Tuple(_) => "Tuple",
            ExprKind::Record { .. } => "Record",
            ExprKind::Variant { .. } => "Variant",
            ExprKind::Select { .. } => "Select",
            ExprKind::Match { .. } => "Match",
            ExprKind::Block { .. } => "Block",
            ExprKind::Handle { .. } => "Handle",
            ExprKind::BindHere { .. } => "BindHere",
            ExprKind::Thunk { .. } => "Thunk",
            ExprKind::LocalPushId { .. } => "LocalPushId",
            ExprKind::PeekId => "PeekId",
            ExprKind::FindId { .. } => "FindId",
            ExprKind::AddId { .. } => "AddId",
            ExprKind::Coerce { .. } => "Coerce",
            ExprKind::Pack { .. } => "Pack",
        }
    }

    fn type_has_unknown(ty: &RuntimeType) -> bool {
        match ty {
            RuntimeType::Unknown => true,
            RuntimeType::Value(ty) => core_type_contains_unknown(ty),
            RuntimeType::Fun { param, ret } => type_has_unknown(param) || type_has_unknown(ret),
            RuntimeType::Thunk { effect, value } => {
                core_type_contains_unknown(effect) || type_has_unknown(value)
            }
        }
    }

    fn type_has_var(ty: &RuntimeType) -> bool {
        match ty {
            RuntimeType::Unknown => false,
            RuntimeType::Value(ty) => core_type_contains_var(ty),
            RuntimeType::Fun { param, ret } => type_has_var(param) || type_has_var(ret),
            RuntimeType::Thunk { effect, value } => {
                core_type_contains_var(effect) || type_has_var(value)
            }
        }
    }

    fn core_type_contains_unknown(ty: &typed_ir::Type) -> bool {
        match ty {
            typed_ir::Type::Unknown => true,
            typed_ir::Type::Var(_) | typed_ir::Type::Never | typed_ir::Type::Any => false,
            typed_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
                typed_ir::TypeArg::Type(t) => core_type_contains_unknown(t),
                typed_ir::TypeArg::Bounds(b) => {
                    b.lower.as_deref().is_some_and(core_type_contains_unknown)
                        || b.upper.as_deref().is_some_and(core_type_contains_unknown)
                }
            }),
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                core_type_contains_unknown(param)
                    || core_type_contains_unknown(param_effect)
                    || core_type_contains_unknown(ret_effect)
                    || core_type_contains_unknown(ret)
            }
            typed_ir::Type::Tuple(items)
            | typed_ir::Type::Union(items)
            | typed_ir::Type::Inter(items) => items.iter().any(core_type_contains_unknown),
            typed_ir::Type::Row { items, tail } => {
                items.iter().any(core_type_contains_unknown) || core_type_contains_unknown(tail)
            }
            typed_ir::Type::Record(record) => record
                .fields
                .iter()
                .any(|f| core_type_contains_unknown(&f.value)),
            typed_ir::Type::Variant(variant) => variant
                .cases
                .iter()
                .any(|c| c.payloads.iter().any(core_type_contains_unknown)),
            typed_ir::Type::Recursive { body, .. } => core_type_contains_unknown(body),
        }
    }

    fn core_type_contains_var(ty: &typed_ir::Type) -> bool {
        match ty {
            typed_ir::Type::Var(_) => true,
            typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => false,
            typed_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
                typed_ir::TypeArg::Type(t) => core_type_contains_var(t),
                typed_ir::TypeArg::Bounds(b) => {
                    b.lower.as_deref().is_some_and(core_type_contains_var)
                        || b.upper.as_deref().is_some_and(core_type_contains_var)
                }
            }),
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                core_type_contains_var(param)
                    || core_type_contains_var(param_effect)
                    || core_type_contains_var(ret_effect)
                    || core_type_contains_var(ret)
            }
            typed_ir::Type::Tuple(items)
            | typed_ir::Type::Union(items)
            | typed_ir::Type::Inter(items) => items.iter().any(core_type_contains_var),
            typed_ir::Type::Row { items, tail } => {
                items.iter().any(core_type_contains_var) || core_type_contains_var(tail)
            }
            typed_ir::Type::Record(record) => record
                .fields
                .iter()
                .any(|f| core_type_contains_var(&f.value)),
            typed_ir::Type::Variant(variant) => variant
                .cases
                .iter()
                .any(|c| c.payloads.iter().any(core_type_contains_var)),
            typed_ir::Type::Recursive { body, .. } => core_type_contains_var(body),
        }
    }

    fn walk_expr_for_coverage(expr: &Expr, stats: &mut TypeCoverageStats) {
        stats.total += 1;
        let kind = expr_kind_tag(expr);
        let has_unknown = type_has_unknown(&expr.ty);
        let has_var = type_has_var(&expr.ty);
        if has_unknown {
            stats.with_unknown += 1;
        }
        if has_var {
            stats.with_var += 1;
        }
        if has_unknown || has_var {
            *stats.by_kind_unconcrete.entry(kind).or_default() += 1;
            *stats
                .by_owner_unconcrete
                .entry(stats.current_owner.clone())
                .or_default() += 1;
            if stats.samples.len() < 40 {
                let owner = stats.current_owner.clone();
                let detail = match &expr.kind {
                    ExprKind::Var(path) => format!("Var({path:?})"),
                    ExprKind::EffectOp(path) => format!("EffectOp({path:?})"),
                    _ => kind.to_string(),
                };
                stats
                    .samples
                    .push(format!("[{owner}] {detail} ty={:?}", &expr.ty));
            }
        } else {
            stats.concrete += 1;
        }
        match &expr.kind {
            ExprKind::Lambda { body, .. }
            | ExprKind::BindHere { expr: body }
            | ExprKind::LocalPushId { body, .. }
            | ExprKind::AddId { thunk: body, .. }
            | ExprKind::Coerce { expr: body, .. }
            | ExprKind::Pack { expr: body, .. }
            | ExprKind::Thunk { expr: body, .. } => walk_expr_for_coverage(body, stats),
            ExprKind::Apply { callee, arg, .. } => {
                walk_expr_for_coverage(callee, stats);
                walk_expr_for_coverage(arg, stats);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                walk_expr_for_coverage(cond, stats);
                walk_expr_for_coverage(then_branch, stats);
                walk_expr_for_coverage(else_branch, stats);
            }
            ExprKind::Tuple(items) => {
                for item in items {
                    walk_expr_for_coverage(item, stats);
                }
            }
            ExprKind::Record { fields, spread } => {
                for field in fields {
                    walk_expr_for_coverage(&field.value, stats);
                }
                if let Some(spread) = spread {
                    let e = match spread {
                        yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(e)
                        | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(e) => e,
                    };
                    walk_expr_for_coverage(e, stats);
                }
            }
            ExprKind::Variant { value, .. } => {
                if let Some(value) = value {
                    walk_expr_for_coverage(value, stats);
                }
            }
            ExprKind::Select { base, .. } => walk_expr_for_coverage(base, stats),
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                walk_expr_for_coverage(scrutinee, stats);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        walk_expr_for_coverage(guard, stats);
                    }
                    walk_expr_for_coverage(&arm.body, stats);
                }
            }
            ExprKind::Block { stmts, tail } => {
                for stmt in stmts {
                    match stmt {
                        yulang_runtime_ir::FinalizedStmt::Let { value, .. } => {
                            walk_expr_for_coverage(value, stats);
                        }
                        yulang_runtime_ir::FinalizedStmt::Expr(e) => {
                            walk_expr_for_coverage(e, stats)
                        }
                        yulang_runtime_ir::FinalizedStmt::Module { body, .. } => {
                            walk_expr_for_coverage(body, stats);
                        }
                    }
                }
                if let Some(tail) = tail {
                    walk_expr_for_coverage(tail, stats);
                }
            }
            ExprKind::Handle { body, arms, .. } => {
                walk_expr_for_coverage(body, stats);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        walk_expr_for_coverage(guard, stats);
                    }
                    walk_expr_for_coverage(&arm.body, stats);
                }
            }
            ExprKind::Var(_)
            | ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => {}
        }
    }

    #[test]
    fn cached_std_finalize_runs_ref_assignment_inside_nested_block() {
        let results = finalized_int_values_from_std_dependency_cache(
            r#"{
    my $x = 0
    {
        &x = 9
    }
    $x
}
"#,
        );

        assert_eq!(results, vec!["9".to_string()]);
    }

    #[test]
    fn cached_std_finalize_runs_ref_assignment_inside_nested_for_loops() {
        let results = finalized_int_values_from_std_dependency_cache(
            r#"{
    my $total = 0
    for x in 1..3:
        for y in 1..2:
            &total = $total + x + y
    $total
}
"#,
        );

        assert_eq!(results, vec!["21".to_string()]);
    }

    fn finalized_int_values_from_std_dependency_cache(src: &str) -> Vec<String> {
        let src = src.to_string();
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&src);
            let output = finalize_module(cached.module).unwrap();
            assert!(
                output
                    .module
                    .bindings
                    .iter()
                    .all(|binding| binding.type_params.is_empty())
            );
            let vm = yulang_vm::compile_vm_module(output.module).unwrap();
            vm.eval_roots()
                .unwrap()
                .into_iter()
                .map(|result| match result {
                    yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(value)) => value.to_string(),
                    yulang_vm::VmResult::Request(request) => {
                        let continuation = format!("{:?}", request.continuation);
                        panic!(
                            "expected int VM result, got request {:?}, blocked {:?}, handle_frames={}, bind_frames={}",
                            request.effect,
                            request.blocked_id,
                            continuation.matches("Handle {").count(),
                            continuation.matches("BindHere").count(),
                        )
                    }
                    other => panic!("expected int VM result, got {other:?}"),
                })
                .collect()
        })
    }

    fn assert_std_dependency_cache_ref_source_finalizes_to_vm_input(src: &str) {
        let src = src.to_string();
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&src);
            let output = finalize_module(cached.module).unwrap();
            assert!(
                output
                    .module
                    .bindings
                    .iter()
                    .all(|binding| binding.type_params.is_empty())
            );
            yulang_vm::compile_vm_module(output.module).unwrap();
        });
    }

    struct RuntimeOracleCase {
        name: &'static str,
        source: &'static str,
    }

    #[derive(Clone, Copy)]
    enum OracleVm {
        Tree,
        Control,
    }

    #[derive(Debug, PartialEq, Eq)]
    struct RuntimeOracleOutput {
        stdout: String,
        results: Vec<String>,
    }

    fn assert_legacy_and_finalize_match_without_std(case: RuntimeOracleCase) {
        assert_legacy_and_finalize_match_without_std_on_vm(case, OracleVm::Tree);
    }

    fn assert_legacy_and_finalize_match_without_std_on_vm(case: RuntimeOracleCase, vm: OracleVm) {
        let module = runtime_module_from_source_without_std(case.source);
        assert_legacy_and_finalize_match_module(case.name, module, vm);
    }

    fn assert_legacy_and_finalize_match_with_std_dependency_cache(case: RuntimeOracleCase) {
        assert_legacy_and_finalize_match_with_std_dependency_cache_on_vm(case, OracleVm::Tree);
    }

    fn assert_legacy_and_finalize_match_with_std_dependency_cache_on_vm(
        case: RuntimeOracleCase,
        vm: OracleVm,
    ) {
        let source = playground_source(case.source);
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&source);
            assert_legacy_and_finalize_match_module(case.name, cached.module, vm);
        });
    }

    fn example_oracle_cases() -> [RuntimeOracleCase; 12] {
        [
            RuntimeOracleCase {
                name: "01_struct_with",
                source: include_str!("../../../../examples/01_struct_with.yu"),
            },
            RuntimeOracleCase {
                name: "03_for_last",
                source: include_str!("../../../../examples/03_for_last.yu"),
            },
            RuntimeOracleCase {
                name: "04_sub_return",
                source: include_str!("../../../../examples/04_sub_return.yu"),
            },
            RuntimeOracleCase {
                name: "05_undet_all",
                source: include_str!("../../../../examples/05_undet_all.yu"),
            },
            RuntimeOracleCase {
                name: "06_undet_once",
                source: include_str!("../../../../examples/06_undet_once.yu"),
            },
            RuntimeOracleCase {
                name: "07_junction",
                source: include_str!("../../../../examples/07_junction.yu"),
            },
            RuntimeOracleCase {
                name: "08_types",
                source: include_str!("../../../../examples/08_types.yu"),
            },
            RuntimeOracleCase {
                name: "09_optional_record_args",
                source: include_str!("../../../../examples/09_optional_record_args.yu"),
            },
            RuntimeOracleCase {
                name: "10_effect_handler",
                source: include_str!("../../../../examples/10_effect_handler.yu"),
            },
            RuntimeOracleCase {
                name: "11_attached_impl",
                source: include_str!("../../../../examples/11_attached_impl.yu"),
            },
            RuntimeOracleCase {
                name: "12_cast",
                source: include_str!("../../../../examples/12_cast.yu"),
            },
            RuntimeOracleCase {
                name: "13_console",
                source: include_str!("../../../../examples/13_console.yu"),
            },
        ]
    }

    fn assert_legacy_and_finalize_match_module<M>(name: &str, module: M, vm: OracleVm)
    where
        M: IntoFinalizeRuntimeModule + Clone,
    {
        let legacy = run_legacy_runtime_module(name, module.clone(), vm);
        let finalized = run_finalize_runtime_module(name, module, vm);
        assert_eq!(finalized, legacy, "{name}");
    }

    fn run_legacy_runtime_module<M>(name: &str, module: M, vm: OracleVm) -> RuntimeOracleOutput
    where
        M: IntoFinalizeRuntimeModule,
    {
        run_finalize_runtime_module(name, module, vm)
    }

    fn run_finalize_runtime_module<M>(name: &str, module: M, vm: OracleVm) -> RuntimeOracleOutput
    where
        M: IntoFinalizeRuntimeModule,
    {
        let module = monomorphize_module(module)
            .unwrap_or_else(|error| panic!("{name} finalize failed: {error}"));
        run_vm_module(name, "finalize", module, vm)
    }

    fn run_vm_module(
        name: &str,
        runtime: &str,
        module: Module,
        vm: OracleVm,
    ) -> RuntimeOracleOutput {
        match vm {
            OracleVm::Tree => run_tree_vm_module(name, runtime, module),
            OracleVm::Control => run_control_vm_module(name, runtime, module),
        }
    }

    fn run_tree_vm_module(name: &str, runtime: &str, module: Module) -> RuntimeOracleOutput {
        let module = yulang_vm::compile_vm_module(module)
            .unwrap_or_else(|error| panic!("{name} {runtime} VM compile failed: {error:?}"));
        let host_output = yulang_vm::eval_roots_with_basic_host(&module)
            .unwrap_or_else(|error| panic!("{name} {runtime} VM eval failed: {error:?}"));
        RuntimeOracleOutput {
            stdout: host_output.stdout,
            results: host_output.results.iter().map(format_vm_result).collect(),
        }
    }

    fn run_control_vm_module(name: &str, runtime: &str, module: Module) -> RuntimeOracleOutput {
        let module = yulang_vm::compile_control_vm_module(module).unwrap_or_else(|error| {
            panic!("{name} {runtime} control VM compile failed: {error:?}")
        });
        let mut stdout = String::new();
        let mut results = Vec::with_capacity(module.root_count());
        for index in 0..module.root_count() {
            let (result, _) = module
                .eval_root_expr_with_basic_host_profiled(index, &mut stdout)
                .unwrap_or_else(|error| {
                    panic!("{name} {runtime} control VM eval failed: {error:?}")
                });
            results.push(format_vm_result(&result));
        }
        RuntimeOracleOutput { stdout, results }
    }

    struct PlaygroundCase {
        name: &'static str,
        source: &'static str,
        stdout: &'static str,
        results: &'static [&'static str],
    }

    fn assert_playground_case_finalizes(case: PlaygroundCase) {
        let source = playground_source(case.source);
        assert_std_source_finalizes_to_results_owned(case.name, source, case.stdout, case.results);
    }

    fn assert_std_source_no_cache_finalizes_to_results(case: PlaygroundCase) {
        let source = case.source.to_string();
        run_with_large_stack(move || {
            let module = runtime_module_from_source_with_std_no_cache(&source);
            let output = finalize_module(module)
                .unwrap_or_else(|error| panic!("{} finalize failed: {error:?}", case.name));
            let vm = yulang_vm::compile_vm_module(output.module)
                .unwrap_or_else(|error| panic!("{} VM compile failed: {error:?}", case.name));
            let host_output = yulang_vm::eval_roots_with_basic_host(&vm)
                .unwrap_or_else(|error| panic!("{} VM eval failed: {error:?}", case.name));
            let actual = host_output
                .results
                .iter()
                .map(format_vm_result)
                .collect::<Vec<_>>();
            assert_eq!(host_output.stdout, case.stdout, "{} stdout", case.name);
            assert_eq!(actual, case.results, "{} roots", case.name);
        });
    }

    fn assert_std_source_finalizes_to_results_owned(
        name: &'static str,
        source: String,
        stdout: &'static str,
        results: &'static [&'static str],
    ) {
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&source);
            let output = finalize_module(cached.module)
                .unwrap_or_else(|error| panic!("{name} finalize failed: {error:?}"));
            let vm = yulang_vm::compile_vm_module(output.module)
                .unwrap_or_else(|error| panic!("{name} VM compile failed: {error:?}"));
            let host_output = yulang_vm::eval_roots_with_basic_host(&vm)
                .unwrap_or_else(|error| panic!("{name} VM eval failed: {error:?}"));
            let actual = host_output
                .results
                .iter()
                .map(format_vm_result)
                .collect::<Vec<_>>();
            assert_eq!(host_output.stdout, stdout, "{name} stdout");
            assert_eq!(actual, results, "{name} roots");
        });
    }

    fn playground_source(source: &str) -> String {
        format!("use std::undet::*\n{source}")
    }

    fn playground_tour_source() -> &'static str {
        r#"// A compact tour of Yulang's current shape.

use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

my inflate({base = 1, extra = base + 1}) = base + extra

inflate { base: 3 }

{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}

sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0

({
    my y = if all [1, 2, 3] < any [2, 3, 4]:
        each [3, 4, 5]
    else:
        2

    point { x: 3, y: y } .norm2
}).once
"#
    }

    fn format_vm_result(result: &yulang_vm::VmResult) -> String {
        match result {
            yulang_vm::VmResult::Value(value) => format_vm_value(value),
            yulang_vm::VmResult::Request(request) => format!("<request {:?}>", request.effect),
        }
    }

    fn format_vm_value(value: &yulang_vm::VmValue) -> String {
        match value {
            yulang_vm::VmValue::Int(value) | yulang_vm::VmValue::Float(value) => value.clone(),
            yulang_vm::VmValue::String(value) => format!("{:?}", value.to_flat_string()),
            yulang_vm::VmValue::Bool(value) => value.to_string(),
            yulang_vm::VmValue::Unit => "()".to_string(),
            yulang_vm::VmValue::List(items) => {
                let mut out = String::from("[");
                format_vm_list_items(&mut out, items);
                out.push(']');
                out
            }
            yulang_vm::VmValue::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|value| format_vm_value(value))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({items})")
            }
            yulang_vm::VmValue::Record(fields) => {
                let fields = fields
                    .iter()
                    .map(|(name, value)| format!("{}: {}", name.0, format_vm_value(value)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{fields}}}")
            }
            yulang_vm::VmValue::Variant { tag, value } => match value {
                Some(value) => format!("{} {}", tag.0, format_vm_value(value)),
                None => tag.0.clone(),
            },
            yulang_vm::VmValue::Bytes(value) => format!("<bytes len={}>", value.len()),
            yulang_vm::VmValue::Path(value) => format!("{:?}", value.display().to_string()),
            yulang_vm::VmValue::FileHandle(_) => "<file>".to_string(),
            yulang_vm::VmValue::EffectOp(path) => format!("<effect-op {path:?}>"),
            yulang_vm::VmValue::PrimitiveOp(_) => "<primitive>".to_string(),
            yulang_vm::VmValue::Resume(_) => "<resume>".to_string(),
            yulang_vm::VmValue::Closure(_) => "<closure>".to_string(),
            yulang_vm::VmValue::Thunk(_) => "<thunk>".to_string(),
            yulang_vm::VmValue::EffectId(id) => format!("<effect-id {id}>"),
        }
    }

    fn format_vm_list_items(
        out: &mut String,
        items: &yulang_vm::runtime::list_tree::ListTree<std::rc::Rc<yulang_vm::VmValue>>,
    ) {
        match items {
            yulang_vm::runtime::list_tree::ListTree::Empty => {}
            yulang_vm::runtime::list_tree::ListTree::Leaf(value) => {
                out.push_str(&format_vm_value(value));
            }
            yulang_vm::runtime::list_tree::ListTree::Node(node) => {
                format_vm_list_items(out, &node.left);
                if !node.left.is_empty() && !node.right.is_empty() {
                    out.push_str(", ");
                }
                format_vm_list_items(out, &node.right);
            }
        }
    }

    fn id_call(arg: Expr) -> Expr {
        Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(ExprKind::Var(path("id")), RuntimeType::Unknown)),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Unknown,
        )
    }

    fn simple_apply_callee_path(expr: &Expr) -> Option<typed_ir::Path> {
        let ExprKind::Apply { callee, .. } = &expr.kind else {
            return None;
        };
        let ExprKind::Var(path) = &callee.kind else {
            return None;
        };
        Some(path.clone())
    }

    fn id_binding() -> Binding {
        Binding {
            name: path("id"),
            type_params: vec![typed_ir::TypeVar("a".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(typed_ir::Type::Never),
                    ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                },
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("x".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Var(path("x")),
                        RuntimeType::Value(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn poly_return_binding() -> Binding {
        Binding {
            name: path("poly_return"),
            type_params: vec![typed_ir::TypeVar("a".into()), typed_ir::TypeVar("b".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(typed_ir::Type::Never),
                    ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("b".into()))),
                },
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        }
    }

    fn int_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path("Int"),
            args: Vec::new(),
        }
    }

    fn bool_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path("Bool"),
            args: Vec::new(),
        }
    }

    fn named_core(name: &str, args: Vec<typed_ir::Type>) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(name),
            args: args.into_iter().map(typed_ir::TypeArg::Type).collect(),
        }
    }

    fn core_fun(
        param: typed_ir::Type,
        ret_effect: typed_ir::Type,
        ret: typed_ir::Type,
    ) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        }
    }

    fn path(name: impl IntoPathArg) -> typed_ir::Path {
        name.into_path()
    }

    trait IntoPathArg {
        fn into_path(self) -> typed_ir::Path;
    }

    impl IntoPathArg for &str {
        fn into_path(self) -> typed_ir::Path {
            typed_ir::Path::from_name(typed_ir::Name(self.into()))
        }
    }

    impl<const N: usize> IntoPathArg for &[&str; N] {
        fn into_path(self) -> typed_ir::Path {
            typed_ir::Path::new(
                self.iter()
                    .map(|segment| typed_ir::Name((*segment).into()))
                    .collect(),
            )
        }
    }

    fn runtime_module_from_source_without_std(src: &str) -> LoweredModule {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            src,
            None,
            yulang_infer::SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = yulang_infer::export_core_program(&mut lowered.state);
        yulang_runtime_lower::lower_core_program(program).unwrap()
    }

    fn runtime_module_from_source_with_std_no_cache(src: &str) -> LoweredModule {
        let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            src,
            Some(repo_root),
            yulang_infer::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = yulang_infer::export_core_program(&mut lowered.state);
        yulang_runtime_lower::lower_core_program(program).unwrap()
    }

    fn runtime_module_from_source_with_std_dependency_cache_large_stack(
        src: &str,
    ) -> yulang_runtime_pipeline::CachedLoweredRuntimeModule {
        let src = src.to_string();
        run_with_large_stack(move || {
            let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
            // Compiled dependency artifacts carry format/source hashes, so a
            // stable test root can reuse valid std cache across cargo runs
            // while read errors still fall back to warming this same cache.
            let cache_paths = yulang_runtime_pipeline::YulangCachePaths::with_user_cache_root(
                &repo_root,
                persistent_artifact_cache_root(&repo_root, "std-runtime-ir"),
            );
            let std_root = repo_root.join("lib/std");
            let options = yulang_runtime_pipeline::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            };
            let _guard = std_runtime_ir_cache_lock()
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());

            if let Ok(cached) =
                yulang_runtime_pipeline::lowered_runtime_module_from_virtual_source_with_dependency_cache_read_only(
                    &src,
                    Some(repo_root.clone()),
                    options.clone(),
                    &cache_paths,
                )
            {
                return cached;
            }

            yulang_runtime_pipeline::lowered_runtime_module_from_virtual_source_with_dependency_cache(
                &src,
                Some(repo_root),
                options,
                &cache_paths,
            )
            .expect("lower std runtime IR with dependency cache fallback")
        })
    }

    fn runtime_module_from_source_with_cold_std_dependency_cache_large_stack(
        src: &str,
        cache_name: &str,
    ) -> yulang_runtime_pipeline::CachedLoweredRuntimeModule {
        let src = src.to_string();
        let cache_name = cache_name.to_string();
        run_with_large_stack(move || {
            let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
            let cache_root = artifact_cache_root(&cache_name);
            let _ = std::fs::remove_dir_all(&cache_root);
            let cache_paths = yulang_runtime_pipeline::YulangCachePaths::with_user_cache_root(
                &repo_root,
                &cache_root,
            );
            let std_root = repo_root.join("lib/std");
            let options = yulang_runtime_pipeline::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            };
            let cached =
                yulang_runtime_pipeline::lowered_runtime_module_from_virtual_source_with_dependency_cache(
                    &src,
                    Some(repo_root),
                    options,
                    &cache_paths,
                )
                .expect("lower std runtime IR with cold dependency cache");
            let _ = std::fs::remove_dir_all(&cache_root);
            cached
        })
    }

    fn std_runtime_ir_cache_lock() -> &'static std::sync::Mutex<()> {
        static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        LOCK.get_or_init(|| std::sync::Mutex::new(()))
    }

    fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
    where
        T: Send + 'static,
    {
        if std::thread::current().name() == Some("runtime-finalize-large-stack") {
            return f();
        }
        let _guard = large_stack_test_lock()
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        std::thread::Builder::new()
            .name("runtime-finalize-large-stack".into())
            .stack_size(512 * 1024 * 1024)
            .spawn(f)
            .expect("spawn large-stack runtime-finalize test thread")
            .join()
            .expect("large-stack runtime-finalize test panicked")
    }

    fn large_stack_test_lock() -> &'static std::sync::Mutex<()> {
        static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        LOCK.get_or_init(|| std::sync::Mutex::new(()))
    }

    fn artifact_cache_root(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "yulang-finalize-cache-{name}-{}",
            std::process::id()
        ))
    }

    fn persistent_artifact_cache_root(
        repo_root: &std::path::Path,
        name: &str,
    ) -> std::path::PathBuf {
        repo_root.join("target/yulang/test-cache").join(name)
    }

    fn compiled_manifest(unit_index: usize, hash: u64) -> CompiledUnitManifest {
        CompiledUnitManifest {
            artifact_format_version: 17,
            parser_format_version: 1,
            unit_index,
            origin: SourceCompilationUnitOrigin::Std,
            realms: Vec::new(),
            bands: Vec::new(),
            files: vec![CompiledSourceFileIdentity {
                path: format!("std/{unit_index}.yu"),
                module_path: path(&["std", "cache_test"]),
                origin: SourceOrigin::Std,
                source_len: 10,
                source_hash: hash,
            }],
            dependencies: (unit_index > 0)
                .then(|| CompiledUnitDependency {
                    unit_index: unit_index - 1,
                    source_hash: hash - 1,
                    interface_hash: hash + 1,
                })
                .into_iter()
                .collect(),
            source_hash: hash,
            syntax_hash: hash + 10,
            interface_hash: hash + 20,
        }
    }
}
