#[cfg(test)]
mod tests {
    use super::super::*;

    #[test]
    pub(super) fn lower_literal_root_uses_graph_type() {
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(named_type("int")),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");

        assert_eq!(core_type(&module.root_exprs[0].ty), &named_type("int"));
    }

    #[test]
    pub(super) fn lower_literal_uses_graph_primitive_type_metadata() {
        let custom_int = typed_ir::Path::new(vec![
            typed_ir::Name("runtime".to_string()),
            typed_ir::Name("int".to_string()),
        ]);
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
                }],
                primitive_types: vec![typed_ir::PrimitiveTypeGraphNode {
                    family: typed_ir::PrimitiveTypeFamily::Int,
                    path: custom_int.clone(),
                }],
                ..typed_ir::CoreGraphView::default()
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");

        assert_eq!(
            core_type(&module.root_exprs[0].ty),
            &typed_ir::Type::Named {
                path: custom_int,
                args: Vec::new(),
            }
        );
    }

    #[test]
    pub(super) fn lower_root_erases_principal_vars_from_graph_bounds() {
        let principal_var = typed_ir::TypeVar("a".to_string());
        let id_path = typed_ir::Path::from_name(typed_ir::Name("id".to_string()));
        let list_with_principal_var = typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
            args: vec![typed_ir::TypeArg::Type(typed_ir::Type::Union(vec![
                typed_ir::Type::Var(principal_var.clone()),
                named_type("int"),
            ]))],
        };
        let list_of_int = typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
            args: vec![typed_ir::TypeArg::Type(named_type("int"))],
        };
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![typed_ir::PrincipalBinding {
                    name: id_path,
                    scheme: typed_ir::Scheme {
                        requirements: Vec::new(),
                        body: typed_ir::Type::Var(principal_var),
                    },
                    body: typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string())),
                }],
                root_exprs: vec![typed_ir::Expr::Lit(typed_ir::Lit::Unit)],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds {
                        lower: Some(Box::new(list_with_principal_var)),
                        upper: None,
                    },
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };
        let lowerer = Lowerer {
            env: HashMap::new(),
            binding_infos: HashMap::new(),
            aliases: HashMap::new(),
            graph: &program.graph,
            runtime_symbols: HashMap::new(),
            primitive_paths: RuntimePrimitivePathTable::standard(),
            principal_vars: principal_module_type_vars(&program.program),
            expected_edges_by_id: HashMap::new(),
            use_expected_arg_evidence: false,
            use_principal_elaboration: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            runtime_adapter_profile: RuntimeAdapterProfile::default(),
            local_param_boundaries: HashMap::new(),
            handler_body_depth: 0,
            current_function_boundary: None,
            current_binding: None,
            current_runtime_adapter_source: None,
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };

        assert_eq!(lowerer.root_graph_type(0), Some(list_of_int));
    }

    #[test]
    pub(super) fn prepare_thunk_expected_type_keeps_more_concrete_actual_value() {
        let value_var = typed_ir::TypeVar("value".to_string());
        let expected = RuntimeType::thunk(
            named_type("undet"),
            RuntimeType::core(typed_ir::Type::Var(value_var)),
        );
        let expr = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
            RuntimeType::core(named_type("int")),
        );

        let mut profile = RuntimeAdapterProfile::default();
        let prepared =
            prepare_expr_for_expected_profiled(expr, &expected, TypeSource::Expected, &mut profile)
                .expect("prepared");

        let RuntimeType::Thunk { value, .. } = &prepared.ty else {
            panic!("expected a thunk");
        };
        assert_eq!(core_type(value), &named_type("int"));
    }

    #[test]
    pub(super) fn runtime_adapter_profile_counts_value_to_thunk_wrap() {
        let expected = RuntimeType::thunk(empty_row(), RuntimeType::core(named_type("int")));
        let expr = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
            RuntimeType::core(named_type("int")),
        );
        let mut profile = RuntimeAdapterProfile::default();

        let prepared =
            prepare_expr_for_expected_profiled(expr, &expected, TypeSource::Expected, &mut profile)
                .expect("prepared");

        assert!(matches!(prepared.kind, ExprKind::Thunk { .. }));
        assert_eq!(profile.value_to_thunk, 1);
        assert_eq!(profile.thunk_to_value, 0);
        assert_eq!(profile.bind_here, 0);
    }

    #[test]
    pub(super) fn runtime_adapter_profile_counts_thunk_to_value_bind_here() {
        let expected = RuntimeType::core(named_type("int"));
        let thunk_ty = RuntimeType::thunk(empty_row(), RuntimeType::core(named_type("int")));
        let expr = Expr::typed(
            ExprKind::Thunk {
                effect: empty_row(),
                value: RuntimeType::core(named_type("int")),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
                    RuntimeType::core(named_type("int")),
                )),
            },
            thunk_ty,
        );
        let mut profile = RuntimeAdapterProfile::default();

        let prepared =
            prepare_expr_for_expected_profiled(expr, &expected, TypeSource::Expected, &mut profile)
                .expect("prepared");

        assert!(matches!(prepared.kind, ExprKind::BindHere { .. }));
        assert_eq!(profile.thunk_to_value, 1);
        assert_eq!(profile.bind_here, 1);
        assert_eq!(profile.value_to_thunk, 0);
    }

    #[test]
    pub(super) fn runtime_adapter_profile_counts_apply_phase_and_source_edge() {
        let expected = RuntimeType::core(named_type("int"));
        let thunk_ty = RuntimeType::thunk(empty_row(), RuntimeType::core(named_type("int")));
        let expr = Expr::typed(
            ExprKind::Thunk {
                effect: empty_row(),
                value: RuntimeType::core(named_type("int")),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
                    RuntimeType::core(named_type("int")),
                )),
            },
            thunk_ty,
        );
        let mut profile = RuntimeAdapterProfile {
            collect_events: true,
            ..RuntimeAdapterProfile::default()
        };

        let prepared = prepare_expr_for_expected_with_adapter_source_profiled(
            expr,
            &expected,
            TypeSource::ApplyArgumentSourceEdge,
            &mut profile,
            Some(RuntimeAdapterSource {
                phase: RuntimeApplyAdapterPhase::PrepareFinalArgument,
                has_apply_evidence: true,
                has_apply_callee_source_edge: false,
                has_apply_arg_source_edge: true,
                callee_source_edge: None,
                arg_source_edge: Some(7),
                owner: Some(typed_ir::Path::from_name(typed_ir::Name(
                    "owner".to_string(),
                ))),
                apply_target: Some(typed_ir::Path::from_name(typed_ir::Name("f".to_string()))),
            }),
        )
        .expect("prepared");

        assert!(matches!(prepared.kind, ExprKind::BindHere { .. }));
        assert_eq!(profile.apply_evidence_thunk_to_value, 1);
        assert_eq!(profile.apply_evidence_bind_here, 1);
        assert_eq!(profile.apply_prepare_final_argument_thunk_to_value, 1);
        assert_eq!(profile.apply_prepare_final_argument_bind_here, 1);
        assert_eq!(profile.apply_evidence_adapter_with_evidence, 2);
        assert_eq!(profile.apply_evidence_adapter_with_source_edge, 2);
        assert_eq!(profile.apply_evidence_thunk_to_value_with_source_edge, 1);
        assert_eq!(profile.apply_evidence_bind_here_with_source_edge, 1);
        assert_eq!(profile.events.len(), 2);
        assert_eq!(
            profile.events[0].apply_target.as_ref(),
            Some(&typed_ir::Path::from_name(typed_ir::Name("f".to_string())))
        );
        assert_eq!(profile.events[0].arg_source_edge, Some(7));
    }

    #[test]
    pub(super) fn lower_role_method_var_resolves_concrete_impl_from_expected_receiver() {
        let role_path = typed_ir::Path::new(vec![
            typed_ir::Name("std".to_string()),
            typed_ir::Name("prelude".to_string()),
            typed_ir::Name("Add".to_string()),
            typed_ir::Name("add".to_string()),
        ]);
        let int_impl = typed_ir::Path::new(vec![
            typed_ir::Name("std".to_string()),
            typed_ir::Name("prelude".to_string()),
            typed_ir::Name("&impl#int".to_string()),
            typed_ir::Name("add".to_string()),
        ]);
        let float_impl = typed_ir::Path::new(vec![
            typed_ir::Name("std".to_string()),
            typed_ir::Name("prelude".to_string()),
            typed_ir::Name("&impl#float".to_string()),
            typed_ir::Name("add".to_string()),
        ]);
        let int_ty = RuntimeType::fun(
            RuntimeType::core(named_type("int")),
            RuntimeType::fun(
                RuntimeType::core(named_type("int")),
                RuntimeType::core(named_type("int")),
            ),
        );
        let float_ty = RuntimeType::fun(
            RuntimeType::core(named_type("float")),
            RuntimeType::fun(
                RuntimeType::core(named_type("float")),
                RuntimeType::core(named_type("float")),
            ),
        );
        let mut lowerer = Lowerer {
            env: HashMap::new(),
            binding_infos: HashMap::from([
                (
                    int_impl.clone(),
                    BindingInfo {
                        ty: int_ty.clone(),
                        type_params: Vec::new(),
                        requirements: Vec::new(),
                    },
                ),
                (
                    float_impl,
                    BindingInfo {
                        ty: float_ty,
                        type_params: Vec::new(),
                        requirements: Vec::new(),
                    },
                ),
            ]),
            aliases: HashMap::new(),
            graph: &typed_ir::CoreGraphView::default(),
            runtime_symbols: HashMap::from([(
                role_path.clone(),
                typed_ir::RuntimeSymbolKind::RoleMethod,
            )]),
            primitive_paths: RuntimePrimitivePathTable::standard(),
            principal_vars: BTreeSet::new(),
            expected_edges_by_id: HashMap::new(),
            use_expected_arg_evidence: false,
            use_principal_elaboration: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            runtime_adapter_profile: RuntimeAdapterProfile::default(),
            local_param_boundaries: HashMap::new(),
            handler_body_depth: 0,
            current_function_boundary: None,
            current_binding: None,
            current_runtime_adapter_source: None,
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };

        let expected_ty = RuntimeType::fun(
            RuntimeType::core(named_type("int")),
            RuntimeType::fun(
                RuntimeType::core(named_type("int")),
                RuntimeType::thunk(
                    typed_ir::Type::Var(typed_ir::TypeVar("effect".to_string())),
                    RuntimeType::core(typed_ir::Type::Var(typed_ir::TypeVar("value".to_string()))),
                ),
            ),
        );

        let expr = lowerer
            .lower_expr(
                typed_ir::Expr::Var(role_path.clone()),
                Some(&expected_ty),
                &mut HashMap::new(),
                TypeSource::Expected,
            )
            .expect("lowered");

        assert!(matches!(expr.kind, ExprKind::Var(path) if path == role_path));
        assert_eq!(expr.ty, expected_ty);
    }

    #[test]
    pub(super) fn lower_let_accepts_function_value_pattern() {
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::Block {
                    stmts: vec![typed_ir::Stmt::Let {
                        pattern: typed_ir::Pattern::Bind(typed_ir::Name("f".to_string())),
                        value: typed_ir::Expr::Lambda {
                            param: typed_ir::Name("x".to_string()),
                            param_effect_annotation: None,
                            param_function_allowed_effects: None,
                            body: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Int(
                                "1".to_string(),
                            ))),
                        },
                    }],
                    tail: Some(Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Unit))),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(unit_type()),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::Block { stmts, .. } = &module.root_exprs[0].kind else {
            panic!("root should be a block");
        };
        let Stmt::Let { pattern, value } = &stmts[0] else {
            panic!("block should bind the function");
        };
        assert!(matches!(
            pattern,
            Pattern::Bind {
                ty: RuntimeType::Fun { .. },
                ..
            }
        ));
        assert!(matches!(value.ty, RuntimeType::Fun { .. }));
    }

    #[test]
    pub(super) fn lower_root_without_graph_type_is_rejected() {
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView::default(),
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        assert!(matches!(
            lower_core_program(program),
            Err(RuntimeError::MissingRootType { index: 0 })
        ));
    }

    #[test]
    pub(super) fn lower_binding_prefers_principal_scheme_over_wide_graph_bounds() {
        let point = named_type("point");
        let record = typed_ir::Type::Record(typed_ir::RecordType {
            fields: vec![typed_ir::RecordField {
                name: typed_ir::Name("x".to_string()),
                value: named_type("int"),
                optional: false,
            }],
            spread: None,
        });
        let point_ctor_ty = typed_ir::Type::Fun {
            param: Box::new(record.clone()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(point.clone()),
        };
        let point_path = typed_ir::Path::from_name(typed_ir::Name("point".to_string()));
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![typed_ir::PrincipalBinding {
                    name: point_path.clone(),
                    scheme: typed_ir::Scheme {
                        requirements: Vec::new(),
                        body: point_ctor_ty.clone(),
                    },
                    body: typed_ir::Expr::Lambda {
                        param: typed_ir::Name("value".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(typed_ir::Expr::Coerce {
                            expr: Box::new(typed_ir::Expr::Var(typed_ir::Path::from_name(
                                typed_ir::Name("value".to_string()),
                            ))),
                            evidence: None,
                        }),
                    },
                }],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: typed_ir::CoreGraphView {
                bindings: vec![typed_ir::BindingGraphNode {
                    binding: point_path,
                    scheme_body: point_ctor_ty.clone(),
                    body_bounds: typed_ir::TypeBounds::upper(typed_ir::Type::Any),
                }],
                root_exprs: Vec::new(),
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");

        assert_eq!(
            module.bindings[0].body.ty,
            RuntimeType::fun(RuntimeType::core(record), RuntimeType::core(point))
        );
    }

    #[test]
    pub(super) fn lower_direct_alias_prefers_more_concrete_target_type() {
        let effect_var = typed_ir::TypeVar("e".to_string());
        let target_path = typed_ir::Path::new(vec![
            typed_ir::Name("std".to_string()),
            typed_ir::Name("range".to_string()),
            typed_ir::Name("from_included".to_string()),
        ]);
        let alias_path = typed_ir::Path::new(vec![
            typed_ir::Name("std".to_string()),
            typed_ir::Name("prelude".to_string()),
            typed_ir::Name("#op:suffix:..".to_string()),
        ]);
        let pure_ty = typed_ir::Type::Fun {
            param: Box::new(named_type("int")),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(named_type("range")),
        };
        let polluted_alias_ty = typed_ir::Type::Fun {
            param: Box::new(named_type("int")),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Named {
                path: typed_ir::Path::new(vec![
                    typed_ir::Name("std".to_string()),
                    typed_ir::Name("flow".to_string()),
                    typed_ir::Name("sub".to_string()),
                ]),
                args: vec![typed_ir::TypeArg::Type(typed_ir::Type::Var(effect_var))],
            }),
            ret: Box::new(named_type("range")),
        };
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![
                    typed_ir::PrincipalBinding {
                        name: alias_path.clone(),
                        scheme: typed_ir::Scheme {
                            requirements: Vec::new(),
                            body: polluted_alias_ty,
                        },
                        body: typed_ir::Expr::Var(target_path.clone()),
                    },
                    typed_ir::PrincipalBinding {
                        name: target_path,
                        scheme: typed_ir::Scheme {
                            requirements: Vec::new(),
                            body: pure_ty.clone(),
                        },
                        body: typed_ir::Expr::PrimitiveOp(typed_ir::PrimitiveOp::IntToString),
                    },
                ],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: typed_ir::CoreGraphView::default(),
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let alias = module
            .bindings
            .iter()
            .find(|binding| binding.name == alias_path)
            .expect("alias binding");

        assert_eq!(
            alias.body.ty,
            RuntimeType::fun(
                RuntimeType::core(named_type("int")),
                RuntimeType::core(named_type("range"))
            )
        );
        assert!(alias.type_params.is_empty());
    }

    #[test]
    pub(super) fn lower_apply_records_polymorphic_instantiation() {
        let a = typed_ir::TypeVar("a".to_string());
        let id_path = typed_ir::Path::from_name(typed_ir::Name("id".to_string()));
        let id_ty = typed_ir::Type::Fun {
            param: Box::new(typed_ir::Type::Var(a.clone())),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(typed_ir::Type::Var(a.clone())),
        };
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![typed_ir::PrincipalBinding {
                    name: id_path.clone(),
                    scheme: typed_ir::Scheme {
                        requirements: Vec::new(),
                        body: id_ty,
                    },
                    body: typed_ir::Expr::Lambda {
                        param: typed_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(typed_ir::Expr::Var(typed_ir::Path::from_name(
                            typed_ir::Name("x".to_string()),
                        ))),
                    },
                }],
                root_exprs: vec![typed_ir::Expr::Apply {
                    callee: Box::new(typed_ir::Expr::Var(id_path.clone())),
                    arg: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))),
                    evidence: None,
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(named_type("int")),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::Apply {
            instantiation: Some(instantiation),
            ..
        } = &module.root_exprs[0].kind
        else {
            panic!("missing instantiation");
        };

        assert_eq!(instantiation.target, id_path);
        assert_eq!(instantiation.args.len(), 1);
        assert_eq!(instantiation.args[0].var, a);
        assert_eq!(instantiation.args[0].ty, named_type("int"));
        assert_eq!(core_type(&module.root_exprs[0].ty), &named_type("int"));
    }

    #[test]
    pub(super) fn lower_handle_resume_uses_apply_evidence() {
        let k_path = typed_ir::Path::from_name(typed_ir::Name("k".to_string()));
        let action_path = typed_ir::Path {
            segments: vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("junction".to_string()),
                typed_ir::Name("or".to_string()),
                typed_ir::Name("choose".to_string()),
            ],
        };
        let effect_path = typed_ir::Path {
            segments: vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("junction".to_string()),
                typed_ir::Name("or".to_string()),
            ],
        };
        let handled_effect = typed_ir::Type::Row {
            items: vec![typed_ir::Type::Named {
                path: effect_path.clone(),
                args: Vec::new(),
            }],
            tail: Box::new(typed_ir::Type::Never),
        };
        let effect_op_ty = typed_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(handled_effect.clone()),
            ret: Box::new(bool_type()),
        };
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::Handle {
                    body: Box::new(typed_ir::Expr::Apply {
                        callee: Box::new(typed_ir::Expr::Var(action_path.clone())),
                        arg: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Unit)),
                        evidence: Some(typed_ir::ApplyEvidence {
                            callee_source_edge: None,
                            expected_callee: None,
                            arg_source_edge: None,
                            callee: typed_ir::TypeBounds::exact(effect_op_ty),
                            arg: typed_ir::TypeBounds::exact(unit_type()),
                            expected_arg: None,
                            result: typed_ir::TypeBounds::exact(bool_type()),
                            principal_callee: None,
                            substitutions: Vec::new(),
                            substitution_candidates: Vec::new(),
                            role_method: false,
                            principal_elaboration: None,
                        }),
                    }),
                    arms: vec![typed_ir::HandleArm {
                        effect: action_path.clone(),
                        payload: typed_ir::Pattern::Wildcard,
                        resume: Some(typed_ir::Name("k".to_string())),
                        guard: None,
                        body: typed_ir::Expr::Apply {
                            callee: Box::new(typed_ir::Expr::Var(k_path)),
                            arg: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Bool(true))),
                            evidence: Some(typed_ir::ApplyEvidence {
                                callee_source_edge: None,
                                expected_callee: None,
                                arg_source_edge: None,
                                callee: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
                                arg: typed_ir::TypeBounds::exact(bool_type()),
                                expected_arg: None,
                                result: typed_ir::TypeBounds::exact(bool_type()),
                                principal_callee: None,
                                substitutions: Vec::new(),
                                substitution_candidates: Vec::new(),
                                role_method: false,
                                principal_elaboration: None,
                            }),
                        },
                    }],
                    evidence: Some(typed_ir::JoinEvidence {
                        result: typed_ir::TypeBounds::exact(bool_type()),
                    }),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(bool_type()),
                }],
                runtime_symbols: vec![typed_ir::RuntimeSymbol {
                    path: action_path,
                    kind: typed_ir::RuntimeSymbolKind::EffectOperation,
                }],
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");

        assert_eq!(core_type(&module.root_exprs[0].ty), &bool_type());
        let ExprKind::Handle { arms, handler, .. } = &module.root_exprs[0].kind else {
            panic!("missing handle");
        };
        assert_eq!(handler.consumes, vec![effect_path]);
        let resume = arms[0].resume.as_ref().expect("resume binding");
        assert_eq!(resume.name, typed_ir::Name("k".to_string()));
        let RuntimeType::Fun { param, ret } = &resume.ty else {
            panic!("resume should be a function");
        };
        assert_eq!(**param, RuntimeType::core(bool_type()));
        assert_eq!(**ret, RuntimeType::core(bool_type()));
    }

    #[test]
    pub(super) fn lower_handle_payload_uses_arm_body_context() {
        let payload_name = typed_ir::Name("payload".to_string());
        let effect_path = typed_ir::Path::from_name(typed_ir::Name("ret".to_string()));
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::Handle {
                    body: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Bool(true))),
                    arms: vec![typed_ir::HandleArm {
                        effect: effect_path,
                        payload: typed_ir::Pattern::Bind(payload_name.clone()),
                        resume: None,
                        guard: None,
                        body: typed_ir::Expr::Var(typed_ir::Path::from_name(payload_name.clone())),
                    }],
                    evidence: Some(typed_ir::JoinEvidence {
                        result: typed_ir::TypeBounds::exact(bool_type()),
                    }),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(bool_type()),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::Handle { arms, .. } = &module.root_exprs[0].kind else {
            panic!("missing handle");
        };
        let Pattern::Bind { ty, .. } = &arms[0].payload else {
            panic!("missing payload binding");
        };
        assert_eq!(core_type(ty), &bool_type());
    }

    #[test]
    pub(super) fn lower_join_inserts_runtime_coercion_for_int_to_float() {
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::If {
                    cond: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Bool(true))),
                    then_branch: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))),
                    else_branch: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Float(
                        "2.0".to_string(),
                    ))),
                    evidence: Some(typed_ir::JoinEvidence {
                        result: typed_ir::TypeBounds::exact(named_type("float")),
                    }),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(named_type("float")),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::If { then_branch, .. } = &module.root_exprs[0].kind else {
            panic!("missing if");
        };

        assert_eq!(core_type(&module.root_exprs[0].ty), &named_type("float"));
        let ExprKind::Coerce { from, to, expr } = &then_branch.kind else {
            panic!("missing coercion");
        };
        assert_eq!(*from, named_type("int"));
        assert_eq!(*to, named_type("float"));
        assert_eq!(core_type(&expr.ty), &named_type("int"));
        assert_eq!(core_type(&then_branch.ty), &named_type("float"));
    }

    #[test]
    pub(super) fn lower_coerce_uses_core_ir_evidence() {
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::Coerce {
                    expr: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))),
                    evidence: Some(typed_ir::CoerceEvidence {
                        source_edge: None,
                        actual: typed_ir::TypeBounds::exact(named_type("int")),
                        expected: typed_ir::TypeBounds::exact(named_type("float")),
                    }),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(named_type("float")),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");

        let ExprKind::Coerce { from, to, expr } = &module.root_exprs[0].kind else {
            panic!("missing coercion");
        };
        assert_eq!(*from, named_type("int"));
        assert_eq!(*to, named_type("float"));
        assert_eq!(core_type(&expr.ty), &named_type("int"));
        assert_eq!(core_type(&module.root_exprs[0].ty), &named_type("float"));
    }

    #[test]
    pub(super) fn lower_coerce_prefers_semantic_cast_impl() {
        let frac = typed_ir::Type::Named {
            path: typed_ir::Path::new(vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("frac".to_string()),
                typed_ir::Name("frac".to_string()),
            ]),
            args: Vec::new(),
        };
        let float = named_type("float");
        let cast_path = typed_ir::Path::new(vec![
            typed_ir::Name("std".to_string()),
            typed_ir::Name("prelude".to_string()),
            typed_ir::Name("cast".to_string()),
        ]);
        let value_path = typed_ir::Path::from_name(typed_ir::Name("value".to_string()));
        let cast_ty = typed_ir::Type::Fun {
            param: Box::new(frac.clone()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(float.clone()),
        };
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![
                    typed_ir::PrincipalBinding {
                        name: value_path.clone(),
                        scheme: typed_ir::Scheme {
                            requirements: Vec::new(),
                            body: frac.clone(),
                        },
                        body: typed_ir::Expr::Record {
                            fields: vec![
                                typed_ir::RecordExprField {
                                    name: typed_ir::Name("num".to_string()),
                                    value: typed_ir::Expr::Lit(typed_ir::Lit::Int("7".to_string())),
                                },
                                typed_ir::RecordExprField {
                                    name: typed_ir::Name("den".to_string()),
                                    value: typed_ir::Expr::Lit(typed_ir::Lit::Int("3".to_string())),
                                },
                            ],
                            spread: None,
                        },
                    },
                    typed_ir::PrincipalBinding {
                        name: cast_path.clone(),
                        scheme: typed_ir::Scheme {
                            requirements: Vec::new(),
                            body: cast_ty.clone(),
                        },
                        body: typed_ir::Expr::Lambda {
                            param: typed_ir::Name("x".to_string()),
                            param_effect_annotation: None,
                            param_function_allowed_effects: None,
                            body: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Float(
                                "0.0".to_string(),
                            ))),
                        },
                    },
                ],
                root_exprs: vec![typed_ir::Expr::Coerce {
                    expr: Box::new(typed_ir::Expr::Var(value_path.clone())),
                    evidence: Some(typed_ir::CoerceEvidence {
                        source_edge: None,
                        actual: typed_ir::TypeBounds::exact(frac.clone()),
                        expected: typed_ir::TypeBounds::exact(float.clone()),
                    }),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: vec![
                    typed_ir::BindingGraphNode {
                        binding: value_path,
                        scheme_body: frac.clone(),
                        body_bounds: typed_ir::TypeBounds::exact(frac.clone()),
                    },
                    typed_ir::BindingGraphNode {
                        binding: cast_path.clone(),
                        scheme_body: cast_ty,
                        body_bounds: typed_ir::TypeBounds::exact(float.clone()),
                    },
                ],
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(float),
                }],
                role_impls: vec![typed_ir::RoleImplGraphNode {
                    role: typed_ir::Path::new(vec![typed_ir::Name("Cast".to_string())]),
                    inputs: vec![typed_ir::TypeBounds::exact(frac)],
                    associated_types: vec![typed_ir::RecordField {
                        name: typed_ir::Name("to".to_string()),
                        value: typed_ir::TypeBounds::exact(named_type("float")),
                        optional: false,
                    }],
                    members: vec![typed_ir::RecordField {
                        name: typed_ir::Name("cast".to_string()),
                        value: cast_path.clone(),
                        optional: false,
                    }],
                }],
                runtime_symbols: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");

        let ExprKind::Apply { callee, .. } = &module.root_exprs[0].kind else {
            panic!("coerce should lower through Cast impl apply");
        };
        assert!(matches!(&callee.kind, ExprKind::Var(path) if path == &cast_path));
        assert_eq!(core_type(&module.root_exprs[0].ty), &named_type("float"));
    }

    #[test]
    pub(super) fn lower_coerce_accepts_representation_source_edge_table() {
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::Coerce {
                    expr: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))),
                    evidence: Some(typed_ir::CoerceEvidence {
                        source_edge: Some(9),
                        actual: typed_ir::TypeBounds::exact(named_type("int")),
                        expected: typed_ir::TypeBounds::exact(named_type("float")),
                    }),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(named_type("float")),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence {
                expected_edges: vec![typed_ir::ExpectedEdgeEvidence {
                    id: 9,
                    kind: typed_ir::ExpectedEdgeKind::RepresentationCoerce,
                    source_range: None,
                    actual: typed_ir::TypeBounds::exact(named_type("int")),
                    expected: typed_ir::TypeBounds::exact(named_type("float")),
                    actual_effect: None,
                    expected_effect: None,
                    closed: true,
                    informative: true,
                    runtime_usable: true,
                }],
                expected_adapter_edges: Vec::new(),
                derived_expected_edges: Vec::new(),
                handler_matches: Vec::new(),
            },
        };

        let module = lower_core_program(program).expect("lowered");

        let ExprKind::Coerce { from, to, .. } = &module.root_exprs[0].kind else {
            panic!("missing coercion");
        };
        assert_eq!(*from, named_type("int"));
        assert_eq!(*to, named_type("float"));
    }

    #[test]
    pub(super) fn lower_unbound_qualified_path_as_effect_op() {
        let effect_path = typed_ir::Path {
            segments: vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("junction".to_string()),
                typed_ir::Name("or".to_string()),
            ],
        };
        let effect_ty = typed_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(typed_ir::Type::Any),
            ret_effect: Box::new(typed_ir::Type::Any),
            ret: Box::new(bool_type()),
        };
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::Expr::Apply {
                    callee: Box::new(typed_ir::Expr::Var(effect_path.clone())),
                    arg: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Unit)),
                    evidence: Some(typed_ir::ApplyEvidence {
                        callee_source_edge: None,
                        expected_callee: None,
                        arg_source_edge: None,
                        callee: typed_ir::TypeBounds::exact(effect_ty),
                        arg: typed_ir::TypeBounds::exact(unit_type()),
                        expected_arg: None,
                        result: typed_ir::TypeBounds::exact(bool_type()),
                        principal_callee: None,
                        substitutions: Vec::new(),
                        substitution_candidates: Vec::new(),
                        role_method: false,
                        principal_elaboration: None,
                    }),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(bool_type()),
                }],
                runtime_symbols: vec![typed_ir::RuntimeSymbol {
                    path: effect_path.clone(),
                    kind: typed_ir::RuntimeSymbolKind::EffectOperation,
                }],
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::BindHere { expr } = &module.root_exprs[0].kind else {
            panic!("missing bind_here");
        };
        let apply = match &expr.kind {
            ExprKind::Thunk { expr, .. } => expr.as_ref(),
            ExprKind::Apply { .. } => expr.as_ref(),
            _ => panic!("missing effectful apply"),
        };
        let ExprKind::Apply { callee, .. } = &apply.kind else {
            panic!("missing apply");
        };
        assert!(matches!(&callee.kind, ExprKind::EffectOp(path) if path == &effect_path));
    }

    #[test]
    pub(super) fn lower_effectful_apply_in_value_context_inserts_bind_here() {
        let effect = typed_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let fn_ty = typed_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(named_type("int")),
        };
        let action_path = typed_ir::Path::from_name(typed_ir::Name("action".to_string()));
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![typed_ir::PrincipalBinding {
                    name: action_path.clone(),
                    scheme: typed_ir::Scheme {
                        requirements: Vec::new(),
                        body: fn_ty.clone(),
                    },
                    body: typed_ir::Expr::Lambda {
                        param: typed_ir::Name("unit".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))),
                    },
                }],
                root_exprs: vec![typed_ir::Expr::Apply {
                    callee: Box::new(typed_ir::Expr::Var(action_path)),
                    arg: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Unit)),
                    evidence: Some(typed_ir::ApplyEvidence {
                        callee_source_edge: None,
                        expected_callee: None,
                        arg_source_edge: None,
                        callee: typed_ir::TypeBounds::exact(fn_ty),
                        arg: typed_ir::TypeBounds::exact(unit_type()),
                        expected_arg: None,
                        result: typed_ir::TypeBounds::exact(named_type("int")),
                        principal_callee: None,
                        substitutions: Vec::new(),
                        substitution_candidates: Vec::new(),
                        role_method: false,
                        principal_elaboration: None,
                    }),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(named_type("int")),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::BindHere { expr } = &module.root_exprs[0].kind else {
            panic!("missing bind_here");
        };
        let RuntimeType::Thunk {
            effect: actual,
            value,
        } = &expr.ty
        else {
            panic!("inner apply should be thunk");
        };
        assert_eq!(actual, &effect);
        assert_eq!(core_type(value), &named_type("int"));
    }

    #[test]
    pub(super) fn lower_tuple_lifts_item_effect_to_tuple_thunk() {
        let effect = typed_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let fn_ty = typed_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(named_type("int")),
        };
        let action_path = typed_ir::Path::from_name(typed_ir::Name("action".to_string()));
        let tuple_ty = typed_ir::Type::Tuple(vec![named_type("int"), named_type("int")]);
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![effectful_action_binding(action_path.clone(), fn_ty.clone())],
                root_exprs: vec![typed_ir::Expr::Tuple(vec![
                    effectful_action_apply(action_path, fn_ty),
                    typed_ir::Expr::Lit(typed_ir::Lit::Int("2".to_string())),
                ])],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(tuple_ty.clone()),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::BindHere { expr } = &module.root_exprs[0].kind else {
            panic!("tuple effect should be forced at the root");
        };
        let RuntimeType::Thunk {
            effect: actual,
            value,
        } = &expr.ty
        else {
            panic!("tuple should be lifted to thunk before forcing");
        };
        assert_eq!(actual, &effect);
        assert_eq!(core_type(value), &tuple_ty);
    }

    #[test]
    pub(super) fn lower_if_lifts_branch_effect_to_if_thunk() {
        let effect = typed_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let fn_ty = typed_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(named_type("int")),
        };
        let action_path = typed_ir::Path::from_name(typed_ir::Name("action".to_string()));
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![effectful_action_binding(action_path.clone(), fn_ty.clone())],
                root_exprs: vec![typed_ir::Expr::If {
                    cond: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Bool(true))),
                    then_branch: Box::new(effectful_action_apply(action_path, fn_ty)),
                    else_branch: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Int("2".to_string()))),
                    evidence: Some(typed_ir::JoinEvidence {
                        result: typed_ir::TypeBounds::exact(named_type("int")),
                    }),
                }],
                roots: vec![typed_ir::PrincipalRoot::Expr(0)],
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(0),
                    bounds: typed_ir::TypeBounds::exact(named_type("int")),
                }],
                runtime_symbols: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::BindHere { expr } = &module.root_exprs[0].kind else {
            panic!("if effect should be forced at the root");
        };
        let RuntimeType::Thunk {
            effect: actual,
            value,
        } = &expr.ty
        else {
            panic!("if should be lifted to thunk before forcing");
        };
        assert_eq!(actual, &effect);
        assert_eq!(core_type(value), &named_type("int"));
    }

    #[test]
    pub(super) fn lower_lambda_adds_runtime_id_admin_to_created_thunk() {
        let effect = typed_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let fn_ty = typed_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(named_type("int")),
        };
        let binding_path = typed_ir::Path::from_name(typed_ir::Name("f".to_string()));
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![typed_ir::PrincipalBinding {
                    name: binding_path,
                    scheme: typed_ir::Scheme {
                        requirements: Vec::new(),
                        body: fn_ty,
                    },
                    body: typed_ir::Expr::Lambda {
                        param: typed_ir::Name("unit".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))),
                    },
                }],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: typed_ir::CoreGraphView::default(),
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::Lambda { body, .. } = &module.bindings[0].body.kind else {
            panic!("expected lambda");
        };
        let ExprKind::LocalPushId { body, .. } = &body.kind else {
            panic!("expected local push around thunk admin");
        };
        let ExprKind::AddId {
            id, allowed, thunk, ..
        } = &body.kind
        else {
            panic!("expected add_id around created thunk");
        };
        assert_eq!(*id, EffectIdRef::Peek);
        assert_eq!(allowed, &effect);
        assert!(matches!(thunk.kind, ExprKind::Thunk { .. }));
    }

    #[test]
    pub(super) fn add_id_uses_thunk_effect() {
        let undet = typed_ir::Type::Row {
            items: vec![named_type("undet")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let value = RuntimeType::core(named_type("int"));
        let inner = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
            value.clone(),
        );
        let thunk = Expr::typed(
            ExprKind::Thunk {
                effect: undet.clone(),
                value: value.clone(),
                expr: Box::new(inner),
            },
            RuntimeType::thunk(undet.clone(), value),
        );

        let expr = add_id_to_created_thunks(thunk);

        let ExprKind::AddId {
            id, allowed, thunk, ..
        } = &expr.kind
        else {
            panic!("expected add_id around thunk");
        };
        assert_eq!(*id, EffectIdRef::Peek);
        assert_eq!(allowed, &undet);
        let RuntimeType::Thunk { effect, .. } = &thunk.ty else {
            panic!("expected thunk type");
        };
        assert_eq!(effect, &undet);
    }

    #[test]
    pub(super) fn param_allowed_effect_does_not_change_thunk_type() {
        let io_path = typed_ir::Path::from_name(typed_ir::Name("io".to_string()));
        let undet = typed_ir::Type::Row {
            items: vec![named_type("undet")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let value = RuntimeType::core(named_type("int"));
        let param_ty = RuntimeType::thunk(undet.clone(), value.clone());

        let protected = apply_param_allowed_effect(
            param_ty,
            None,
            Some(&typed_ir::FunctionSigAllowedEffects::Effects(vec![io_path])),
        );

        let RuntimeType::Thunk {
            effect,
            value: actual_value,
        } = protected
        else {
            panic!("expected thunk");
        };
        assert_eq!(effect, undet);
        assert_eq!(*actual_value, value);
    }

    #[test]
    pub(super) fn lower_binding_refines_anonymous_effect_from_body() {
        let effect_path = typed_ir::Path {
            segments: vec![
                typed_ir::Name("io".to_string()),
                typed_ir::Name("abort".to_string()),
            ],
        };
        let effect = typed_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let effect_op_ty = typed_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(typed_ir::Type::Never),
        };
        let wrapper_path = typed_ir::Path::from_name(typed_ir::Name("wrapper".to_string()));
        let anonymous_effect_ty = typed_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("_".to_string()))),
            ret: Box::new(typed_ir::Type::Never),
        };
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: vec![typed_ir::PrincipalBinding {
                    name: wrapper_path,
                    scheme: typed_ir::Scheme {
                        requirements: Vec::new(),
                        body: anonymous_effect_ty,
                    },
                    body: typed_ir::Expr::Lambda {
                        param: typed_ir::Name("unit".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(typed_ir::Expr::Apply {
                            callee: Box::new(typed_ir::Expr::Var(effect_path.clone())),
                            arg: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Unit)),
                            evidence: Some(typed_ir::ApplyEvidence {
                                callee_source_edge: None,
                                expected_callee: None,
                                arg_source_edge: None,
                                callee: typed_ir::TypeBounds::exact(effect_op_ty),
                                arg: typed_ir::TypeBounds::exact(unit_type()),
                                expected_arg: None,
                                result: typed_ir::TypeBounds::exact(typed_ir::Type::Never),
                                principal_callee: None,
                                substitutions: Vec::new(),
                                substitution_candidates: Vec::new(),
                                role_method: false,
                                principal_elaboration: None,
                            }),
                        }),
                    },
                }],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: typed_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: Vec::new(),
                runtime_symbols: vec![typed_ir::RuntimeSymbol {
                    path: effect_path,
                    kind: typed_ir::RuntimeSymbolKind::EffectOperation,
                }],
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: typed_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let binding = &module.bindings[0];

        assert!(binding.type_params.is_empty());
        let RuntimeType::Fun { ret, .. } = &binding.body.ty else {
            panic!("wrapper should be a function");
        };
        let RuntimeType::Thunk {
            effect: actual,
            value,
        } = ret.as_ref()
        else {
            panic!("anonymous effect should be refined to a thunk");
        };
        assert_eq!(actual, &effect);
        assert_eq!(core_type(value), &typed_ir::Type::Never);
    }

    #[test]
    pub(super) fn lower_apply_uses_evidence_for_any_local_callee() {
        let mut lowerer = Lowerer {
            env: HashMap::new(),
            binding_infos: HashMap::new(),
            aliases: HashMap::new(),
            graph: &typed_ir::CoreGraphView::default(),
            runtime_symbols: HashMap::new(),
            primitive_paths: RuntimePrimitivePathTable::standard(),
            principal_vars: BTreeSet::new(),
            expected_edges_by_id: HashMap::new(),
            use_expected_arg_evidence: false,
            use_principal_elaboration: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            runtime_adapter_profile: RuntimeAdapterProfile::default(),
            local_param_boundaries: HashMap::new(),
            handler_body_depth: 0,
            current_function_boundary: None,
            current_binding: None,
            current_runtime_adapter_source: None,
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };
        let local = typed_ir::Path::from_name(typed_ir::Name("k".to_string()));
        let mut locals = HashMap::from([(local.clone(), RuntimeType::core(typed_ir::Type::Any))]);
        let expr = typed_ir::Expr::Apply {
            callee: Box::new(typed_ir::Expr::Var(local)),
            arg: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Unit)),
            evidence: Some(typed_ir::ApplyEvidence {
                callee_source_edge: None,
                expected_callee: None,
                arg_source_edge: None,
                callee: typed_ir::TypeBounds {
                    lower: None,
                    upper: Some(Box::new(typed_ir::Type::Any)),
                },
                arg: typed_ir::TypeBounds::exact(unit_type()),
                expected_arg: None,
                result: typed_ir::TypeBounds::exact(named_type("int")),
                principal_callee: None,
                substitutions: Vec::new(),
                substitution_candidates: Vec::new(),
                role_method: false,
                principal_elaboration: None,
            }),
        };

        let expr = lowerer
            .lower_expr(
                expr,
                Some(&RuntimeType::core(named_type("int"))),
                &mut locals,
                TypeSource::RootGraph,
            )
            .expect("lowered");

        let ExprKind::Apply { callee, .. } = &expr.kind else {
            panic!("missing apply");
        };
        assert!(matches!(callee.ty, RuntimeType::Fun { .. }));
        assert_eq!(core_type(&expr.ty), &named_type("int"));
    }

    #[test]
    pub(super) fn lower_apply_can_use_expected_arg_evidence_opt_in() {
        let mut lowerer = Lowerer {
            env: HashMap::new(),
            binding_infos: HashMap::new(),
            aliases: HashMap::new(),
            graph: &typed_ir::CoreGraphView::default(),
            runtime_symbols: HashMap::new(),
            primitive_paths: RuntimePrimitivePathTable::standard(),
            principal_vars: BTreeSet::new(),
            expected_edges_by_id: HashMap::new(),
            use_expected_arg_evidence: true,
            use_principal_elaboration: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            runtime_adapter_profile: RuntimeAdapterProfile::default(),
            local_param_boundaries: HashMap::new(),
            handler_body_depth: 0,
            current_function_boundary: None,
            current_binding: None,
            current_runtime_adapter_source: None,
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };
        let callee_path = typed_ir::Path::from_name(typed_ir::Name("k".to_string()));
        let arg_path = typed_ir::Path::from_name(typed_ir::Name("x".to_string()));
        let mut locals = HashMap::from([
            (callee_path.clone(), RuntimeType::core(typed_ir::Type::Any)),
            (arg_path.clone(), RuntimeType::core(typed_ir::Type::Any)),
        ]);
        let expr = typed_ir::Expr::Apply {
            callee: Box::new(typed_ir::Expr::Var(callee_path.clone())),
            arg: Box::new(typed_ir::Expr::Var(arg_path.clone())),
            evidence: Some(typed_ir::ApplyEvidence {
                callee_source_edge: None,
                expected_callee: None,
                arg_source_edge: Some(3),
                callee: typed_ir::TypeBounds {
                    lower: None,
                    upper: Some(Box::new(typed_ir::Type::Any)),
                },
                arg: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
                expected_arg: Some(typed_ir::TypeBounds::exact(named_type("int"))),
                result: typed_ir::TypeBounds::exact(named_type("int")),
                principal_callee: None,
                substitutions: Vec::new(),
                substitution_candidates: Vec::new(),
                role_method: false,
                principal_elaboration: None,
            }),
        };

        let expr = lowerer
            .lower_expr(
                expr,
                Some(&RuntimeType::core(named_type("int"))),
                &mut locals,
                TypeSource::RootGraph,
            )
            .expect("lowered");

        let ExprKind::Apply { arg, .. } = &expr.kind else {
            panic!("missing apply");
        };
        assert_eq!(core_type(&arg.ty), &named_type("int"));
        assert_eq!(
            locals.get(&arg_path),
            Some(&RuntimeType::core(named_type("int")))
        );
        assert_eq!(lowerer.expected_arg_evidence_profile.present, 1);
        assert_eq!(lowerer.expected_arg_evidence_profile.converted, 1);
        assert_eq!(lowerer.expected_arg_evidence_profile.usable_by_bounds, 1);
        assert_eq!(
            lowerer.expected_arg_evidence_profile.used_as_arg_type_hint,
            1
        );
    }

    #[test]
    pub(super) fn lower_apply_can_use_closed_expected_slot_when_edge_actual_is_open() {
        let principal_evidence = typed_ir::PrincipalEvidence {
            expected_edges: vec![typed_ir::ExpectedEdgeEvidence {
                id: 3,
                kind: typed_ir::ExpectedEdgeKind::ApplicationArgument,
                source_range: None,
                actual: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
                expected: typed_ir::TypeBounds::exact(named_type("int")),
                actual_effect: None,
                expected_effect: None,
                closed: true,
                informative: true,
                runtime_usable: false,
            }],
            expected_adapter_edges: Vec::new(),
            derived_expected_edges: Vec::new(),
            handler_matches: Vec::new(),
        };
        let mut lowerer = Lowerer {
            env: HashMap::new(),
            binding_infos: HashMap::new(),
            aliases: HashMap::new(),
            graph: &typed_ir::CoreGraphView::default(),
            runtime_symbols: HashMap::new(),
            primitive_paths: RuntimePrimitivePathTable::standard(),
            principal_vars: BTreeSet::new(),
            expected_edges_by_id: principal_evidence
                .expected_edges
                .iter()
                .map(|edge| (edge.id, edge))
                .collect(),
            use_expected_arg_evidence: true,
            use_principal_elaboration: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            runtime_adapter_profile: RuntimeAdapterProfile::default(),
            local_param_boundaries: HashMap::new(),
            handler_body_depth: 0,
            current_function_boundary: None,
            current_binding: None,
            current_runtime_adapter_source: None,
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };
        let callee_path = typed_ir::Path::from_name(typed_ir::Name("k".to_string()));
        let arg_path = typed_ir::Path::from_name(typed_ir::Name("x".to_string()));
        let mut locals = HashMap::from([
            (callee_path.clone(), RuntimeType::core(typed_ir::Type::Any)),
            (arg_path.clone(), RuntimeType::core(typed_ir::Type::Any)),
        ]);
        let expr = typed_ir::Expr::Apply {
            callee: Box::new(typed_ir::Expr::Var(callee_path)),
            arg: Box::new(typed_ir::Expr::Var(arg_path.clone())),
            evidence: Some(typed_ir::ApplyEvidence {
                callee_source_edge: None,
                expected_callee: None,
                arg_source_edge: Some(3),
                callee: typed_ir::TypeBounds {
                    lower: None,
                    upper: Some(Box::new(typed_ir::Type::Any)),
                },
                arg: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
                expected_arg: Some(typed_ir::TypeBounds::exact(named_type("int"))),
                result: typed_ir::TypeBounds::exact(named_type("int")),
                principal_callee: None,
                substitutions: Vec::new(),
                substitution_candidates: Vec::new(),
                role_method: false,
                principal_elaboration: None,
            }),
        };

        let expr = lowerer
            .lower_expr(
                expr,
                Some(&RuntimeType::core(named_type("int"))),
                &mut locals,
                TypeSource::RootGraph,
            )
            .expect("lowered");

        let ExprKind::Apply { arg, .. } = &expr.kind else {
            panic!("missing apply");
        };
        assert_eq!(core_type(&arg.ty), &named_type("int"));
        assert_eq!(
            locals.get(&arg_path),
            Some(&RuntimeType::core(named_type("int")))
        );
        assert_eq!(lowerer.expected_arg_evidence_profile.present, 1);
        assert_eq!(lowerer.expected_arg_evidence_profile.converted, 1);
        assert_eq!(lowerer.expected_arg_evidence_profile.usable_by_table, 1);
        assert_eq!(
            lowerer.expected_arg_evidence_profile.used_as_arg_type_hint,
            1
        );
        assert_eq!(
            lowerer
                .expected_arg_evidence_profile
                .used_as_lowering_expected,
            1
        );
    }

    #[test]
    pub(super) fn lower_apply_ignores_expected_arg_when_expected_slot_is_erased() {
        let principal_evidence = typed_ir::PrincipalEvidence {
            expected_edges: vec![typed_ir::ExpectedEdgeEvidence {
                id: 3,
                kind: typed_ir::ExpectedEdgeKind::ApplicationArgument,
                source_range: None,
                actual: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
                expected: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
                actual_effect: None,
                expected_effect: None,
                closed: true,
                informative: false,
                runtime_usable: false,
            }],
            expected_adapter_edges: Vec::new(),
            derived_expected_edges: Vec::new(),
            handler_matches: Vec::new(),
        };
        let mut lowerer = Lowerer {
            env: HashMap::new(),
            binding_infos: HashMap::new(),
            aliases: HashMap::new(),
            graph: &typed_ir::CoreGraphView::default(),
            runtime_symbols: HashMap::new(),
            primitive_paths: RuntimePrimitivePathTable::standard(),
            principal_vars: BTreeSet::new(),
            expected_edges_by_id: principal_evidence
                .expected_edges
                .iter()
                .map(|edge| (edge.id, edge))
                .collect(),
            use_expected_arg_evidence: true,
            use_principal_elaboration: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            runtime_adapter_profile: RuntimeAdapterProfile::default(),
            local_param_boundaries: HashMap::new(),
            handler_body_depth: 0,
            current_function_boundary: None,
            current_binding: None,
            current_runtime_adapter_source: None,
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };
        let callee_path = typed_ir::Path::from_name(typed_ir::Name("k".to_string()));
        let arg_path = typed_ir::Path::from_name(typed_ir::Name("x".to_string()));
        let mut locals = HashMap::from([
            (callee_path.clone(), RuntimeType::core(typed_ir::Type::Any)),
            (arg_path.clone(), RuntimeType::core(typed_ir::Type::Any)),
        ]);
        let expr = typed_ir::Expr::Apply {
            callee: Box::new(typed_ir::Expr::Var(callee_path)),
            arg: Box::new(typed_ir::Expr::Var(arg_path.clone())),
            evidence: Some(typed_ir::ApplyEvidence {
                callee_source_edge: None,
                expected_callee: None,
                arg_source_edge: Some(3),
                callee: typed_ir::TypeBounds {
                    lower: None,
                    upper: Some(Box::new(typed_ir::Type::Any)),
                },
                arg: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
                expected_arg: Some(typed_ir::TypeBounds::exact(typed_ir::Type::Any)),
                result: typed_ir::TypeBounds::exact(named_type("int")),
                principal_callee: None,
                substitutions: Vec::new(),
                substitution_candidates: Vec::new(),
                role_method: false,
                principal_elaboration: None,
            }),
        };

        let expr = lowerer
            .lower_expr(
                expr,
                Some(&RuntimeType::core(named_type("int"))),
                &mut locals,
                TypeSource::RootGraph,
            )
            .expect("lowered");

        let ExprKind::Apply { arg, .. } = &expr.kind else {
            panic!("missing apply");
        };
        assert!(matches!(arg.ty, RuntimeType::Core(typed_ir::Type::Any)));
        assert_eq!(
            locals.get(&arg_path),
            Some(&RuntimeType::Core(typed_ir::Type::Any))
        );
        assert_eq!(lowerer.expected_arg_evidence_profile.present, 1);
        assert_eq!(lowerer.expected_arg_evidence_profile.converted, 1);
        assert_eq!(
            lowerer
                .expected_arg_evidence_profile
                .ignored_table_uninformative,
            1
        );
        assert_eq!(lowerer.expected_arg_evidence_profile.ignored_unusable, 1);
        assert_eq!(
            lowerer.expected_arg_evidence_profile.used_as_arg_type_hint,
            0
        );
    }

    #[test]
    pub(super) fn lower_apply_uses_fold_requirement_to_refine_associated_result() {
        let container = typed_ir::TypeVar("container".to_string());
        let item = typed_ir::TypeVar("item".to_string());
        let each_path = typed_ir::Path::from_name(typed_ir::Name("each".to_string()));
        let list_int = list_type(named_type("int"));
        let each_ty = RuntimeType::fun(
            RuntimeType::core(typed_ir::Type::Var(container.clone())),
            RuntimeType::thunk(
                named_type("undet"),
                RuntimeType::core(typed_ir::Type::Var(item.clone())),
            ),
        );
        let fold_role = typed_ir::Path::new(vec![
            typed_ir::Name("std".to_string()),
            typed_ir::Name("fold".to_string()),
            typed_ir::Name("Fold".to_string()),
        ]);
        let graph = typed_ir::CoreGraphView {
            role_impls: vec![typed_ir::RoleImplGraphNode {
                role: fold_role.clone(),
                inputs: vec![typed_ir::TypeBounds::exact(list_int.clone())],
                associated_types: vec![typed_ir::RecordField {
                    name: typed_ir::Name("item".to_string()),
                    value: typed_ir::TypeBounds::exact(named_type("int")),
                    optional: false,
                }],
                members: Vec::new(),
            }],
            ..typed_ir::CoreGraphView::default()
        };
        let mut lowerer = Lowerer {
            env: HashMap::from([(each_path.clone(), each_ty.clone())]),
            binding_infos: HashMap::from([(
                each_path.clone(),
                BindingInfo {
                    ty: each_ty,
                    type_params: vec![container.clone(), item.clone()],
                    requirements: vec![typed_ir::RoleRequirement {
                        role: fold_role,
                        args: vec![
                            typed_ir::RoleRequirementArg::Input(typed_ir::TypeBounds::exact(
                                typed_ir::Type::Var(container),
                            )),
                            typed_ir::RoleRequirementArg::Associated {
                                name: typed_ir::Name("item".to_string()),
                                bounds: typed_ir::TypeBounds::exact(typed_ir::Type::Var(item)),
                            },
                        ],
                    }],
                },
            )]),
            aliases: HashMap::new(),
            graph: &graph,
            runtime_symbols: HashMap::new(),
            primitive_paths: RuntimePrimitivePathTable::standard(),
            principal_vars: BTreeSet::new(),
            expected_edges_by_id: HashMap::new(),
            use_expected_arg_evidence: false,
            use_principal_elaboration: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            runtime_adapter_profile: RuntimeAdapterProfile::default(),
            local_param_boundaries: HashMap::new(),
            handler_body_depth: 0,
            current_function_boundary: None,
            current_binding: None,
            current_runtime_adapter_source: None,
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };
        let xs = typed_ir::Path::from_name(typed_ir::Name("xs".to_string()));
        let mut locals = HashMap::from([(xs.clone(), RuntimeType::core(list_int))]);
        let expr = typed_ir::Expr::Apply {
            callee: Box::new(typed_ir::Expr::Var(each_path)),
            arg: Box::new(typed_ir::Expr::Var(xs)),
            evidence: None,
        };

        let expr = lowerer
            .lower_expr(expr, None, &mut locals, TypeSource::Expected)
            .expect("lowered");

        let RuntimeType::Thunk { value, .. } = &expr.ty else {
            panic!("each should return a thunk");
        };
        assert_eq!(core_type(value), &named_type("int"));
    }

    pub(super) fn effectful_action_binding(
        name: typed_ir::Path,
        fn_ty: typed_ir::Type,
    ) -> typed_ir::PrincipalBinding {
        typed_ir::PrincipalBinding {
            name,
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: fn_ty,
            },
            body: typed_ir::Expr::Lambda {
                param: typed_ir::Name("unit".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))),
            },
        }
    }

    pub(super) fn effectful_action_apply(
        path: typed_ir::Path,
        fn_ty: typed_ir::Type,
    ) -> typed_ir::Expr {
        typed_ir::Expr::Apply {
            callee: Box::new(typed_ir::Expr::Var(path)),
            arg: Box::new(typed_ir::Expr::Lit(typed_ir::Lit::Unit)),
            evidence: Some(typed_ir::ApplyEvidence {
                callee_source_edge: None,
                expected_callee: None,
                arg_source_edge: None,
                callee: typed_ir::TypeBounds::exact(fn_ty),
                arg: typed_ir::TypeBounds::exact(unit_type()),
                expected_arg: None,
                result: typed_ir::TypeBounds::exact(named_type("int")),
                principal_callee: None,
                substitutions: Vec::new(),
                substitution_candidates: Vec::new(),
                role_method: false,
                principal_elaboration: None,
            }),
        }
    }

    pub(super) fn list_type(item: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::new(vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("list".to_string()),
                typed_ir::Name("list".to_string()),
            ]),
            args: vec![typed_ir::TypeArg::Type(item)],
        }
    }
}
