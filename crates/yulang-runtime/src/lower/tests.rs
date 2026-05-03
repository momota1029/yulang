#[cfg(test)]
mod tests {
    use super::super::*;

    #[test]
    pub(super) fn lower_literal_root_uses_graph_type() {
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(named_type("int")),
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");

        assert_eq!(core_type(&module.root_exprs[0].ty), &named_type("int"));
    }

    #[test]
    pub(super) fn lower_root_erases_principal_vars_from_graph_bounds() {
        let principal_var = core_ir::TypeVar("a".to_string());
        let id_path = core_ir::Path::from_name(core_ir::Name("id".to_string()));
        let list_with_principal_var = core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name("list".to_string())),
            args: vec![core_ir::TypeArg::Type(core_ir::Type::Union(vec![
                core_ir::Type::Var(principal_var.clone()),
                named_type("int"),
            ]))],
        };
        let list_of_int = core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name("list".to_string())),
            args: vec![core_ir::TypeArg::Type(named_type("int"))],
        };
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![core_ir::PrincipalBinding {
                    name: id_path,
                    scheme: core_ir::Scheme {
                        requirements: Vec::new(),
                        body: core_ir::Type::Var(principal_var),
                    },
                    body: core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string())),
                }],
                root_exprs: vec![core_ir::Expr::Lit(core_ir::Lit::Unit)],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds {
                        lower: Some(Box::new(list_with_principal_var)),
                        upper: None,
                    },
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
        };
        let lowerer = Lowerer {
            env: HashMap::new(),
            binding_infos: HashMap::new(),
            aliases: HashMap::new(),
            graph: &program.graph,
            runtime_symbols: HashMap::new(),
            principal_vars: principal_module_type_vars(&program.program),
            principal_evidence: &core_ir::PrincipalEvidence::default(),
            use_expected_arg_evidence: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };

        assert_eq!(lowerer.root_graph_type(0), Some(list_of_int));
    }

    #[test]
    pub(super) fn prepare_thunk_expected_type_keeps_more_concrete_actual_value() {
        let value_var = core_ir::TypeVar("value".to_string());
        let expected = RuntimeType::thunk(
            named_type("undet"),
            RuntimeType::core(core_ir::Type::Var(value_var)),
        );
        let expr = Expr::typed(
            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
            RuntimeType::core(named_type("int")),
        );

        let prepared =
            prepare_expr_for_expected(expr, &expected, TypeSource::Expected).expect("prepared");

        let RuntimeType::Thunk { value, .. } = &prepared.ty else {
            panic!("expected a thunk");
        };
        assert_eq!(core_type(value), &named_type("int"));
    }

    #[test]
    pub(super) fn lower_role_method_var_resolves_concrete_impl_from_expected_receiver() {
        let role_path = core_ir::Path::new(vec![
            core_ir::Name("std".to_string()),
            core_ir::Name("prelude".to_string()),
            core_ir::Name("Add".to_string()),
            core_ir::Name("add".to_string()),
        ]);
        let int_impl = core_ir::Path::new(vec![
            core_ir::Name("std".to_string()),
            core_ir::Name("prelude".to_string()),
            core_ir::Name("&impl#int".to_string()),
            core_ir::Name("add".to_string()),
        ]);
        let float_impl = core_ir::Path::new(vec![
            core_ir::Name("std".to_string()),
            core_ir::Name("prelude".to_string()),
            core_ir::Name("&impl#float".to_string()),
            core_ir::Name("add".to_string()),
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
            graph: &core_ir::CoreGraphView::default(),
            runtime_symbols: HashMap::from([(
                role_path.clone(),
                core_ir::RuntimeSymbolKind::RoleMethod,
            )]),
            principal_vars: BTreeSet::new(),
            principal_evidence: &core_ir::PrincipalEvidence::default(),
            use_expected_arg_evidence: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };

        let expected_ty = RuntimeType::fun(
            RuntimeType::core(named_type("int")),
            RuntimeType::fun(
                RuntimeType::core(named_type("int")),
                RuntimeType::thunk(
                    core_ir::Type::Var(core_ir::TypeVar("effect".to_string())),
                    RuntimeType::core(core_ir::Type::Var(core_ir::TypeVar("value".to_string()))),
                ),
            ),
        );

        let expr = lowerer
            .lower_expr(
                core_ir::Expr::Var(role_path.clone()),
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
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![core_ir::Expr::Block {
                    stmts: vec![core_ir::Stmt::Let {
                        pattern: core_ir::Pattern::Bind(core_ir::Name("f".to_string())),
                        value: core_ir::Expr::Lambda {
                            param: core_ir::Name("x".to_string()),
                            param_effect_annotation: None,
                            param_function_allowed_effects: None,
                            body: Box::new(core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))),
                        },
                    }],
                    tail: Some(Box::new(core_ir::Expr::Lit(core_ir::Lit::Unit))),
                }],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(unit_type()),
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
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
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView::default(),
            evidence: core_ir::PrincipalEvidence::default(),
        };

        assert!(matches!(
            lower_core_program(program),
            Err(RuntimeError::MissingRootType { index: 0 })
        ));
    }

    #[test]
    pub(super) fn lower_binding_prefers_principal_scheme_over_wide_graph_bounds() {
        let point = named_type("point");
        let record = core_ir::Type::Record(core_ir::RecordType {
            fields: vec![core_ir::RecordField {
                name: core_ir::Name("x".to_string()),
                value: named_type("int"),
                optional: false,
            }],
            spread: None,
        });
        let point_ctor_ty = core_ir::Type::Fun {
            param: Box::new(record.clone()),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(point.clone()),
        };
        let point_path = core_ir::Path::from_name(core_ir::Name("point".to_string()));
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![core_ir::PrincipalBinding {
                    name: point_path.clone(),
                    scheme: core_ir::Scheme {
                        requirements: Vec::new(),
                        body: point_ctor_ty.clone(),
                    },
                    body: core_ir::Expr::Lambda {
                        param: core_ir::Name("value".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(core_ir::Expr::Coerce {
                            expr: Box::new(core_ir::Expr::Var(core_ir::Path::from_name(
                                core_ir::Name("value".to_string()),
                            ))),
                            evidence: None,
                        }),
                    },
                }],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: core_ir::CoreGraphView {
                bindings: vec![core_ir::BindingGraphNode {
                    binding: point_path,
                    scheme_body: point_ctor_ty.clone(),
                    body_bounds: core_ir::TypeBounds::upper(core_ir::Type::Any),
                }],
                root_exprs: Vec::new(),
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");

        assert_eq!(
            module.bindings[0].body.ty,
            RuntimeType::fun(RuntimeType::core(record), RuntimeType::core(point))
        );
    }

    #[test]
    pub(super) fn lower_direct_alias_prefers_more_concrete_target_type() {
        let effect_var = core_ir::TypeVar("e".to_string());
        let target_path = core_ir::Path::new(vec![
            core_ir::Name("std".to_string()),
            core_ir::Name("range".to_string()),
            core_ir::Name("from_included".to_string()),
        ]);
        let alias_path = core_ir::Path::new(vec![
            core_ir::Name("std".to_string()),
            core_ir::Name("prelude".to_string()),
            core_ir::Name("#op:suffix:..".to_string()),
        ]);
        let pure_ty = core_ir::Type::Fun {
            param: Box::new(named_type("int")),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(named_type("range")),
        };
        let polluted_alias_ty = core_ir::Type::Fun {
            param: Box::new(named_type("int")),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Named {
                path: core_ir::Path::new(vec![
                    core_ir::Name("std".to_string()),
                    core_ir::Name("flow".to_string()),
                    core_ir::Name("sub".to_string()),
                ]),
                args: vec![core_ir::TypeArg::Type(core_ir::Type::Var(effect_var))],
            }),
            ret: Box::new(named_type("range")),
        };
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![
                    core_ir::PrincipalBinding {
                        name: alias_path.clone(),
                        scheme: core_ir::Scheme {
                            requirements: Vec::new(),
                            body: polluted_alias_ty,
                        },
                        body: core_ir::Expr::Var(target_path.clone()),
                    },
                    core_ir::PrincipalBinding {
                        name: target_path,
                        scheme: core_ir::Scheme {
                            requirements: Vec::new(),
                            body: pure_ty.clone(),
                        },
                        body: core_ir::Expr::PrimitiveOp(core_ir::PrimitiveOp::IntToString),
                    },
                ],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: core_ir::CoreGraphView::default(),
            evidence: core_ir::PrincipalEvidence::default(),
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
        let a = core_ir::TypeVar("a".to_string());
        let id_path = core_ir::Path::from_name(core_ir::Name("id".to_string()));
        let id_ty = core_ir::Type::Fun {
            param: Box::new(core_ir::Type::Var(a.clone())),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(core_ir::Type::Var(a.clone())),
        };
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![core_ir::PrincipalBinding {
                    name: id_path.clone(),
                    scheme: core_ir::Scheme {
                        requirements: Vec::new(),
                        body: id_ty,
                    },
                    body: core_ir::Expr::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(core_ir::Expr::Var(core_ir::Path::from_name(
                            core_ir::Name("x".to_string()),
                        ))),
                    },
                }],
                root_exprs: vec![core_ir::Expr::Apply {
                    callee: Box::new(core_ir::Expr::Var(id_path.clone())),
                    arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))),
                    evidence: None,
                }],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(named_type("int")),
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
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
        let k_path = core_ir::Path::from_name(core_ir::Name("k".to_string()));
        let action_path = core_ir::Path {
            segments: vec![
                core_ir::Name("std".to_string()),
                core_ir::Name("junction".to_string()),
                core_ir::Name("or".to_string()),
                core_ir::Name("choose".to_string()),
            ],
        };
        let effect_path = core_ir::Path {
            segments: vec![
                core_ir::Name("std".to_string()),
                core_ir::Name("junction".to_string()),
                core_ir::Name("or".to_string()),
            ],
        };
        let handled_effect = core_ir::Type::Row {
            items: vec![core_ir::Type::Named {
                path: effect_path.clone(),
                args: Vec::new(),
            }],
            tail: Box::new(core_ir::Type::Never),
        };
        let effect_op_ty = core_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(handled_effect.clone()),
            ret: Box::new(bool_type()),
        };
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![core_ir::Expr::Handle {
                    body: Box::new(core_ir::Expr::Apply {
                        callee: Box::new(core_ir::Expr::Var(action_path.clone())),
                        arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Unit)),
                        evidence: Some(core_ir::ApplyEvidence {
                            arg_source_edge: None,
                            callee: core_ir::TypeBounds::exact(effect_op_ty),
                            arg: core_ir::TypeBounds::exact(unit_type()),
                            expected_arg: None,
                            result: core_ir::TypeBounds::exact(bool_type()),
                            principal_callee: None,
                            substitutions: Vec::new(),
                            role_method: false,
                        }),
                    }),
                    arms: vec![core_ir::HandleArm {
                        effect: action_path.clone(),
                        payload: core_ir::Pattern::Wildcard,
                        resume: Some(core_ir::Name("k".to_string())),
                        guard: None,
                        body: core_ir::Expr::Apply {
                            callee: Box::new(core_ir::Expr::Var(k_path)),
                            arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Bool(true))),
                            evidence: Some(core_ir::ApplyEvidence {
                                arg_source_edge: None,
                                callee: core_ir::TypeBounds::exact(core_ir::Type::Any),
                                arg: core_ir::TypeBounds::exact(bool_type()),
                                expected_arg: None,
                                result: core_ir::TypeBounds::exact(bool_type()),
                                principal_callee: None,
                                substitutions: Vec::new(),
                                role_method: false,
                            }),
                        },
                    }],
                    evidence: Some(core_ir::JoinEvidence {
                        result: core_ir::TypeBounds::exact(bool_type()),
                    }),
                }],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(bool_type()),
                }],
                runtime_symbols: vec![core_ir::RuntimeSymbol {
                    path: action_path,
                    kind: core_ir::RuntimeSymbolKind::EffectOperation,
                }],
            },
            evidence: core_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");

        assert_eq!(core_type(&module.root_exprs[0].ty), &bool_type());
        let ExprKind::Handle { arms, handler, .. } = &module.root_exprs[0].kind else {
            panic!("missing handle");
        };
        assert_eq!(handler.consumes, vec![effect_path]);
        let resume = arms[0].resume.as_ref().expect("resume binding");
        assert_eq!(resume.name, core_ir::Name("k".to_string()));
        let RuntimeType::Fun { param, ret } = &resume.ty else {
            panic!("resume should be a function");
        };
        assert_eq!(**param, RuntimeType::core(bool_type()));
        assert_eq!(**ret, RuntimeType::core(bool_type()));
    }

    #[test]
    pub(super) fn lower_handle_payload_uses_arm_body_context() {
        let payload_name = core_ir::Name("payload".to_string());
        let effect_path = core_ir::Path::from_name(core_ir::Name("ret".to_string()));
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![core_ir::Expr::Handle {
                    body: Box::new(core_ir::Expr::Lit(core_ir::Lit::Bool(true))),
                    arms: vec![core_ir::HandleArm {
                        effect: effect_path,
                        payload: core_ir::Pattern::Bind(payload_name.clone()),
                        resume: None,
                        guard: None,
                        body: core_ir::Expr::Var(core_ir::Path::from_name(payload_name.clone())),
                    }],
                    evidence: Some(core_ir::JoinEvidence {
                        result: core_ir::TypeBounds::exact(bool_type()),
                    }),
                }],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(bool_type()),
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
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
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![core_ir::Expr::If {
                    cond: Box::new(core_ir::Expr::Lit(core_ir::Lit::Bool(true))),
                    then_branch: Box::new(core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))),
                    else_branch: Box::new(core_ir::Expr::Lit(core_ir::Lit::Float(
                        "2.0".to_string(),
                    ))),
                    evidence: Some(core_ir::JoinEvidence {
                        result: core_ir::TypeBounds::exact(named_type("float")),
                    }),
                }],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(named_type("float")),
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
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
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![core_ir::Expr::Coerce {
                    expr: Box::new(core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))),
                    evidence: Some(core_ir::CoerceEvidence {
                        source_edge: None,
                        actual: core_ir::TypeBounds::exact(named_type("int")),
                        expected: core_ir::TypeBounds::exact(named_type("float")),
                    }),
                }],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(named_type("float")),
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
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
    pub(super) fn lower_unbound_qualified_path_as_effect_op() {
        let effect_path = core_ir::Path {
            segments: vec![
                core_ir::Name("std".to_string()),
                core_ir::Name("junction".to_string()),
                core_ir::Name("or".to_string()),
            ],
        };
        let effect_ty = core_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(bool_type()),
        };
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![core_ir::Expr::Apply {
                    callee: Box::new(core_ir::Expr::Var(effect_path.clone())),
                    arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Unit)),
                    evidence: Some(core_ir::ApplyEvidence {
                        arg_source_edge: None,
                        callee: core_ir::TypeBounds::exact(effect_ty),
                        arg: core_ir::TypeBounds::exact(unit_type()),
                        expected_arg: None,
                        result: core_ir::TypeBounds::exact(bool_type()),
                        principal_callee: None,
                        substitutions: Vec::new(),
                        role_method: false,
                    }),
                }],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(bool_type()),
                }],
                runtime_symbols: vec![core_ir::RuntimeSymbol {
                    path: effect_path.clone(),
                    kind: core_ir::RuntimeSymbolKind::EffectOperation,
                }],
            },
            evidence: core_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::BindHere { expr } = &module.root_exprs[0].kind else {
            panic!("missing bind_here");
        };
        let ExprKind::Thunk { expr, .. } = &expr.kind else {
            panic!("missing thunk");
        };
        let ExprKind::Apply { callee, .. } = &expr.kind else {
            panic!("missing apply");
        };
        assert!(matches!(&callee.kind, ExprKind::EffectOp(path) if path == &effect_path));
    }

    #[test]
    pub(super) fn lower_effectful_apply_in_value_context_inserts_bind_here() {
        let effect = core_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(core_ir::Type::Never),
        };
        let fn_ty = core_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(named_type("int")),
        };
        let action_path = core_ir::Path::from_name(core_ir::Name("action".to_string()));
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![core_ir::PrincipalBinding {
                    name: action_path.clone(),
                    scheme: core_ir::Scheme {
                        requirements: Vec::new(),
                        body: fn_ty.clone(),
                    },
                    body: core_ir::Expr::Lambda {
                        param: core_ir::Name("unit".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))),
                    },
                }],
                root_exprs: vec![core_ir::Expr::Apply {
                    callee: Box::new(core_ir::Expr::Var(action_path)),
                    arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Unit)),
                    evidence: Some(core_ir::ApplyEvidence {
                        arg_source_edge: None,
                        callee: core_ir::TypeBounds::exact(fn_ty),
                        arg: core_ir::TypeBounds::exact(unit_type()),
                        expected_arg: None,
                        result: core_ir::TypeBounds::exact(named_type("int")),
                        principal_callee: None,
                        substitutions: Vec::new(),
                        role_method: false,
                    }),
                }],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(named_type("int")),
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
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
        let effect = core_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(core_ir::Type::Never),
        };
        let fn_ty = core_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(named_type("int")),
        };
        let action_path = core_ir::Path::from_name(core_ir::Name("action".to_string()));
        let tuple_ty = core_ir::Type::Tuple(vec![named_type("int"), named_type("int")]);
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![effectful_action_binding(action_path.clone(), fn_ty.clone())],
                root_exprs: vec![core_ir::Expr::Tuple(vec![
                    effectful_action_apply(action_path, fn_ty),
                    core_ir::Expr::Lit(core_ir::Lit::Int("2".to_string())),
                ])],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(tuple_ty.clone()),
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
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
        let effect = core_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(core_ir::Type::Never),
        };
        let fn_ty = core_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(named_type("int")),
        };
        let action_path = core_ir::Path::from_name(core_ir::Name("action".to_string()));
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![effectful_action_binding(action_path.clone(), fn_ty.clone())],
                root_exprs: vec![core_ir::Expr::If {
                    cond: Box::new(core_ir::Expr::Lit(core_ir::Lit::Bool(true))),
                    then_branch: Box::new(effectful_action_apply(action_path, fn_ty)),
                    else_branch: Box::new(core_ir::Expr::Lit(core_ir::Lit::Int("2".to_string()))),
                    evidence: Some(core_ir::JoinEvidence {
                        result: core_ir::TypeBounds::exact(named_type("int")),
                    }),
                }],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: vec![core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(0),
                    bounds: core_ir::TypeBounds::exact(named_type("int")),
                }],
                runtime_symbols: Vec::new(),
            },
            evidence: core_ir::PrincipalEvidence::default(),
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
        let effect = core_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(core_ir::Type::Never),
        };
        let fn_ty = core_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(named_type("int")),
        };
        let binding_path = core_ir::Path::from_name(core_ir::Name("f".to_string()));
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![core_ir::PrincipalBinding {
                    name: binding_path,
                    scheme: core_ir::Scheme {
                        requirements: Vec::new(),
                        body: fn_ty,
                    },
                    body: core_ir::Expr::Lambda {
                        param: core_ir::Name("unit".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))),
                    },
                }],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: core_ir::CoreGraphView::default(),
            evidence: core_ir::PrincipalEvidence::default(),
        };

        let module = lower_core_program(program).expect("lowered");
        let ExprKind::Lambda { body, .. } = &module.bindings[0].body.kind else {
            panic!("expected lambda");
        };
        let ExprKind::LocalPushId { body, .. } = &body.kind else {
            panic!("expected local push around thunk admin");
        };
        let ExprKind::AddId { id, allowed, thunk } = &body.kind else {
            panic!("expected add_id around created thunk");
        };
        assert_eq!(*id, EffectIdRef::Peek);
        assert_eq!(allowed, &effect);
        assert!(matches!(thunk.kind, ExprKind::Thunk { .. }));
    }

    #[test]
    pub(super) fn add_id_uses_thunk_effect() {
        let undet = core_ir::Type::Row {
            items: vec![named_type("undet")],
            tail: Box::new(core_ir::Type::Never),
        };
        let value = RuntimeType::core(named_type("int"));
        let inner = Expr::typed(
            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
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

        let ExprKind::AddId { id, allowed, thunk } = &expr.kind else {
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
        let io_path = core_ir::Path::from_name(core_ir::Name("io".to_string()));
        let undet = core_ir::Type::Row {
            items: vec![named_type("undet")],
            tail: Box::new(core_ir::Type::Never),
        };
        let value = RuntimeType::core(named_type("int"));
        let param_ty = RuntimeType::thunk(undet.clone(), value.clone());

        let protected = apply_param_allowed_effect(
            param_ty,
            None,
            Some(&core_ir::FunctionSigAllowedEffects::Effects(vec![io_path])),
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
        let effect_path = core_ir::Path {
            segments: vec![
                core_ir::Name("io".to_string()),
                core_ir::Name("abort".to_string()),
            ],
        };
        let effect = core_ir::Type::Row {
            items: vec![named_type("io")],
            tail: Box::new(core_ir::Type::Never),
        };
        let effect_op_ty = core_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(effect.clone()),
            ret: Box::new(core_ir::Type::Never),
        };
        let wrapper_path = core_ir::Path::from_name(core_ir::Name("wrapper".to_string()));
        let anonymous_effect_ty = core_ir::Type::Fun {
            param: Box::new(unit_type()),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Var(core_ir::TypeVar("_".to_string()))),
            ret: Box::new(core_ir::Type::Never),
        };
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![core_ir::PrincipalBinding {
                    name: wrapper_path,
                    scheme: core_ir::Scheme {
                        requirements: Vec::new(),
                        body: anonymous_effect_ty,
                    },
                    body: core_ir::Expr::Lambda {
                        param: core_ir::Name("unit".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(core_ir::Expr::Apply {
                            callee: Box::new(core_ir::Expr::Var(effect_path.clone())),
                            arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Unit)),
                            evidence: Some(core_ir::ApplyEvidence {
                                arg_source_edge: None,
                                callee: core_ir::TypeBounds::exact(effect_op_ty),
                                arg: core_ir::TypeBounds::exact(unit_type()),
                                expected_arg: None,
                                result: core_ir::TypeBounds::exact(core_ir::Type::Never),
                                principal_callee: None,
                                substitutions: Vec::new(),
                                role_method: false,
                            }),
                        }),
                    },
                }],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: core_ir::CoreGraphView {
                bindings: Vec::new(),
                root_exprs: Vec::new(),
                runtime_symbols: vec![core_ir::RuntimeSymbol {
                    path: effect_path,
                    kind: core_ir::RuntimeSymbolKind::EffectOperation,
                }],
            },
            evidence: core_ir::PrincipalEvidence::default(),
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
        assert_eq!(core_type(value), &core_ir::Type::Never);
    }

    #[test]
    pub(super) fn lower_apply_uses_evidence_for_any_local_callee() {
        let mut lowerer = Lowerer {
            env: HashMap::new(),
            binding_infos: HashMap::new(),
            aliases: HashMap::new(),
            graph: &core_ir::CoreGraphView::default(),
            runtime_symbols: HashMap::new(),
            principal_vars: BTreeSet::new(),
            principal_evidence: &core_ir::PrincipalEvidence::default(),
            use_expected_arg_evidence: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };
        let local = core_ir::Path::from_name(core_ir::Name("k".to_string()));
        let mut locals = HashMap::from([(local.clone(), RuntimeType::core(core_ir::Type::Any))]);
        let expr = core_ir::Expr::Apply {
            callee: Box::new(core_ir::Expr::Var(local)),
            arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Unit)),
            evidence: Some(core_ir::ApplyEvidence {
                arg_source_edge: None,
                callee: core_ir::TypeBounds {
                    lower: None,
                    upper: Some(Box::new(core_ir::Type::Any)),
                },
                arg: core_ir::TypeBounds::exact(unit_type()),
                expected_arg: None,
                result: core_ir::TypeBounds::exact(named_type("int")),
                principal_callee: None,
                substitutions: Vec::new(),
                role_method: false,
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
            graph: &core_ir::CoreGraphView::default(),
            runtime_symbols: HashMap::new(),
            principal_vars: BTreeSet::new(),
            principal_evidence: &core_ir::PrincipalEvidence::default(),
            use_expected_arg_evidence: true,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };
        let callee_path = core_ir::Path::from_name(core_ir::Name("k".to_string()));
        let arg_path = core_ir::Path::from_name(core_ir::Name("x".to_string()));
        let mut locals = HashMap::from([
            (callee_path.clone(), RuntimeType::core(core_ir::Type::Any)),
            (arg_path.clone(), RuntimeType::core(core_ir::Type::Any)),
        ]);
        let expr = core_ir::Expr::Apply {
            callee: Box::new(core_ir::Expr::Var(callee_path.clone())),
            arg: Box::new(core_ir::Expr::Var(arg_path.clone())),
            evidence: Some(core_ir::ApplyEvidence {
                arg_source_edge: Some(3),
                callee: core_ir::TypeBounds {
                    lower: None,
                    upper: Some(Box::new(core_ir::Type::Any)),
                },
                arg: core_ir::TypeBounds::exact(core_ir::Type::Any),
                expected_arg: Some(core_ir::TypeBounds::exact(named_type("int"))),
                result: core_ir::TypeBounds::exact(named_type("int")),
                principal_callee: None,
                substitutions: Vec::new(),
                role_method: false,
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
        assert_eq!(lowerer.expected_arg_evidence_profile.available, 1);
        assert!(lowerer.expected_arg_evidence_profile.used >= 1);
    }

    #[test]
    pub(super) fn lower_apply_uses_fold_requirement_to_refine_associated_result() {
        let container = core_ir::TypeVar("container".to_string());
        let item = core_ir::TypeVar("item".to_string());
        let each_path = core_ir::Path::from_name(core_ir::Name("each".to_string()));
        let list_int = list_type(named_type("int"));
        let each_ty = RuntimeType::fun(
            RuntimeType::core(core_ir::Type::Var(container.clone())),
            RuntimeType::thunk(
                named_type("undet"),
                RuntimeType::core(core_ir::Type::Var(item.clone())),
            ),
        );
        let mut lowerer = Lowerer {
            env: HashMap::from([(each_path.clone(), each_ty.clone())]),
            binding_infos: HashMap::from([(
                each_path.clone(),
                BindingInfo {
                    ty: each_ty,
                    type_params: vec![container.clone(), item.clone()],
                    requirements: vec![core_ir::RoleRequirement {
                        role: core_ir::Path::new(vec![
                            core_ir::Name("std".to_string()),
                            core_ir::Name("fold".to_string()),
                            core_ir::Name("Fold".to_string()),
                        ]),
                        args: vec![
                            core_ir::RoleRequirementArg::Input(core_ir::TypeBounds::exact(
                                core_ir::Type::Var(container),
                            )),
                            core_ir::RoleRequirementArg::Associated {
                                name: core_ir::Name("item".to_string()),
                                bounds: core_ir::TypeBounds::exact(core_ir::Type::Var(item)),
                            },
                        ],
                    }],
                },
            )]),
            aliases: HashMap::new(),
            graph: &core_ir::CoreGraphView::default(),
            runtime_symbols: HashMap::new(),
            principal_vars: BTreeSet::new(),
            principal_evidence: &core_ir::PrincipalEvidence::default(),
            use_expected_arg_evidence: false,
            expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
            next_synthetic_type_var: 0,
            next_effect_id_var: 0,
        };
        let xs = core_ir::Path::from_name(core_ir::Name("xs".to_string()));
        let mut locals = HashMap::from([(xs.clone(), RuntimeType::core(list_int))]);
        let expr = core_ir::Expr::Apply {
            callee: Box::new(core_ir::Expr::Var(each_path)),
            arg: Box::new(core_ir::Expr::Var(xs)),
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
        name: core_ir::Path,
        fn_ty: core_ir::Type,
    ) -> core_ir::PrincipalBinding {
        core_ir::PrincipalBinding {
            name,
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: fn_ty,
            },
            body: core_ir::Expr::Lambda {
                param: core_ir::Name("unit".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))),
            },
        }
    }

    pub(super) fn effectful_action_apply(
        path: core_ir::Path,
        fn_ty: core_ir::Type,
    ) -> core_ir::Expr {
        core_ir::Expr::Apply {
            callee: Box::new(core_ir::Expr::Var(path)),
            arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Unit)),
            evidence: Some(core_ir::ApplyEvidence {
                arg_source_edge: None,
                callee: core_ir::TypeBounds::exact(fn_ty),
                arg: core_ir::TypeBounds::exact(unit_type()),
                expected_arg: None,
                result: core_ir::TypeBounds::exact(named_type("int")),
                principal_callee: None,
                substitutions: Vec::new(),
                role_method: false,
            }),
        }
    }

    pub(super) fn list_type(item: core_ir::Type) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::new(vec![
                core_ir::Name("std".to_string()),
                core_ir::Name("list".to_string()),
                core_ir::Name("list".to_string()),
            ]),
            args: vec![core_ir::TypeArg::Type(item)],
        }
    }
}
