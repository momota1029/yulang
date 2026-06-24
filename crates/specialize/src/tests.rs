mod tests {
    use crate::{
        boundary_expr, boundary_expr_with_hygiene, hygiene, specialize, specialize_roots,
        specialize2,
    };
    use mono::{
        ComputationType, EffectiveThunkType, ExprKind, GuardMarker, InstanceSource, Lit, Type,
    };

    #[test]
    fn empty_arena_specializes_to_empty_program() {
        let arena = poly::expr::Arena::new();
        let program = specialize(&arena).expect("empty arena should specialize");

        assert!(program.roots.is_empty());
        assert!(program.instances.is_empty());
    }

    #[test]
    fn specialize2_empty_arena_specializes_to_empty_program() {
        let arena = poly::expr::Arena::new();
        let program = specialize2(&arena).expect("empty arena should specialize");

        assert!(program.roots.is_empty());
        assert!(program.instances.is_empty());
    }

    #[test]
    fn default_specialize_does_not_treat_arena_roots_as_runtime_demands() {
        let mut arena = poly::expr::Arena::new();
        let def = arena.defs.fresh();
        arena.defs.set(
            def,
            poly::expr::Def::Let {
                vis: poly::expr::Vis::My,
                scheme: None,
                body: None,
                children: Vec::new(),
            },
        );
        arena.roots.push(def);

        let program = specialize(&arena).expect("unused arena roots should not be specialized");

        assert!(program.roots.is_empty());
        assert!(program.instances.is_empty());
    }

    #[test]
    fn boundary_expr_uses_coerce_for_value_boundary() {
        let actual = int_type();
        let expected = float_type();
        let expr = mono::Expr::new(ExprKind::Lit(Lit::Int(1)));

        let wrapped = boundary_expr(&actual, &expected, expr.clone());

        assert_eq!(
            wrapped.kind,
            ExprKind::Coerce {
                source: actual,
                target: expected,
                expr: Box::new(expr),
            }
        );
    }

    #[test]
    fn boundary_expr_uses_adapter_for_function_boundary() {
        let actual = pure_function_type(int_type(), int_type());
        let expected = pure_function_type(int_type(), float_type());
        let function = mono::Expr::new(ExprKind::Local(mono::DefId(0)));

        let wrapped = boundary_expr(&actual, &expected, function.clone());

        let ExprKind::FunctionAdapter {
            source,
            target,
            function: wrapped_function,
            hygiene,
        } = wrapped.kind
        else {
            panic!("function boundary should produce adapter");
        };
        assert_eq!(source, actual);
        assert_eq!(target, expected);
        assert_eq!(*wrapped_function, function);
        assert!(hygiene.markers.is_empty());
    }

    #[test]
    fn boundary_expr_hygiene_does_not_mark_expected_only_thunk_argument() {
        let effect = io_effect_type();
        let actual = pure_function_type(thunk_type(effect, int_type()), int_type());
        let expected = pure_function_type(int_type(), int_type());
        let function = mono::Expr::new(ExprKind::Local(mono::DefId(0)));

        let wrapped = boundary_expr(&actual, &expected, function);

        let ExprKind::FunctionAdapter { hygiene, .. } = wrapped.kind else {
            panic!("function boundary should produce adapter");
        };
        assert!(hygiene.markers.is_empty());
    }

    #[test]
    fn boundary_expr_hygiene_marks_actual_thunk_argument() {
        let effect = io_effect_type();
        let actual = pure_function_type(int_type(), int_type());
        let expected = pure_function_type(thunk_type(effect, int_type()), int_type());
        let function = mono::Expr::new(ExprKind::Local(mono::DefId(0)));

        let wrapped = boundary_expr(&actual, &expected, function);

        let ExprKind::FunctionAdapter { hygiene, .. } = wrapped.kind else {
            panic!("function boundary should produce adapter");
        };
        assert_eq!(
            hygiene.markers,
            vec![GuardMarker {
                path: vec!["io".to_string()],
                depth: 0,
                guard_own_path: true,
                guard_foreign_path: false,
                preserve_own_on_resume: false,
            }]
        );
    }

    #[test]
    fn boundary_expr_hygiene_does_not_mark_expected_only_nested_function_boundary() {
        let effect = io_effect_type();
        let actual = pure_function_type(
            pure_function_type(int_type(), thunk_type(effect, int_type())),
            int_type(),
        );
        let expected = pure_function_type(pure_function_type(int_type(), int_type()), int_type());
        let function = mono::Expr::new(ExprKind::Local(mono::DefId(0)));

        let wrapped = boundary_expr(&actual, &expected, function);

        let ExprKind::FunctionAdapter { hygiene, .. } = wrapped.kind else {
            panic!("function boundary should produce adapter");
        };
        assert!(hygiene.markers.is_empty());
    }

    #[test]
    fn boundary_expr_hygiene_marks_actual_nested_function_boundary() {
        let effect = io_effect_type();
        let actual = pure_function_type(pure_function_type(int_type(), int_type()), int_type());
        let expected = pure_function_type(
            pure_function_type(int_type(), thunk_type(effect, int_type())),
            int_type(),
        );
        let function = mono::Expr::new(ExprKind::Local(mono::DefId(0)));

        let wrapped = boundary_expr(&actual, &expected, function);

        let ExprKind::FunctionAdapter { hygiene, .. } = wrapped.kind else {
            panic!("function boundary should produce adapter");
        };
        assert_eq!(
            hygiene.markers,
            vec![GuardMarker {
                path: vec!["io".to_string()],
                depth: 1,
                guard_own_path: true,
                guard_foreign_path: false,
                preserve_own_on_resume: false,
            }]
        );
    }

    #[test]
    fn boundary_expr_hygiene_marks_effectful_callback_contract_on_argument_only() {
        let effect = io_effect_type();
        let callback = pure_function_type(int_type(), thunk_type(effect.clone(), int_type()));
        let actual =
            pure_function_type(callback.clone(), pure_function_type(int_type(), int_type()));
        let expected = pure_function_type(
            callback,
            thunk_type(effect, pure_function_type(int_type(), int_type())),
        );
        let function = mono::Expr::new(ExprKind::Local(mono::DefId(0)));
        let hygiene =
            hygiene::function_adapter_hygiene_with_argument_contract(&actual, &expected, true);

        let wrapped = boundary_expr_with_hygiene(&actual, &expected, function, hygiene);

        let ExprKind::FunctionAdapter { hygiene, .. } = wrapped.kind else {
            panic!("function boundary should produce adapter");
        };
        assert!(hygiene.markers.is_empty());
        assert!(hygiene.ret_markers.is_empty());
        assert_eq!(
            hygiene.arg_markers,
            vec![GuardMarker {
                path: vec!["io".to_string()],
                depth: 1,
                guard_own_path: true,
                guard_foreign_path: false,
                preserve_own_on_resume: true,
            }]
        );
    }

    #[test]
    fn boundary_expr_hygiene_deduplicates_path_and_depth() {
        let effect = io_effect_type();
        let actual = pure_function_type(
            thunk_type(effect.clone(), int_type()),
            thunk_type(effect, int_type()),
        );
        let expected = pure_function_type(int_type(), int_type());
        let function = mono::Expr::new(ExprKind::Local(mono::DefId(0)));

        let wrapped = boundary_expr(&actual, &expected, function);

        let ExprKind::FunctionAdapter { hygiene, .. } = wrapped.kind else {
            panic!("function boundary should produce adapter");
        };
        assert_eq!(
            hygiene.markers,
            vec![GuardMarker {
                path: vec!["io".to_string()],
                depth: 0,
                guard_own_path: true,
                guard_foreign_path: false,
                preserve_own_on_resume: false,
            }]
        );
    }

    #[test]
    fn boundary_expr_uses_make_thunk_for_thunk_expected_boundary() {
        let actual = int_type();
        let effect = io_effect_type();
        let expected = thunk_type(effect.clone(), int_type());
        let body = mono::Expr::new(ExprKind::Lit(Lit::Int(1)));

        let wrapped = boundary_expr(&actual, &expected, body.clone());

        assert_eq!(
            wrapped.kind,
            ExprKind::MakeThunk {
                source: ComputationType {
                    effect: effect.clone(),
                    value: actual,
                },
                target: EffectiveThunkType {
                    effect,
                    value: int_type(),
                },
                body: Box::new(body),
            }
        );
    }

    #[test]
    fn boundary_expr_uses_force_thunk_for_thunk_actual_boundary() {
        let effect = io_effect_type();
        let actual = thunk_type(effect.clone(), int_type());
        let expected = int_type();
        let thunk = mono::Expr::new(ExprKind::Local(mono::DefId(0)));

        let wrapped = boundary_expr(&actual, &expected, thunk.clone());

        assert_eq!(
            wrapped.kind,
            ExprKind::ForceThunk {
                source: EffectiveThunkType {
                    effect: effect.clone(),
                    value: int_type(),
                },
                target: ComputationType {
                    effect,
                    value: expected,
                },
                thunk: Box::new(thunk),
            }
        );
    }

    #[test]
    fn string_input_does_not_materialize_unused_generic_binding() {
        let lowering = lower_source("my id x = x\n");

        let program =
            specialize(&lowering.session.poly).expect("unused generic binding should be ignored");

        assert!(program.roots.is_empty());
        assert!(program.instances.is_empty());
    }

    #[test]
    fn string_input_materializes_explicit_monomorphic_root() {
        let lowering = lower_source("my one = 1\n");
        let arena = &lowering.session.poly;
        let root = arena.roots[0];

        let program = specialize_roots(arena, [root]).expect("monomorphic root should specialize");

        assert_eq!(
            program.roots,
            vec![mono::Root::Instance(mono::InstanceId(0))]
        );
        assert_eq!(program.instances.len(), 1);
        assert_eq!(
            program.instances[0].source,
            InstanceSource::Def(mono::DefId(root.0))
        );
        assert_eq!(
            program.instances[0].signature.ty,
            Type::Con {
                path: vec!["int".to_string()],
                args: Vec::new()
            }
        );
        assert_eq!(program.instances[0].body.kind, ExprKind::Lit(Lit::Int(1)));
    }

    #[test]
    fn string_input_materializes_reachable_monomorphic_refs() {
        let lowering = lower_source("my one = 1\nmy two = one\n");
        let arena = &lowering.session.poly;
        let two = arena.roots[1];

        let program =
            specialize_roots(arena, [two]).expect("reachable monomorphic ref should specialize");

        assert_eq!(
            program.roots,
            vec![mono::Root::Instance(mono::InstanceId(0))]
        );
        assert_eq!(program.instances.len(), 2);
        assert_eq!(
            program.instances[0].source,
            InstanceSource::Def(mono::DefId(two.0))
        );
        assert_eq!(
            program.instances[0].body.kind,
            ExprKind::InstanceRef(mono::InstanceId(1))
        );
        assert_eq!(program.instances[1].body.kind, ExprKind::Lit(Lit::Int(1)));
    }

    #[test]
    fn string_input_defaults_explicit_generic_root_without_context() {
        let lowering = lower_source("my id x = x\n");
        let arena = &lowering.session.poly;
        let root = arena.roots[0];

        let program =
            specialize_roots(arena, [root]).expect("generic root should get a default signature");

        assert_eq!(
            mono::dump::dump_type(&program.instances[0].signature.ty),
            "unit -> unit"
        );
    }

    #[test]
    fn string_input_specializes_generic_ref_from_apply_argument_and_result() {
        let lowering = lower_source("my id x = x\nmy one = 1\nmy call = id(one)\n");
        let arena = &lowering.session.poly;
        let call = arena.roots[2];

        let program = specialize_roots(arena, [call])
            .expect("generic callee should specialize from apply context");

        assert_eq!(
            program.roots,
            vec![mono::Root::Instance(mono::InstanceId(0))]
        );
        assert_eq!(program.instances.len(), 3);
        assert_eq!(
            mono::dump::dump_type(&program.instances[1].signature.ty),
            "int -> int"
        );
        assert_eq!(
            program.instances[0].body.kind,
            ExprKind::Apply(
                Box::new(mono::Expr::new(ExprKind::InstanceRef(mono::InstanceId(1)))),
                Box::new(mono::Expr::new(ExprKind::InstanceRef(mono::InstanceId(2))))
            )
        );
    }

    #[test]
    fn string_input_specializes_root_expr_generic_call() {
        let lowering = lower_source("my id x = x\nid(1)\n");
        let arena = &lowering.session.poly;

        let program = specialize(arena).expect("root expr should specialize generic callee");

        assert_eq!(program.roots.len(), 1);
        assert_eq!(
            program.roots[0],
            mono::Root::Expr(mono::Expr::new(ExprKind::Apply(
                Box::new(mono::Expr::new(ExprKind::InstanceRef(mono::InstanceId(0)))),
                Box::new(mono::Expr::new(ExprKind::Lit(Lit::Int(1))))
            )))
        );
        assert_eq!(program.instances.len(), 1);
        assert_eq!(
            mono::dump::dump_type(&program.instances[0].signature.ty),
            "int -> int"
        );
    }

    #[test]
    fn specialize2_string_input_specializes_root_expr_generic_call() {
        let lowering = lower_source("my id x = x\nid(1)\n");
        let arena = &lowering.session.poly;

        let program = specialize2(arena).expect("root expr should specialize generic callee");

        assert_eq!(program.roots.len(), 1);
        assert_eq!(
            program.roots[0],
            mono::Root::Expr(mono::Expr::new(ExprKind::Apply(
                Box::new(mono::Expr::new(ExprKind::InstanceRef(mono::InstanceId(0)))),
                Box::new(mono::Expr::new(ExprKind::Lit(Lit::Int(1))))
            )))
        );
        assert_eq!(program.instances.len(), 1);
        assert_eq!(
            mono::dump::dump_type(&program.instances[0].signature.ty),
            "int -> int"
        );
    }

    #[test]
    fn specialize2_keeps_unreachable_type_slots_from_forcing_errors() {
        let lowering = lower_source("my const x y = x\nconst(1)\n");
        let arena = &lowering.session.poly;

        let program = specialize2(arena)
            .expect("unreachable unconstrained slots should not block specialization");
        let text = mono::dump::dump_program(&program);

        assert!(text.contains("unit -> int"), "{text}");
        assert!(!text.contains("OpenVar"), "{text}");
    }

    #[test]
    fn specialize2_record_pattern_default_uses_provided_field_type_for_later_default() {
        let lowering = lower_source(
            "my box { width = 1, height = width } = height\n\
             box { width: 1.2 }\n",
        );
        let arena = &lowering.session.poly;

        let program = specialize2(arena).expect("record default call should specialize");
        let text = mono::dump::dump_program(&program);

        assert!(text.contains("width: float"), "{text}");
        assert!(text.contains("-> float"), "{text}");
        assert!(!text.contains("width: int"), "{text}");
        assert!(!text.contains("float => int"), "{text}");
    }

    #[test]
    fn specialize2_string_input_specializes_root_case_with_direct_cast_join() {
        let lowering =
            lower_source("cast(x: int): float = 0.0\ncase true: true -> 1, false -> 2.0\n");
        let arena = &lowering.session.poly;

        let program = specialize2(arena).expect("root case should specialize through cast join");
        let text = mono::dump::dump_program(&program);

        assert!(text.contains("mono roots [case true:"), "{text}");
        assert!(text.contains("-> (m0 1)"), "{text}");
        assert!(text.contains("m0 = d0 : int -> float"), "{text}");
        assert!(!text.contains("coerce[int => float]"), "{text}");
        assert!(!text.contains("int | float"), "{text}");
    }

    #[test]
    fn specialize2_string_input_runs_computed_top_level_binding() {
        let lowering = lower_source("my id x = x\nmy a = id(1)\n");
        let arena = &lowering.session.poly;

        let program = specialize2(arena).expect("computed top-level binding should specialize");
        let text = mono::dump::dump_program(&program);

        assert!(text.contains("mono roots [eval m0]"), "{text}");
        assert!(text.contains("m0 = d1 : int"), "{text}");
        assert!(text.contains("m1 = d0 : int -> int"), "{text}");
    }

    #[test]
    fn string_input_keeps_block_local_let_as_local_value() {
        let lowering = lower_source(
            "my f x =\n\
             \x20 my y = x\n\
             \x20 y\n\
             f(1)\n",
        );
        let arena = &lowering.session.poly;

        let program = specialize(arena).expect("block local let should specialize in context");

        assert_eq!(program.instances.len(), 1);
        assert_eq!(
            mono::dump::dump_type(&program.instances[0].signature.ty),
            "int -> int"
        );
    }

    #[test]
    fn string_input_specializes_stack_quantified_handler_annotation() {
        let lowering = lower_source(
            "act signal:\n  our ping: () -> int\n\n\
             my handle(x: [_] int): int = catch x:\n\
             \x20 signal::ping(), k -> k 1\n\
             \x20 v -> v\n\n\
             handle(signal::ping())\n",
        );
        let arena = &lowering.session.poly;

        let program = specialize(arena).expect("[_] handler annotation should specialize");

        let [mono::Root::Expr(root)] = program.roots.as_slice() else {
            panic!("expected one root expression");
        };
        assert!(
            matches!(root.kind, ExprKind::Apply(_, _)),
            "root should already be a value application: {:?}",
            root.kind
        );
        assert_eq!(program.instances.len(), 1);
        let signature = mono::dump::dump_type(&program.instances[0].signature.ty);
        assert!(signature.ends_with(" -> int"), "{signature}");
        assert!(!signature.contains("stack("), "{signature}");
    }

    #[test]
    fn string_input_keeps_unused_effectful_thunk_argument_suspended() {
        let lowering = lower_source(
            "act out:\n  our read: () -> int\n\n\
             my keep(x: [_] int) = 1\n\
             keep(out::read(()))\n",
        );
        let arena = &lowering.session.poly;

        let program = specialize(arena).expect("effectful argument annotation should specialize");

        assert_eq!(program.instances.len(), 1);
        assert_eq!(
            mono::dump::dump_type(&program.instances[0].signature.ty),
            "thunk[any, int] -> int"
        );
        let dump = mono::dump::dump_program(&program);
        assert!(
            dump.contains("make-thunk[int ! [out] => thunk[any, int]]"),
            "{dump}"
        );
    }

    #[test]
    fn string_input_materializes_effect_operation_ref_as_effect_op() {
        let lowering = lower_source("act out:\n  our say: int -> unit\nout::say(1)\n");
        let arena = &lowering.session.poly;

        let program = specialize(arena).expect("effect operation root should specialize");

        let [mono::Root::Expr(root)] = program.roots.as_slice() else {
            panic!("expected one root expression");
        };
        let ExprKind::ForceThunk { thunk, .. } = &root.kind else {
            panic!("effect operation call should be forced at the root boundary");
        };
        let ExprKind::Apply(callee, arg) = &thunk.kind else {
            panic!("forced thunk should come from an operation application");
        };
        assert_eq!(
            callee.kind,
            ExprKind::EffectOp {
                path: vec!["out".to_string(), "say".to_string()]
            }
        );
        assert_eq!(arg.kind, ExprKind::Lit(Lit::Int(1)));
    }

    #[test]
    fn specialize2_string_input_materializes_effect_operation_ref_as_effect_op() {
        let lowering = lower_source("act out:\n  our say: int -> unit\nout::say(1)\n");
        let arena = &lowering.session.poly;

        let program = specialize2(arena).expect("effect operation root should specialize");

        let [mono::Root::Expr(root)] = program.roots.as_slice() else {
            panic!("expected one root expression");
        };
        let ExprKind::ForceThunk { thunk, .. } = &root.kind else {
            panic!("effect operation call should be forced at the root boundary");
        };
        let ExprKind::Apply(callee, arg) = &thunk.kind else {
            panic!("forced thunk should come from an operation application");
        };
        assert_eq!(
            callee.kind,
            ExprKind::EffectOp {
                path: vec!["out".to_string(), "say".to_string()]
            }
        );
        assert_eq!(arg.kind, ExprKind::Lit(Lit::Int(1)));
    }

    fn lower_source(source: &str) -> infer::lowering::BodyLowering {
        let files = sources::load(vec![sources::SourceFile {
            module_path: sources::Path::default(),
            source: source.to_string(),
        }]);
        let output = infer::dump::dump_loaded_files(&files).expect("source should lower");
        assert!(
            output.lowering.errors.is_empty(),
            "body lowering errors: {:?}",
            output.lowering.errors
        );
        output.lowering
    }

    fn pure_function_type(arg: Type, ret: Type) -> Type {
        Type::Fun {
            arg: Box::new(arg),
            arg_effect: Box::new(Type::pure_effect()),
            ret_effect: Box::new(Type::pure_effect()),
            ret: Box::new(ret),
        }
    }

    fn int_type() -> Type {
        Type::Con {
            path: vec!["int".to_string()],
            args: Vec::new(),
        }
    }

    fn float_type() -> Type {
        Type::Con {
            path: vec!["float".to_string()],
            args: Vec::new(),
        }
    }

    fn thunk_type(effect: Type, value: Type) -> Type {
        Type::Thunk {
            effect: Box::new(effect),
            value: Box::new(value),
        }
    }

    fn io_effect_type() -> Type {
        Type::EffectRow(vec![Type::Con {
            path: vec!["io".to_string()],
            args: Vec::new(),
        }])
    }
}
