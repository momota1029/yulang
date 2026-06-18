use mono::Type;

use super::{
    DefId, Expr, ExprId, Instance, InstanceId, Program, Root, RuntimeError, SelectResolution,
    ValidateError, Value, boundary::value_boundary_supported, format_values, lower,
    run_mono_program, run_program, run_program_with_host_and_stats, validate,
};

#[test]
fn lowers_empty_program() {
    assert_eq!(lower(&mono::Program::default()).unwrap().roots, Vec::new());
}

#[test]
fn lowers_root_expression_to_expr_arena() {
    let program = mono::Program {
        roots: vec![mono::Root::Expr(mono::Expr::new(mono::ExprKind::Lit(
            mono::Lit::Int(1),
        )))],
        instances: Vec::new(),
    };

    let lowered = lower(&program).unwrap();

    assert_eq!(lowered.roots, vec![Root::Expr(super::ExprId(0))]);
    assert_eq!(lowered.exprs.len(), 1);
    assert_eq!(run_program(&lowered), Ok(vec![Value::Int(1)]));
}

#[test]
fn eval_instance_root_runs_without_result_value() {
    let program = mono::Program {
        roots: vec![mono::Root::EvalInstance(mono::InstanceId(0))],
        instances: vec![mono::Instance {
            id: mono::InstanceId(0),
            source: mono::InstanceSource::Def(mono::DefId(0)),
            signature: mono::Signature {
                ty: mono::Type::Con {
                    path: vec!["int".to_string()],
                    args: Vec::new(),
                },
            },
            body: mono::Expr::new(mono::ExprKind::Lit(mono::Lit::Int(1))),
        }],
    };

    let lowered = lower(&program).unwrap();

    assert_eq!(
        lowered.roots,
        vec![Root::EvalInstance(super::InstanceId(0))]
    );
    assert_eq!(run_program(&lowered), Ok(Vec::new()));
}

#[test]
fn runs_specialized_generic_call_like_oracle() {
    assert_oracle_parity("my id x = x\nid(1)\n", "[1]");
}

#[test]
fn runs_apply_colon_block_argument_like_oracle() {
    assert_oracle_parity("my id x = x\nid:\n  my x = 1\n  x\n", "[1]");
}

#[test]
fn runs_higher_order_application_like_oracle() {
    assert_oracle_parity("my apply f = f(1)\nmy id x = x\napply id\n", "[1]");
}

#[test]
fn runs_stack_handler_hygiene_to_outer_handler() {
    assert_oracle_parity(
        "pub act sub 'a:\n\
             \x20 pub return: 'a -> never\n\
             \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
             \x20 \x20 return a, _ -> a\n\
             \x20 \x20 a -> a\n\n\
             our g h = sub::sub:\n\
             \x20 h 0\n\
             \x20 sub::return 1\n\n\
             sub::sub:\n\
             \x20 g \\i -> sub::return i\n\
             \x20 sub::return 2\n",
        "[0]",
    );
}

#[test]
fn runs_nested_handler_after_inner_resume_like_oracle() {
    assert_oracle_parity(
        "act inner:\n\
         \x20 pub ping: () -> int\n\
         act outer:\n\
         \x20 pub ping: () -> int\n\
         my body() =\n\
         \x20 catch inner::ping():\n\
         \x20 \x20 inner::ping(), k -> k(1)\n\
         \x20 \x20 value -> value\n\
         \x20 outer::ping()\n\
         catch body():\n\
         \x20 outer::ping(), k -> k(2)\n\
         \x20 value -> value\n",
        "[2]",
    );
}

#[test]
fn keeps_effectful_thunk_argument_suspended_like_oracle() {
    assert_oracle_parity(
        "act out:\n\
         \x20 pub read: () -> int\n\
         my keep(x: [_] int) = 1\n\
         keep(out::read(()))\n",
        "[1]",
    );
}

#[test]
fn forces_effectful_thunk_argument_under_handler_like_oracle() {
    assert_oracle_parity(
        "act out:\n\
         \x20 pub read: () -> int\n\
         my handle(x: [out] int) = catch x:\n\
         \x20 out::read(), k -> k(1)\n\
         \x20 value -> value\n\
         handle(out::read(()))\n",
        "[1]",
    );
}

#[test]
fn routes_foreign_thunk_effect_past_inner_handler_like_oracle() {
    assert_oracle_parity(
        "pub act sub 'a:\n\
         \x20 pub return: 'a -> never\n\
         \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
         \x20 \x20 return a, _ -> a\n\
         \x20 \x20 a -> a\n\n\
         my inner(x: [_] int): int = catch x:\n\
         \x20 sub::return a, _ -> 99\n\
         \x20 a -> a\n\n\
         sub::sub:\n\
         \x20 inner(sub::return 0)\n\
         \x20 sub::return 2\n",
        "[0]",
    );
}

#[test]
fn runs_record_case_payload_like_oracle() {
    assert_oracle_parity(
        "case { width: 1, height: 2 }:\n\
         \x20 { width, height } -> height\n\
         \x20 _ -> 0\n",
        "[2]",
    );
}

#[test]
fn runs_struct_field_projection_like_oracle() {
    assert_oracle_parity("struct User { age: int }\nUser({ age: 1 }).age\n", "[1]");
}

#[test]
fn runs_constructor_case_pattern_like_oracle() {
    assert_oracle_parity(
        "enum opt 'a:\n  none\n  some 'a\n\
         case opt::some 1:\n\
         \x20 opt::some x -> x\n\
         \x20 _ -> 0\n",
        "[1]",
    );
}

#[test]
fn runs_constructor_payload_effect_handler_like_oracle() {
    assert_oracle_parity(
        "enum opt 'a:\n\
         \x20 none\n\
         \x20 some 'a\n\
         act eff:\n\
         \x20 our send: opt int -> int\n\
         catch eff::send(opt::some 1):\n\
         \x20 eff::send(opt::some x), k -> k(x)\n\
         \x20 value -> value\n",
        "[1]",
    );
}

#[test]
fn reports_unhandled_effect() {
    let program = mono::Program {
        roots: vec![mono::Root::Expr(force_effect_call(
            vec!["out".to_string(), "say".to_string()],
            mono::Expr::new(mono::ExprKind::Lit(mono::Lit::Unit)),
        ))],
        instances: Vec::new(),
    };

    assert_eq!(
        run_mono_program(&program),
        Err(super::RunError::Runtime(RuntimeError::UnhandledEffect {
            path: vec!["out".to_string(), "say".to_string()]
        }))
    );
}

#[test]
fn runs_list_singleton_primitive() {
    let program = Program {
        roots: vec![Root::Expr(ExprId(2))],
        instances: Vec::new(),
        exprs: vec![
            Expr::PrimitiveOp {
                op: mono::PrimitiveOp::ListSingleton,
                context: mono::PrimitiveContext::default(),
            },
            Expr::Lit(mono::Lit::Int(1)),
            Expr::Apply {
                callee: ExprId(0),
                arg: ExprId(1),
            },
        ],
    };

    let values = run_program(&program).unwrap();
    assert_eq!(format_values(&values), "[[1]]");
}

#[test]
fn direct_binary_primitive_instance_ref_skips_partial_primitive_value() {
    let program = Program {
        roots: vec![Root::Expr(ExprId(5))],
        instances: vec![Instance {
            id: InstanceId(0),
            source: mono::InstanceSource::Def(mono::DefId(0)),
            signature: mono::Signature { ty: int_type() },
            entry: ExprId(0),
        }],
        exprs: vec![
            Expr::PrimitiveOp {
                op: mono::PrimitiveOp::IntAdd,
                context: mono::PrimitiveContext::default(),
            },
            Expr::InstanceRef(InstanceId(0)),
            Expr::Lit(mono::Lit::Int(2)),
            Expr::Apply {
                callee: ExprId(1),
                arg: ExprId(2),
            },
            Expr::Lit(mono::Lit::Int(3)),
            Expr::Apply {
                callee: ExprId(3),
                arg: ExprId(4),
            },
        ],
    };

    let (values, stats) = run_program_with_host_and_stats(&program, &mut |_, _| None).unwrap();
    assert_eq!(values, vec![Value::Int(5)]);
    assert_eq!(stats.apply_primitive_calls, 0);
    assert_eq!(stats.primitive_apply_partial, 0);
    assert_eq!(stats.primitive_apply_complete, 1);
}

#[test]
fn validation_rejects_unresolved_typeclass_method() {
    let program = Program {
        roots: vec![Root::Expr(ExprId(1))],
        instances: Vec::new(),
        exprs: vec![
            Expr::Lit(mono::Lit::Unit),
            Expr::Select {
                base: ExprId(0),
                name: "show".to_string(),
                resolution: Some(SelectResolution::TypeclassMethod { member: DefId(7) }),
            },
        ],
    };

    assert_eq!(
        validate(&program),
        Err(ValidateError::UnresolvedTypeclassMethod {
            expr: ExprId(1),
            member: DefId(7),
        })
    );
}

#[test]
fn validation_rejects_unresolved_type_variables_in_boundaries() {
    let program = Program {
        roots: vec![Root::Expr(ExprId(1))],
        instances: Vec::new(),
        exprs: vec![
            Expr::Lit(mono::Lit::Int(1)),
            Expr::Coerce {
                source: Type::OpenVar(0),
                target: Type::Any,
                expr: ExprId(0),
            },
        ],
    };

    assert_eq!(
        validate(&program),
        Err(ValidateError::NonVmReadyType {
            feature: "unresolved type variable".to_string(),
            ty: Type::OpenVar(0),
        })
    );
}

#[test]
fn value_boundary_supports_record_field_functions_that_differ_only_by_effect_shape() {
    let source = record_with_update_effect(effect_row(&["source", "effect"]));
    let target = record_with_update_effect(effect_row(&["target", "effect"]));

    assert!(value_boundary_supported(&source, &target));
    assert!(value_boundary_supported(&target, &source));
}

#[test]
fn validator_accepts_ref_constructor_adapter_with_projected_update_effect() {
    let outer = effect_row(&["outer", "list"]);
    let update = ref_update_effect(int_type());
    let source_record = record_with_ref_fields(
        outer.clone(),
        Type::EffectRow(vec![update.clone(), outer.clone()]),
    );
    let target_record = record_with_ref_fields(outer.clone(), Type::EffectRow(vec![update]));
    let ref_type = Type::Con {
        path: vec![
            "std".to_string(),
            "control".to_string(),
            "var".to_string(),
            "ref".to_string(),
        ],
        args: vec![outer, int_type()],
    };
    let source = pure_function_type(source_record, ref_type.clone());
    let target = pure_function_type(target_record, ref_type);
    let program = Program {
        roots: vec![Root::Expr(ExprId(1))],
        instances: Vec::new(),
        exprs: vec![
            Expr::Lit(mono::Lit::Unit),
            Expr::FunctionAdapter {
                source,
                target,
                function: ExprId(0),
                hygiene: mono::FunctionAdapterHygiene::default(),
            },
        ],
    };

    assert_eq!(validate(&program), Ok(()));
}

fn lower_source(source: &str) -> infer::lowering::BodyLowering {
    let files = sources::load(vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }]);
    let output = infer::dump::dump_loaded_files(&files).unwrap();
    assert!(
        output.lowering.errors.is_empty(),
        "body lowering errors: {:?}",
        output.lowering.errors
    );
    output.lowering
}

fn record_with_update_effect(effect: Type) -> Type {
    Type::Record(vec![mono::TypeField {
        name: "update_effect".to_string(),
        value: pure_function_type(unit_type(), thunk_type(effect, unit_type())),
        optional: false,
    }])
}

fn record_with_ref_fields(get_effect: Type, update_effect: Type) -> Type {
    Type::Record(vec![
        mono::TypeField {
            name: "get".to_string(),
            value: pure_function_type(unit_type(), thunk_type(get_effect, int_type())),
            optional: false,
        },
        mono::TypeField {
            name: "update_effect".to_string(),
            value: pure_function_type(unit_type(), thunk_type(update_effect, unit_type())),
            optional: false,
        },
    ])
}

fn pure_function_type(arg: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(arg),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(Type::pure_effect()),
        ret: Box::new(ret),
    }
}

fn thunk_type(effect: Type, value: Type) -> Type {
    Type::Thunk {
        effect: Box::new(effect),
        value: Box::new(value),
    }
}

fn unit_type() -> Type {
    Type::unit()
}

fn int_type() -> Type {
    Type::Con {
        path: vec!["int".to_string()],
        args: Vec::new(),
    }
}

fn ref_update_effect(value: Type) -> Type {
    Type::Con {
        path: vec![
            "std".to_string(),
            "control".to_string(),
            "var".to_string(),
            "ref_update".to_string(),
        ],
        args: vec![value],
    }
}

fn effect_row(parts: &[&str]) -> Type {
    Type::EffectRow(vec![Type::Con {
        path: parts.iter().map(|part| part.to_string()).collect(),
        args: Vec::new(),
    }])
}

fn assert_oracle_parity(source: &str, expected: &str) {
    let lowering = lower_source(source);
    let program = specialize::specialize(&lowering.session.poly).unwrap();
    let oracle_values = mono_runtime::run_program(&program).unwrap();
    let control_values = run_mono_program(&program).unwrap();
    let oracle = format_oracle_values(&oracle_values);
    let control = format_values(&control_values);

    assert_eq!(oracle, expected, "{}", mono::dump::dump_program(&program));
    assert_eq!(control, expected, "{}", mono::dump::dump_program(&program));
    assert_eq!(control, oracle, "{}", mono::dump::dump_program(&program));
}

fn force_effect_call(path: Vec<String>, payload: mono::Expr) -> mono::Expr {
    let effect = Type::EffectRow(vec![Type::Con {
        path: path.clone(),
        args: Vec::new(),
    }]);
    mono::Expr::new(mono::ExprKind::ForceThunk {
        source: mono::EffectiveThunkType {
            effect: effect.clone(),
            value: Type::Any,
        },
        target: mono::ComputationType {
            effect,
            value: Type::Any,
        },
        thunk: Box::new(mono::Expr::new(mono::ExprKind::Apply(
            Box::new(mono::Expr::new(mono::ExprKind::EffectOp { path })),
            Box::new(payload),
        ))),
    })
}

fn format_oracle_values(values: &[mono_runtime::Value]) -> String {
    let mut out = String::new();
    out.push('[');
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_oracle_value(value));
    }
    out.push(']');
    out
}

fn format_oracle_value(value: &mono_runtime::Value) -> String {
    match value {
        mono_runtime::Value::Int(value) => value.to_string(),
        mono_runtime::Value::BigInt(value) => value.to_string(),
        mono_runtime::Value::Float(value) => value.to_string(),
        mono_runtime::Value::Str(value) => format!("{value:?}"),
        mono_runtime::Value::Bool(value) => value.to_string(),
        mono_runtime::Value::Unit => "()".to_string(),
        mono_runtime::Value::Tuple(values) => format_oracle_delimited_values("(", ")", values),
        mono_runtime::Value::List(values) => {
            let mut out = String::new();
            out.push('[');
            for index in 0..values.len() {
                if index > 0 {
                    out.push_str(", ");
                }
                let value = values.index(index).unwrap();
                out.push_str(&format_oracle_value(value.as_ref()));
            }
            out.push(']');
            out
        }
        mono_runtime::Value::Record(fields) => {
            let mut out = String::new();
            out.push('{');
            for (index, field) in fields.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                out.push_str(&field.name);
                out.push_str(": ");
                out.push_str(&format_oracle_value(&field.value));
            }
            out.push('}');
            out
        }
        mono_runtime::Value::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                return tag.clone();
            }
            format!(
                "{tag}{}",
                format_oracle_delimited_values("(", ")", payloads)
            )
        }
        mono_runtime::Value::DataConstructor { def, payloads } => {
            if payloads.is_empty() {
                return format!("<ctor d{}>", def.0);
            }
            format!(
                "<ctor d{}>{}",
                def.0,
                format_oracle_delimited_values("(", ")", payloads)
            )
        }
        mono_runtime::Value::ConstructorFunction(constructor) => {
            format!(
                "<ctor-fn d{} {}/{}>",
                constructor.def.0,
                constructor.args.len(),
                constructor.arity
            )
        }
        mono_runtime::Value::PrimitiveOp(primitive) => {
            format!(
                "<prim {:?} {}/{}>",
                primitive.op,
                primitive.args.len(),
                primitive.op.arity()
            )
        }
        mono_runtime::Value::Closure(_) | mono_runtime::Value::RecursiveClosure { .. } => {
            "<closure>".to_string()
        }
        mono_runtime::Value::Thunk(_) => "<thunk>".to_string(),
        mono_runtime::Value::FunctionAdapter(_) => "<function-adapter>".to_string(),
        mono_runtime::Value::EffectOp { path } => format!("<effect-op {}>", path.join("::")),
        mono_runtime::Value::Continuation(id) => format!("<continuation {}>", id.0),
        mono_runtime::Value::Marked { value, .. } => format_oracle_value(value),
    }
}

fn format_oracle_delimited_values(
    open: &str,
    close: &str,
    values: &[mono_runtime::Value],
) -> String {
    let mut out = String::new();
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_oracle_value(value));
    }
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}
