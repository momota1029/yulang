use mono::Type;

use super::{
    DefId, Expr, ExprId, Program, Root, RuntimeError, SelectResolution, ValidateError, Value,
    format_values, lower, run_mono_program, run_program, validate,
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
fn runs_specialized_generic_call_like_oracle() {
    assert_oracle_parity("my id x = x\nid(1)\n", "[1]");
}

#[test]
fn runs_apply_colon_block_argument_like_oracle() {
    assert_oracle_parity("my id x = x\nid:\n  my x = 1\n  x\n", "[1]");
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
        mono_runtime::Value::Closure(_) => "<closure>".to_string(),
        mono_runtime::Value::Thunk(_) => "<thunk>".to_string(),
        mono_runtime::Value::FunctionAdapter(_) => "<function-adapter>".to_string(),
        mono_runtime::Value::EffectOp { path } => format!("<effect-op {}>", path.join("::")),
        mono_runtime::Value::Continuation(id) => format!("<continuation {}>", id.0),
        mono_runtime::Value::Marked { value, markers } => {
            let mut out = format_oracle_value(value);
            out.push_str(" @ [");
            for (index, marker) in markers.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                out.push_str(&marker.path.join("::"));
                out.push('#');
                out.push_str(&marker.id.0.to_string());
                out.push(':');
                out.push_str(&marker.depth.to_string());
            }
            out.push(']');
            out
        }
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
