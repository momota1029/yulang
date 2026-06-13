use super::{Root, RuntimeError, Value, lower, run_mono_program, run_program};

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
    let lowering = lower_source("my id x = x\nid(1)\n");
    let program = specialize::specialize(&lowering.session.poly).unwrap();

    assert_eq!(
        run_mono_program(&program),
        Ok(vec![Value::Int(1)]),
        "{}",
        mono::dump::dump_program(&program)
    );
    assert_eq!(
        mono_runtime::run_program(&program).unwrap()[0],
        mono_runtime::Value::Int(1)
    );
}

#[test]
fn runs_stack_handler_hygiene_to_outer_handler() {
    let lowering = lower_source(
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
    );
    let program = specialize::specialize(&lowering.session.poly).unwrap();

    assert_eq!(
        run_mono_program(&program),
        Ok(vec![Value::Int(0)]),
        "{}",
        mono::dump::dump_program(&program)
    );
    assert_eq!(
        mono_runtime::run_program(&program).unwrap()[0],
        mono_runtime::Value::Int(0)
    );
}

#[test]
fn reports_unhandled_effect() {
    let program = mono::Program {
        roots: vec![mono::Root::Expr(mono::Expr::new(mono::ExprKind::Apply(
            Box::new(mono::Expr::new(mono::ExprKind::EffectOp {
                path: vec!["out".to_string(), "say".to_string()],
            })),
            Box::new(mono::Expr::new(mono::ExprKind::Lit(mono::Lit::Unit))),
        )))],
        instances: Vec::new(),
    };

    assert_eq!(
        run_mono_program(&program),
        Err(super::RunError::Runtime(RuntimeError::UnhandledEffect {
            path: vec!["out".to_string(), "say".to_string()]
        }))
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
