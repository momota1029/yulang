use std::fmt;

use yulang_runtime as runtime;

use crate::cps_eval::{CpsEvalError, eval_cps_module};
use crate::cps_lower::{CpsLowerError, lower_cps_module};
use crate::cps_repr_cranelift::{CpsReprCraneliftError, compile_runtime_module_to_cps_repr_jit};
use crate::cps_validate::{CpsValidateError, validate_cps_module};

#[derive(Debug, Clone, PartialEq)]
pub enum CpsCompareError {
    Lower(CpsLowerError),
    Validate(CpsValidateError),
    Eval(CpsEvalError),
    Cranelift(CpsReprCraneliftError),
    Vm(runtime::VmError),
    ResidualRequest {
        index: usize,
        request: runtime::VmRequest,
    },
    RootCountMismatch {
        vm: usize,
        cps: usize,
    },
    ValueMismatch {
        index: usize,
        vm: runtime::VmValue,
        cps: runtime::VmValue,
    },
    I64Mismatch {
        index: usize,
        vm: i64,
        cps_cranelift: i64,
    },
    NonI64Value {
        index: usize,
        value: runtime::VmValue,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprI64CompareReport {
    pub roots: Vec<CpsReprI64RootCompare>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprI64RootCompare {
    pub index: usize,
    pub vm: i64,
    pub cps_cranelift: i64,
}

impl fmt::Display for CpsCompareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CpsCompareError::Lower(error) => write!(f, "{error}"),
            CpsCompareError::Validate(error) => write!(f, "{error}"),
            CpsCompareError::Eval(error) => write!(f, "{error}"),
            CpsCompareError::Cranelift(error) => write!(f, "{error}"),
            CpsCompareError::Vm(error) => write!(f, "{error}"),
            CpsCompareError::ResidualRequest { index, request } => write!(
                f,
                "VM root {index} produced a host/effect request instead of a value: {request:?}"
            ),
            CpsCompareError::RootCountMismatch { vm, cps } => {
                write!(f, "VM produced {vm} roots but CPS produced {cps}")
            }
            CpsCompareError::ValueMismatch { index, vm, cps } => {
                write!(f, "CPS root {index} mismatch: VM {vm:?}, CPS {cps:?}")
            }
            CpsCompareError::I64Mismatch {
                index,
                vm,
                cps_cranelift,
            } => write!(
                f,
                "CPS repr Cranelift root {index} mismatch: VM {vm}, Cranelift {cps_cranelift}"
            ),
            CpsCompareError::NonI64Value { index, value } => {
                write!(f, "VM root {index} produced non-i64 value {value:?}")
            }
        }
    }
}

impl std::error::Error for CpsCompareError {}

impl From<CpsLowerError> for CpsCompareError {
    fn from(value: CpsLowerError) -> Self {
        Self::Lower(value)
    }
}

impl From<CpsValidateError> for CpsCompareError {
    fn from(value: CpsValidateError) -> Self {
        Self::Validate(value)
    }
}

impl From<CpsEvalError> for CpsCompareError {
    fn from(value: CpsEvalError) -> Self {
        Self::Eval(value)
    }
}

impl From<CpsReprCraneliftError> for CpsCompareError {
    fn from(value: CpsReprCraneliftError) -> Self {
        Self::Cranelift(value)
    }
}

impl From<runtime::VmError> for CpsCompareError {
    fn from(value: runtime::VmError) -> Self {
        Self::Vm(value)
    }
}

pub fn compare_cps_module(module: &runtime::Module) -> Result<(), CpsCompareError> {
    let cps_module = lower_cps_module(module)?;
    validate_cps_module(&cps_module)?;
    let cps_values = eval_cps_module(&cps_module)?;
    let vm_results = runtime::compile_vm_module(module.clone())?.eval_roots()?;
    if vm_results.len() != cps_values.len() {
        return Err(CpsCompareError::RootCountMismatch {
            vm: vm_results.len(),
            cps: cps_values.len(),
        });
    }
    for (index, (vm_result, cps)) in vm_results.into_iter().zip(cps_values).enumerate() {
        let vm = match vm_result {
            runtime::VmResult::Value(value) => value,
            runtime::VmResult::Request(request) => {
                return Err(CpsCompareError::ResidualRequest { index, request });
            }
        };
        if vm != cps {
            return Err(CpsCompareError::ValueMismatch { index, vm, cps });
        }
    }
    Ok(())
}

pub fn compare_cps_repr_cranelift_i64(module: &runtime::Module) -> Result<(), CpsCompareError> {
    compare_cps_repr_cranelift_i64_report(module).map(|_| ())
}

pub fn compare_cps_repr_cranelift_i64_report(
    module: &runtime::Module,
) -> Result<CpsReprI64CompareReport, CpsCompareError> {
    let mut jit = compile_runtime_module_to_cps_repr_jit(module)?;
    let cps_values = jit.run_roots_i64()?;
    let vm_results = runtime::compile_vm_module(module.clone())?.eval_roots()?;
    if vm_results.len() != cps_values.len() {
        return Err(CpsCompareError::RootCountMismatch {
            vm: vm_results.len(),
            cps: cps_values.len(),
        });
    }
    let mut roots = Vec::with_capacity(vm_results.len());
    for (index, (vm_result, cps_cranelift)) in vm_results.into_iter().zip(cps_values).enumerate() {
        let value = match vm_result {
            runtime::VmResult::Value(value) => value,
            runtime::VmResult::Request(request) => {
                return Err(CpsCompareError::ResidualRequest { index, request });
            }
        };
        let vm = match value {
            runtime::VmValue::Int(value) => {
                value
                    .parse::<i64>()
                    .map_err(|_| CpsCompareError::NonI64Value {
                        index,
                        value: runtime::VmValue::Int(value),
                    })?
            }
            runtime::VmValue::Bool(value) => i64::from(value),
            value => return Err(CpsCompareError::NonI64Value { index, value }),
        };
        if vm != cps_cranelift {
            return Err(CpsCompareError::I64Mismatch {
                index,
                vm,
                cps_cranelift,
            });
        }
        roots.push(CpsReprI64RootCompare {
            index,
            vm,
            cps_cranelift,
        });
    }
    Ok(CpsReprI64CompareReport { roots })
}

#[cfg(test)]
mod tests {
    use yulang_typed_ir as typed_ir;

    use crate::compare::compare_module;

    use super::*;

    fn unknown_lit(lit: typed_ir::Lit) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::Lit(lit), runtime::Type::unknown())
    }

    fn primitive(op: typed_ir::PrimitiveOp) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::PrimitiveOp(op), runtime::Type::unknown())
    }

    fn apply(callee: runtime::Expr, arg: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            runtime::Type::unknown(),
        )
    }

    fn if_expr(
        cond: runtime::Expr,
        then_branch: runtime::Expr,
        else_branch: runtime::Expr,
    ) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
                evidence: None,
            },
            runtime::Type::unknown(),
        )
    }

    fn var(name: &str) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Var(typed_ir::Path::from_name(typed_ir::Name(name.to_string()))),
            runtime::Type::unknown(),
        )
    }

    fn effect_op(name: &str) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::EffectOp(effect_operation_path(name)),
            runtime::Type::unknown(),
        )
    }

    fn effect_operation_path(name: &str) -> typed_ir::Path {
        typed_ir::Path {
            segments: vec![
                typed_ir::Name(name.to_string()),
                typed_ir::Name(name.to_string()),
            ],
        }
    }

    fn bind_pattern(name: &str) -> runtime::Pattern {
        runtime::Pattern::Bind {
            name: typed_ir::Name(name.to_string()),
            ty: runtime::Type::unknown(),
        }
    }

    fn handle_once(
        effect: &str,
        payload: &str,
        resume: &str,
        body: runtime::Expr,
        arm_body: runtime::Expr,
    ) -> runtime::Expr {
        let effect_namespace = typed_ir::Path::from_name(typed_ir::Name(effect.to_string()));
        let effect_operation = effect_operation_path(effect);
        runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(body),
                arms: vec![runtime::HandleArm {
                    effect: effect_operation,
                    payload: bind_pattern(payload),
                    resume: Some(runtime::ResumeBinding {
                        name: typed_ir::Name(resume.to_string()),
                        ty: runtime::Type::unknown(),
                    }),
                    guard: None,
                    body: arm_body,
                }],
                evidence: runtime::JoinEvidence {
                    result: typed_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: vec![effect_namespace],
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        )
    }

    fn block(stmts: Vec<runtime::Stmt>, tail: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Block {
                stmts,
                tail: Some(Box::new(tail)),
            },
            runtime::Type::unknown(),
        )
    }

    fn thunk(expr: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Thunk {
                effect: typed_ir::Type::Unknown,
                value: runtime::Type::unknown(),
                expr: Box::new(expr),
            },
            runtime::Type::thunk(typed_ir::Type::Unknown, runtime::Type::unknown()),
        )
    }

    fn handled_body(expr: runtime::Expr) -> runtime::Expr {
        thunk(expr)
    }

    fn lambda(param: &str, body: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Lambda {
                param: typed_ir::Name(param.to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(body),
            },
            runtime::Type::unknown(),
        )
    }

    fn binding(name: &str, body: runtime::Expr) -> runtime::Binding {
        runtime::Binding {
            name: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Unknown,
            },
            body,
        }
    }

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        module_with_bindings_and_root(Vec::new(), expr)
    }

    fn module_with_bindings_and_root(
        bindings: Vec<runtime::Binding>,
        expr: runtime::Expr,
    ) -> runtime::Module {
        runtime::Module {
            path: typed_ir::Path::default(),
            bindings,
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    fn primitive_call(op: typed_ir::PrimitiveOp, args: Vec<runtime::Expr>) -> runtime::Expr {
        args.into_iter()
            .fold(primitive(op), |callee, arg| apply(callee, arg))
    }

    fn list_expr(items: Vec<i64>) -> runtime::Expr {
        list_of_exprs(
            items
                .into_iter()
                .map(|item| unknown_lit(typed_ir::Lit::Int(item.to_string())))
                .collect(),
        )
    }

    fn list_of_exprs(items: Vec<runtime::Expr>) -> runtime::Expr {
        items
            .into_iter()
            .map(|item| primitive_call(typed_ir::PrimitiveOp::ListSingleton, vec![item]))
            .fold(
                primitive_call(
                    typed_ir::PrimitiveOp::ListEmpty,
                    vec![unknown_lit(typed_ir::Lit::Unit)],
                ),
                |acc, item| primitive_call(typed_ir::PrimitiveOp::ListMerge, vec![acc, item]),
            )
    }

    fn record(fields: Vec<(&str, runtime::Expr)>) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|(name, value)| runtime::RecordExprField {
                        name: typed_ir::Name(name.to_string()),
                        value,
                    })
                    .collect(),
                spread: None,
            },
            runtime::Type::unknown(),
        )
    }

    fn variant(tag: &str, value: Option<runtime::Expr>) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Variant {
                tag: typed_ir::Name(tag.to_string()),
                value: value.map(Box::new),
            },
            runtime::Type::unknown(),
        )
    }

    fn compare_all(module: &runtime::Module) {
        compare_module(module).expect("native control matches VM");
        compare_cps_module(module).expect("CPS matches VM");
    }

    fn compare_cps_cranelift_i64(module: &runtime::Module) {
        compare_cps_repr_cranelift_i64(module).expect("CPS repr Cranelift matches VM");
    }

    fn cps_cranelift_display_roots(module: &runtime::Module) -> Vec<String> {
        let mut jit =
            compile_runtime_module_to_cps_repr_jit(module).expect("compiled CPS repr Cranelift");
        jit.run_roots_display().expect("ran CPS repr Cranelift")
    }

    #[test]
    fn compares_pure_int_add_with_vm_and_native_control() {
        let expr = apply(
            apply(
                primitive(typed_ir::PrimitiveOp::IntAdd),
                unknown_lit(typed_ir::Lit::Int("20".to_string())),
            ),
            unknown_lit(typed_ir::Lit::Int("22".to_string())),
        );
        compare_all(&module_with_root(expr));
    }

    #[test]
    fn compares_pure_int_add_with_cps_repr_cranelift() {
        let expr = apply(
            apply(
                primitive(typed_ir::PrimitiveOp::IntAdd),
                unknown_lit(typed_ir::Lit::Int("20".to_string())),
            ),
            unknown_lit(typed_ir::Lit::Int("22".to_string())),
        );
        compare_cps_cranelift_i64(&module_with_root(expr));
    }

    #[test]
    fn compares_effect_handler_with_cps_repr_cranelift() {
        let body = apply(
            effect_op("choose"),
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
        );
        let arm_body = apply(var("k"), var("x"));

        compare_cps_cranelift_i64(&module_with_root(handle_once(
            "choose",
            "x",
            "k",
            handled_body(body),
            arm_body,
        )));
    }

    #[test]
    fn compares_multishot_effect_handler_with_cps_repr_cranelift() {
        let body = apply(
            effect_op("choose"),
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );

        compare_cps_cranelift_i64(&module_with_root(handle_once(
            "choose",
            "x",
            "k",
            handled_body(body),
            arm_body,
        )));
    }

    #[test]
    fn compares_effect_handler_rest_continuation_with_cps_repr_cranelift() {
        let choose_one = apply(
            effect_op("choose"),
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
        );
        let body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), choose_one),
            unknown_lit(typed_ir::Lit::Int("10".to_string())),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );

        compare_cps_cranelift_i64(&module_with_root(handle_once(
            "choose",
            "x",
            "k",
            handled_body(body),
            arm_body,
        )));
    }

    #[test]
    fn compares_effect_handler_branch_with_cps_repr_cranelift() {
        let then_branch = apply(
            apply(
                primitive(typed_ir::PrimitiveOp::IntAdd),
                apply(
                    effect_op("choose"),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
            ),
            unknown_lit(typed_ir::Lit::Int("10".to_string())),
        );
        let else_branch = apply(
            apply(
                primitive(typed_ir::PrimitiveOp::IntAdd),
                apply(
                    effect_op("choose"),
                    unknown_lit(typed_ir::Lit::Int("2".to_string())),
                ),
            ),
            unknown_lit(typed_ir::Lit::Int("20".to_string())),
        );
        let body = if_expr(
            unknown_lit(typed_ir::Lit::Bool(true)),
            then_branch,
            else_branch,
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_three = apply(var("k"), unknown_lit(typed_ir::Lit::Int("3".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_three,
        );

        compare_cps_cranelift_i64(&module_with_root(handle_once(
            "choose",
            "x",
            "k",
            handled_body(body),
            arm_body,
        )));
    }

    #[test]
    fn compares_non_scalar_effect_payloads_with_cps_repr_cranelift() {
        let cases = vec![
            (
                unknown_lit(typed_ir::Lit::String("ok".to_string())),
                "ok".to_string(),
            ),
            (list_expr(vec![1, 2, 3]), "[1, 2, 3]".to_string()),
            (
                record(vec![(
                    "answer",
                    unknown_lit(typed_ir::Lit::Int("42".to_string())),
                )]),
                "{ answer: 42 }".to_string(),
            ),
            (
                variant(
                    "just",
                    Some(unknown_lit(typed_ir::Lit::Int("7".to_string()))),
                ),
                ":just 7".to_string(),
            ),
        ];

        for (payload, expected) in cases {
            let body = apply(effect_op("choose"), payload);
            let arm_body = apply(var("k"), var("x"));
            let module = module_with_root(handle_once(
                "choose",
                "x",
                "k",
                handled_body(body),
                arm_body,
            ));

            compare_cps_module(&module).expect("CPS matches VM");
            assert_eq!(cps_cranelift_display_roots(&module), vec![expected]);
        }
    }

    #[test]
    fn carries_runtime_values_through_cps_repr_control_edges() {
        let branch = module_with_root(if_expr(
            unknown_lit(typed_ir::Lit::Bool(true)),
            list_expr(vec![1, 2]),
            list_expr(vec![3]),
        ));
        compare_cps_module(&branch).expect("branch CPS matches VM");
        assert_eq!(
            cps_cranelift_display_roots(&branch),
            vec!["[1, 2]".to_string()]
        );

        let direct_call = module_with_bindings_and_root(
            vec![binding("make", lambda("u", list_expr(vec![4, 5])))],
            apply(var("make"), unknown_lit(typed_ir::Lit::Unit)),
        );
        compare_cps_module(&direct_call).expect("direct call CPS matches VM");
        assert_eq!(
            cps_cranelift_display_roots(&direct_call),
            vec!["[4, 5]".to_string()]
        );

        let closure_apply = module_with_root(block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("f"),
                value: lambda("u", list_expr(vec![6, 7])),
            }],
            apply(var("f"), unknown_lit(typed_ir::Lit::Unit)),
        ));
        compare_cps_module(&closure_apply).expect("closure apply CPS matches VM");
        assert_eq!(
            cps_cranelift_display_roots(&closure_apply),
            vec!["[6, 7]".to_string()]
        );
    }

    #[test]
    fn carries_large_closure_environment_through_cps_repr() {
        let closure_apply = module_with_root(block(
            vec![
                runtime::Stmt::Let {
                    pattern: bind_pattern("a"),
                    value: unknown_lit(typed_ir::Lit::Int("1".to_string())),
                },
                runtime::Stmt::Let {
                    pattern: bind_pattern("b"),
                    value: unknown_lit(typed_ir::Lit::Int("2".to_string())),
                },
                runtime::Stmt::Let {
                    pattern: bind_pattern("c"),
                    value: unknown_lit(typed_ir::Lit::Int("3".to_string())),
                },
                runtime::Stmt::Let {
                    pattern: bind_pattern("d"),
                    value: unknown_lit(typed_ir::Lit::Int("4".to_string())),
                },
                runtime::Stmt::Let {
                    pattern: bind_pattern("e"),
                    value: unknown_lit(typed_ir::Lit::Int("5".to_string())),
                },
                runtime::Stmt::Let {
                    pattern: bind_pattern("f"),
                    value: lambda(
                        "u",
                        handle_once(
                            "choose",
                            "x",
                            "k",
                            handled_body(apply(
                                effect_op("choose"),
                                list_of_exprs(vec![
                                    var("a"),
                                    var("b"),
                                    var("c"),
                                    var("d"),
                                    var("e"),
                                ]),
                            )),
                            apply(var("k"), var("x")),
                        ),
                    ),
                },
            ],
            apply(var("f"), unknown_lit(typed_ir::Lit::Unit)),
        ));

        compare_cps_module(&closure_apply).expect("large closure env CPS matches VM");
        assert_eq!(
            cps_cranelift_display_roots(&closure_apply),
            vec!["[1, 2, 3, 4, 5]".to_string()]
        );
    }

    #[test]
    fn applies_partial_top_level_function_through_cps_repr() {
        let add = binding(
            "add",
            lambda(
                "x",
                lambda(
                    "y",
                    apply(
                        apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("x")),
                        var("y"),
                    ),
                ),
            ),
        );
        let root = apply(
            apply(var("add"), unknown_lit(typed_ir::Lit::Int("1".to_string()))),
            unknown_lit(typed_ir::Lit::Int("41".to_string())),
        );
        let module = module_with_bindings_and_root(vec![add], root);

        compare_cps_module(&module).expect("partial function CPS matches VM");
        assert_eq!(cps_cranelift_display_roots(&module), vec!["42".to_string()]);
    }

    #[test]
    fn compares_if_with_vm_and_native_control() {
        let expr = if_expr(
            apply(
                apply(
                    primitive(typed_ir::PrimitiveOp::IntLt),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
                unknown_lit(typed_ir::Lit::Int("2".to_string())),
            ),
            unknown_lit(typed_ir::Lit::String("then".to_string())),
            unknown_lit(typed_ir::Lit::String("else".to_string())),
        );
        compare_all(&module_with_root(expr));
    }

    #[test]
    fn compares_block_binding_with_vm_and_native_control() {
        let expr = block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("x"),
                value: unknown_lit(typed_ir::Lit::Int("21".to_string())),
            }],
            apply(
                apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("x")),
                var("x"),
            ),
        );
        compare_all(&module_with_root(expr));
    }

    #[test]
    fn compares_recursive_binding_with_vm_and_native_control() {
        let countdown = binding(
            "countdown",
            lambda(
                "n",
                if_expr(
                    apply(
                        apply(primitive(typed_ir::PrimitiveOp::IntLe), var("n")),
                        unknown_lit(typed_ir::Lit::Int("0".to_string())),
                    ),
                    unknown_lit(typed_ir::Lit::Int("0".to_string())),
                    apply(
                        var("countdown"),
                        apply(
                            apply(primitive(typed_ir::PrimitiveOp::IntSub), var("n")),
                            unknown_lit(typed_ir::Lit::Int("1".to_string())),
                        ),
                    ),
                ),
            ),
        );
        let root = apply(
            var("countdown"),
            unknown_lit(typed_ir::Lit::Int("3".to_string())),
        );
        compare_all(&module_with_bindings_and_root(vec![countdown], root));
    }
}
