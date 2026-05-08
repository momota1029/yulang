use std::fmt;

use yulang_runtime as runtime;

use crate::eval::{NativeEvalError, eval_module};
use crate::lower::{NativeLowerError, lower_module};

#[derive(Debug, Clone, PartialEq)]
pub enum NativeCompareError {
    Lower(NativeLowerError),
    Eval(NativeEvalError),
    Vm(runtime::VmError),
    ResidualRequest {
        index: usize,
        request: runtime::VmRequest,
    },
    RootCountMismatch {
        vm: usize,
        native: usize,
    },
    ValueMismatch {
        index: usize,
        vm: runtime::VmValue,
        native: runtime::VmValue,
    },
}

impl fmt::Display for NativeCompareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeCompareError::Lower(error) => write!(f, "{error}"),
            NativeCompareError::Eval(error) => write!(f, "{error}"),
            NativeCompareError::Vm(error) => write!(f, "{error}"),
            NativeCompareError::ResidualRequest { index, request } => write!(
                f,
                "VM root {index} produced a host/effect request instead of a value: {request:?}"
            ),
            NativeCompareError::RootCountMismatch { vm, native } => {
                write!(
                    f,
                    "VM produced {vm} roots but native control produced {native}"
                )
            }
            NativeCompareError::ValueMismatch { index, vm, native } => write!(
                f,
                "native control root {index} mismatch: VM {vm:?}, native {native:?}"
            ),
        }
    }
}

impl std::error::Error for NativeCompareError {}

impl From<NativeLowerError> for NativeCompareError {
    fn from(value: NativeLowerError) -> Self {
        Self::Lower(value)
    }
}

impl From<NativeEvalError> for NativeCompareError {
    fn from(value: NativeEvalError) -> Self {
        Self::Eval(value)
    }
}

impl From<runtime::VmError> for NativeCompareError {
    fn from(value: runtime::VmError) -> Self {
        Self::Vm(value)
    }
}

pub fn compare_module(module: &runtime::Module) -> Result<(), NativeCompareError> {
    let native_module = lower_module(module)?;
    let native_values = eval_module(&native_module)?;
    let vm_results = runtime::compile_vm_module(module.clone())?.eval_roots()?;
    if vm_results.len() != native_values.len() {
        return Err(NativeCompareError::RootCountMismatch {
            vm: vm_results.len(),
            native: native_values.len(),
        });
    }
    for (index, (vm_result, native)) in vm_results.into_iter().zip(native_values).enumerate() {
        let vm = match vm_result {
            runtime::VmResult::Value(value) => value,
            runtime::VmResult::Request(request) => {
                return Err(NativeCompareError::ResidualRequest { index, request });
            }
        };
        if vm != native {
            return Err(NativeCompareError::ValueMismatch { index, vm, native });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use yulang_core_ir as core_ir;

    use super::*;

    fn unknown_lit(lit: core_ir::Lit) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::Lit(lit), runtime::Type::unknown())
    }

    fn primitive(op: core_ir::PrimitiveOp) -> runtime::Expr {
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
            runtime::ExprKind::Var(core_ir::Path::from_name(core_ir::Name(name.to_string()))),
            runtime::Type::unknown(),
        )
    }

    fn bind_pattern(name: &str) -> runtime::Pattern {
        runtime::Pattern::Bind {
            name: core_ir::Name(name.to_string()),
            ty: runtime::Type::unknown(),
        }
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

    fn lambda(param: &str, body: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Lambda {
                param: core_ir::Name(param.to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(body),
            },
            runtime::Type::unknown(),
        )
    }

    fn binding(name: &str, body: runtime::Expr) -> runtime::Binding {
        runtime::Binding {
            name: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            type_params: Vec::new(),
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: core_ir::Type::Unknown,
            },
            body,
        }
    }

    fn module_with_binding_and_root(
        binding: runtime::Binding,
        expr: runtime::Expr,
    ) -> runtime::Module {
        module_with_bindings_and_root(vec![binding], expr)
    }

    fn module_with_bindings_and_root(
        bindings: Vec<runtime::Binding>,
        expr: runtime::Expr,
    ) -> runtime::Module {
        runtime::Module {
            path: core_ir::Path::default(),
            bindings,
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        runtime::Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    #[test]
    fn compares_pure_int_add_with_vm() {
        let expr = apply(
            apply(
                primitive(core_ir::PrimitiveOp::IntAdd),
                unknown_lit(core_ir::Lit::Int("20".to_string())),
            ),
            unknown_lit(core_ir::Lit::Int("22".to_string())),
        );
        let module = module_with_root(expr);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_if_with_vm() {
        let expr = if_expr(
            apply(
                apply(
                    primitive(core_ir::PrimitiveOp::IntLt),
                    unknown_lit(core_ir::Lit::Int("1".to_string())),
                ),
                unknown_lit(core_ir::Lit::Int("2".to_string())),
            ),
            unknown_lit(core_ir::Lit::String("then".to_string())),
            unknown_lit(core_ir::Lit::String("else".to_string())),
        );
        let module = module_with_root(expr);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_simple_block_binding_with_vm() {
        let expr = block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("x"),
                value: unknown_lit(core_ir::Lit::Int("21".to_string())),
            }],
            apply(
                apply(primitive(core_ir::PrimitiveOp::IntAdd), var("x")),
                var("x"),
            ),
        );
        let module = module_with_root(expr);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_direct_monomorphic_call_with_vm() {
        let inc = binding(
            "inc",
            lambda(
                "x",
                apply(
                    apply(primitive(core_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(core_ir::Lit::Int("1".to_string())),
                ),
            ),
        );
        let root = apply(var("inc"), unknown_lit(core_ir::Lit::Int("41".to_string())));
        let module = module_with_binding_and_root(inc, root);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_multiple_bindings_with_vm() {
        let inc = binding(
            "inc",
            lambda(
                "x",
                apply(
                    apply(primitive(core_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(core_ir::Lit::Int("1".to_string())),
                ),
            ),
        );
        let twice = binding(
            "twice",
            lambda("x", apply(var("inc"), apply(var("inc"), var("x")))),
        );
        let root = apply(
            var("twice"),
            unknown_lit(core_ir::Lit::Int("40".to_string())),
        );
        let module = module_with_bindings_and_root(vec![inc, twice], root);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_recursive_binding_with_vm() {
        let countdown = binding(
            "countdown",
            lambda(
                "n",
                if_expr(
                    apply(
                        apply(primitive(core_ir::PrimitiveOp::IntLe), var("n")),
                        unknown_lit(core_ir::Lit::Int("0".to_string())),
                    ),
                    unknown_lit(core_ir::Lit::Int("0".to_string())),
                    apply(
                        var("countdown"),
                        apply(
                            apply(primitive(core_ir::PrimitiveOp::IntSub), var("n")),
                            unknown_lit(core_ir::Lit::Int("1".to_string())),
                        ),
                    ),
                ),
            ),
        );
        let root = apply(
            var("countdown"),
            unknown_lit(core_ir::Lit::Int("3".to_string())),
        );
        let module = module_with_binding_and_root(countdown, root);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_immediate_lambda_call_with_vm() {
        let expr = apply(
            lambda(
                "x",
                apply(
                    apply(primitive(core_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(core_ir::Lit::Int("1".to_string())),
                ),
            ),
            unknown_lit(core_ir::Lit::Int("41".to_string())),
        );
        let module = module_with_root(expr);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_lambda_capture_with_vm() {
        let expr = block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("y"),
                value: unknown_lit(core_ir::Lit::Int("10".to_string())),
            }],
            apply(
                lambda(
                    "x",
                    apply(
                        apply(primitive(core_ir::PrimitiveOp::IntAdd), var("x")),
                        var("y"),
                    ),
                ),
                unknown_lit(core_ir::Lit::Int("32".to_string())),
            ),
        );
        let module = module_with_root(expr);

        compare_module(&module).expect("native control matches VM");
    }
}
