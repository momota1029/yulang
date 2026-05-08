use std::fmt;

use yulang_runtime as runtime;

use crate::cps_eval::{CpsEvalError, eval_cps_module};
use crate::cps_lower::{CpsLowerError, lower_cps_module};
use crate::cps_validate::{CpsValidateError, validate_cps_module};

#[derive(Debug, Clone, PartialEq)]
pub enum CpsCompareError {
    Lower(CpsLowerError),
    Validate(CpsValidateError),
    Eval(CpsEvalError),
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
}

impl fmt::Display for CpsCompareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CpsCompareError::Lower(error) => write!(f, "{error}"),
            CpsCompareError::Validate(error) => write!(f, "{error}"),
            CpsCompareError::Eval(error) => write!(f, "{error}"),
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

#[cfg(test)]
mod tests {
    use yulang_core_ir as core_ir;

    use crate::compare::compare_module;

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

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        module_with_bindings_and_root(Vec::new(), expr)
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

    fn compare_all(module: &runtime::Module) {
        compare_module(module).expect("native control matches VM");
        compare_cps_module(module).expect("CPS matches VM");
    }

    #[test]
    fn compares_pure_int_add_with_vm_and_native_control() {
        let expr = apply(
            apply(
                primitive(core_ir::PrimitiveOp::IntAdd),
                unknown_lit(core_ir::Lit::Int("20".to_string())),
            ),
            unknown_lit(core_ir::Lit::Int("22".to_string())),
        );
        compare_all(&module_with_root(expr));
    }

    #[test]
    fn compares_if_with_vm_and_native_control() {
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
        compare_all(&module_with_root(expr));
    }

    #[test]
    fn compares_block_binding_with_vm_and_native_control() {
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
        compare_all(&module_with_bindings_and_root(vec![countdown], root));
    }
}
