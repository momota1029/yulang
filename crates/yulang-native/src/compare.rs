use std::fmt;

use yulang_infer as infer;
use yulang_runtime as runtime;

use crate::abi::lower_closure_module_to_abi;
use crate::closure::closure_convert_module;
use crate::cranelift::{NativeCraneliftError, compile_abi_module};
use crate::eval::{NativeEvalError, eval_module};
use crate::lower::{NativeLowerError, lower_module};
use crate::source::{NativeSourceError, runtime_module_from_source_with_options};

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

#[derive(Debug)]
pub enum NativeSourceCompareError {
    Source(NativeSourceError),
    Lower(NativeLowerError),
    Eval(NativeEvalError),
    Vm(runtime::VmError),
    Cranelift(NativeCraneliftError),
    ResidualRequest {
        index: usize,
        request: runtime::VmRequest,
    },
    RootCountMismatch {
        vm: usize,
        native: usize,
        cranelift: usize,
    },
    UnsupportedVmScalar {
        index: usize,
        value: runtime::VmValue,
    },
    UnsupportedNativeScalar {
        index: usize,
        value: runtime::VmValue,
    },
    NativeMismatch {
        index: usize,
        vm: i64,
        native: i64,
    },
    CraneliftMismatch {
        index: usize,
        vm: i64,
        cranelift: i64,
    },
}

impl fmt::Display for NativeSourceCompareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeSourceCompareError::Source(error) => write!(f, "{error}"),
            NativeSourceCompareError::Lower(error) => write!(f, "{error}"),
            NativeSourceCompareError::Eval(error) => write!(f, "{error}"),
            NativeSourceCompareError::Vm(error) => write!(f, "{error}"),
            NativeSourceCompareError::Cranelift(error) => write!(f, "{error}"),
            NativeSourceCompareError::ResidualRequest { index, request } => write!(
                f,
                "VM root {index} produced a host/effect request instead of a value: {request:?}"
            ),
            NativeSourceCompareError::RootCountMismatch {
                vm,
                native,
                cranelift,
            } => write!(
                f,
                "root count mismatch: VM {vm}, native control {native}, Cranelift {cranelift}"
            ),
            NativeSourceCompareError::UnsupportedVmScalar { index, value } => write!(
                f,
                "VM root {index} produced non-scalar prototype value {value:?}"
            ),
            NativeSourceCompareError::UnsupportedNativeScalar { index, value } => write!(
                f,
                "native control root {index} produced non-scalar prototype value {value:?}"
            ),
            NativeSourceCompareError::NativeMismatch { index, vm, native } => write!(
                f,
                "native control root {index} mismatch: VM scalar {vm}, native scalar {native}"
            ),
            NativeSourceCompareError::CraneliftMismatch {
                index,
                vm,
                cranelift,
            } => write!(
                f,
                "Cranelift root {index} mismatch: VM scalar {vm}, Cranelift scalar {cranelift}"
            ),
        }
    }
}

impl std::error::Error for NativeSourceCompareError {}

impl From<NativeSourceError> for NativeSourceCompareError {
    fn from(error: NativeSourceError) -> Self {
        NativeSourceCompareError::Source(error)
    }
}

impl From<NativeLowerError> for NativeSourceCompareError {
    fn from(error: NativeLowerError) -> Self {
        NativeSourceCompareError::Lower(error)
    }
}

impl From<NativeEvalError> for NativeSourceCompareError {
    fn from(error: NativeEvalError) -> Self {
        NativeSourceCompareError::Eval(error)
    }
}

impl From<runtime::VmError> for NativeSourceCompareError {
    fn from(error: runtime::VmError) -> Self {
        NativeSourceCompareError::Vm(error)
    }
}

impl From<NativeCraneliftError> for NativeSourceCompareError {
    fn from(error: NativeCraneliftError) -> Self {
        NativeSourceCompareError::Cranelift(error)
    }
}

pub fn compare_source_i64(source: &str) -> Result<(), NativeSourceCompareError> {
    compare_source_i64_with_options(source, infer::SourceOptions::default())
}

pub fn compare_source_i64_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> Result<(), NativeSourceCompareError> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    let native_module = lower_module(&runtime_module)?;
    let native_values = eval_module(&native_module)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    let mut jit = compile_abi_module(&abi_module)?;
    let cranelift_values = jit.run_roots_i64()?;

    let vm_results = runtime::compile_vm_module(runtime_module)?.eval_roots()?;
    if vm_results.len() != native_values.len() || vm_results.len() != cranelift_values.len() {
        return Err(NativeSourceCompareError::RootCountMismatch {
            vm: vm_results.len(),
            native: native_values.len(),
            cranelift: cranelift_values.len(),
        });
    }

    for (index, ((vm_result, native_value), cranelift_value)) in vm_results
        .into_iter()
        .zip(native_values)
        .zip(cranelift_values)
        .enumerate()
    {
        let vm_value = match vm_result {
            runtime::VmResult::Value(value) => value,
            runtime::VmResult::Request(request) => {
                return Err(NativeSourceCompareError::ResidualRequest { index, request });
            }
        };
        let vm_scalar =
            scalar_i64(vm_value.clone()).ok_or(NativeSourceCompareError::UnsupportedVmScalar {
                index,
                value: vm_value,
            })?;
        let native_scalar = scalar_i64(native_value.clone()).ok_or(
            NativeSourceCompareError::UnsupportedNativeScalar {
                index,
                value: native_value,
            },
        )?;
        if vm_scalar != native_scalar {
            return Err(NativeSourceCompareError::NativeMismatch {
                index,
                vm: vm_scalar,
                native: native_scalar,
            });
        }
        if vm_scalar != cranelift_value {
            return Err(NativeSourceCompareError::CraneliftMismatch {
                index,
                vm: vm_scalar,
                cranelift: cranelift_value,
            });
        }
    }
    Ok(())
}

fn scalar_i64(value: runtime::VmValue) -> Option<i64> {
    match value {
        runtime::VmValue::Int(value) => value.parse().ok(),
        runtime::VmValue::Bool(value) => Some(i64::from(value)),
        runtime::VmValue::Unit => Some(0),
        _ => None,
    }
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

    #[test]
    fn compares_source_int_literal_with_vm_native_and_cranelift() {
        compare_source_i64("41").expect("source scalar paths match");
    }

    #[test]
    fn compares_source_bool_literal_with_vm_native_and_cranelift() {
        compare_source_i64("true").expect("source scalar paths match");
    }

    #[test]
    fn compares_source_simple_function_call_with_vm_native_and_cranelift() {
        compare_source_i64("my id x = x\nid 41").expect("source scalar paths match");
    }
}
