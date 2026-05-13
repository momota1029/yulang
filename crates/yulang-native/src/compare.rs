use std::fmt;

use yulang_runtime as runtime;

use crate::abi::lower_closure_module_to_abi;
use crate::abi_eval::{NativeAbiEvalError, eval_abi_module};
use crate::closure::closure_convert_module;
use crate::cranelift::{NativeCraneliftError, compile_abi_module};
use crate::eval::{NativeEvalError, eval_module};
use crate::lower::{NativeLowerError, lower_module};
use crate::value_cranelift::{NativeValueCraneliftError, compile_value_abi_module};

#[derive(Debug, Clone, PartialEq)]
pub enum NativeCompareError {
    Lower(NativeLowerError),
    Eval(NativeEvalError),
    Abi(NativeAbiEvalError),
    Vm(runtime::VmError),
    ResidualRequest {
        index: usize,
        request: runtime::VmRequest,
    },
    RootCountMismatch {
        vm: usize,
        native: usize,
        abi: usize,
    },
    ValueMismatch {
        index: usize,
        vm: runtime::VmValue,
        native: runtime::VmValue,
    },
    AbiValueMismatch {
        index: usize,
        vm: runtime::VmValue,
        abi: runtime::VmValue,
    },
}

impl fmt::Display for NativeCompareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeCompareError::Lower(error) => write!(f, "{error}"),
            NativeCompareError::Eval(error) => write!(f, "{error}"),
            NativeCompareError::Abi(error) => write!(f, "{error}"),
            NativeCompareError::Vm(error) => write!(f, "{error}"),
            NativeCompareError::ResidualRequest { index, request } => write!(
                f,
                "VM root {index} produced a host/effect request instead of a value: {request:?}"
            ),
            NativeCompareError::RootCountMismatch { vm, native, abi } => {
                write!(
                    f,
                    "root count mismatch: VM {vm}, native control {native}, native ABI {abi}"
                )
            }
            NativeCompareError::ValueMismatch { index, vm, native } => write!(
                f,
                "native control root {index} mismatch: VM {vm:?}, native {native:?}"
            ),
            NativeCompareError::AbiValueMismatch { index, vm, abi } => write!(
                f,
                "native ABI root {index} mismatch: VM {vm:?}, native ABI {abi:?}"
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

impl From<NativeAbiEvalError> for NativeCompareError {
    fn from(value: NativeAbiEvalError) -> Self {
        Self::Abi(value)
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
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    let abi_values = eval_abi_module(&abi_module)?;
    let vm_results = runtime::compile_vm_module(module.clone())?.eval_roots()?;
    if vm_results.len() != native_values.len() || vm_results.len() != abi_values.len() {
        return Err(NativeCompareError::RootCountMismatch {
            vm: vm_results.len(),
            native: native_values.len(),
            abi: abi_values.len(),
        });
    }
    for (index, ((vm_result, native), abi)) in vm_results
        .into_iter()
        .zip(native_values)
        .zip(abi_values)
        .enumerate()
    {
        let vm = match vm_result {
            runtime::VmResult::Value(value) => value,
            runtime::VmResult::Request(request) => {
                return Err(NativeCompareError::ResidualRequest { index, request });
            }
        };
        if vm != native {
            return Err(NativeCompareError::ValueMismatch { index, vm, native });
        }
        if vm != abi {
            return Err(NativeCompareError::AbiValueMismatch { index, vm, abi });
        }
    }
    Ok(())
}

#[derive(Debug)]
pub enum NativeValueCompareError {
    Lower(NativeLowerError),
    Eval(NativeEvalError),
    Abi(NativeAbiEvalError),
    Vm(runtime::VmError),
    Cranelift(NativeValueCraneliftError),
    ResidualRequest {
        index: usize,
        request: runtime::VmRequest,
    },
    RootCountMismatch {
        vm: usize,
        native: usize,
        abi: usize,
        cranelift: usize,
    },
    NativeMismatch {
        index: usize,
        vm: runtime::VmValue,
        native: runtime::VmValue,
    },
    AbiMismatch {
        index: usize,
        vm: runtime::VmValue,
        abi: runtime::VmValue,
    },
    CraneliftMismatch {
        index: usize,
        vm: runtime::VmValue,
        cranelift: runtime::VmValue,
    },
}

impl fmt::Display for NativeValueCompareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeValueCompareError::Lower(error) => write!(f, "{error}"),
            NativeValueCompareError::Eval(error) => write!(f, "{error}"),
            NativeValueCompareError::Abi(error) => write!(f, "{error}"),
            NativeValueCompareError::Vm(error) => write!(f, "{error}"),
            NativeValueCompareError::Cranelift(error) => write!(f, "{error}"),
            NativeValueCompareError::ResidualRequest { index, request } => write!(
                f,
                "VM root {index} produced a host/effect request instead of a value: {request:?}"
            ),
            NativeValueCompareError::RootCountMismatch {
                vm,
                native,
                abi,
                cranelift,
            } => write!(
                f,
                "root count mismatch: VM {vm}, native control {native}, native ABI {abi}, value Cranelift {cranelift}"
            ),
            NativeValueCompareError::NativeMismatch { index, vm, native } => write!(
                f,
                "native control root {index} mismatch: VM {vm:?}, native {native:?}"
            ),
            NativeValueCompareError::AbiMismatch { index, vm, abi } => write!(
                f,
                "native ABI root {index} mismatch: VM {vm:?}, native ABI {abi:?}"
            ),
            NativeValueCompareError::CraneliftMismatch {
                index,
                vm,
                cranelift,
            } => write!(
                f,
                "value Cranelift root {index} mismatch: VM {vm:?}, Cranelift {cranelift:?}"
            ),
        }
    }
}

impl std::error::Error for NativeValueCompareError {}

impl From<NativeLowerError> for NativeValueCompareError {
    fn from(error: NativeLowerError) -> Self {
        NativeValueCompareError::Lower(error)
    }
}

impl From<NativeEvalError> for NativeValueCompareError {
    fn from(error: NativeEvalError) -> Self {
        NativeValueCompareError::Eval(error)
    }
}

impl From<NativeAbiEvalError> for NativeValueCompareError {
    fn from(error: NativeAbiEvalError) -> Self {
        NativeValueCompareError::Abi(error)
    }
}

impl From<runtime::VmError> for NativeValueCompareError {
    fn from(error: runtime::VmError) -> Self {
        NativeValueCompareError::Vm(error)
    }
}

impl From<NativeValueCraneliftError> for NativeValueCompareError {
    fn from(error: NativeValueCraneliftError) -> Self {
        NativeValueCompareError::Cranelift(error)
    }
}

pub fn compare_module_value(module: &runtime::Module) -> Result<(), NativeValueCompareError> {
    let native_module = lower_module(module)?;
    let native_values = eval_module(&native_module)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    let abi_values = eval_abi_module(&abi_module)?;
    let mut jit = compile_value_abi_module(&abi_module)?;
    let cranelift_values = jit.run_roots()?;

    let vm_results = runtime::compile_vm_module(module.clone())?.eval_roots()?;
    if vm_results.len() != native_values.len()
        || vm_results.len() != abi_values.len()
        || vm_results.len() != cranelift_values.len()
    {
        return Err(NativeValueCompareError::RootCountMismatch {
            vm: vm_results.len(),
            native: native_values.len(),
            abi: abi_values.len(),
            cranelift: cranelift_values.len(),
        });
    }

    for (index, (((vm_result, native), abi), cranelift)) in vm_results
        .into_iter()
        .zip(native_values)
        .zip(abi_values)
        .zip(cranelift_values)
        .enumerate()
    {
        let vm = match vm_result {
            runtime::VmResult::Value(value) => value,
            runtime::VmResult::Request(request) => {
                return Err(NativeValueCompareError::ResidualRequest { index, request });
            }
        };
        if vm != native {
            return Err(NativeValueCompareError::NativeMismatch { index, vm, native });
        }
        if vm != abi {
            return Err(NativeValueCompareError::AbiMismatch { index, vm, abi });
        }
        if vm != cranelift {
            return Err(NativeValueCompareError::CraneliftMismatch {
                index,
                vm,
                cranelift,
            });
        }
    }
    Ok(())
}

#[derive(Debug)]
pub enum NativeSourceCompareError {
    Lower(NativeLowerError),
    Eval(NativeEvalError),
    Abi(NativeAbiEvalError),
    Vm(runtime::VmError),
    Cranelift(NativeCraneliftError),
    ResidualRequest {
        index: usize,
        request: runtime::VmRequest,
    },
    RootCountMismatch {
        vm: usize,
        native: usize,
        abi: usize,
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
    UnsupportedAbiScalar {
        index: usize,
        value: runtime::VmValue,
    },
    NativeMismatch {
        index: usize,
        vm: i64,
        native: i64,
    },
    AbiMismatch {
        index: usize,
        vm: i64,
        abi: i64,
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
            NativeSourceCompareError::Lower(error) => write!(f, "{error}"),
            NativeSourceCompareError::Eval(error) => write!(f, "{error}"),
            NativeSourceCompareError::Abi(error) => write!(f, "{error}"),
            NativeSourceCompareError::Vm(error) => write!(f, "{error}"),
            NativeSourceCompareError::Cranelift(error) => write!(f, "{error}"),
            NativeSourceCompareError::ResidualRequest { index, request } => write!(
                f,
                "VM root {index} produced a host/effect request instead of a value: {request:?}"
            ),
            NativeSourceCompareError::RootCountMismatch {
                vm,
                native,
                abi,
                cranelift,
            } => write!(
                f,
                "root count mismatch: VM {vm}, native control {native}, native ABI {abi}, Cranelift {cranelift}"
            ),
            NativeSourceCompareError::UnsupportedVmScalar { index, value } => write!(
                f,
                "VM root {index} produced non-scalar prototype value {value:?}"
            ),
            NativeSourceCompareError::UnsupportedNativeScalar { index, value } => write!(
                f,
                "native control root {index} produced non-scalar prototype value {value:?}"
            ),
            NativeSourceCompareError::UnsupportedAbiScalar { index, value } => write!(
                f,
                "native ABI root {index} produced non-scalar prototype value {value:?}"
            ),
            NativeSourceCompareError::NativeMismatch { index, vm, native } => write!(
                f,
                "native control root {index} mismatch: VM scalar {vm}, native scalar {native}"
            ),
            NativeSourceCompareError::AbiMismatch { index, vm, abi } => write!(
                f,
                "native ABI root {index} mismatch: VM scalar {vm}, native ABI scalar {abi}"
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

impl From<NativeAbiEvalError> for NativeSourceCompareError {
    fn from(error: NativeAbiEvalError) -> Self {
        NativeSourceCompareError::Abi(error)
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

pub fn compare_module_i64(module: &runtime::Module) -> Result<(), NativeSourceCompareError> {
    compare_runtime_module_i64(module.clone())
}

fn compare_runtime_module_i64(
    runtime_module: runtime::Module,
) -> Result<(), NativeSourceCompareError> {
    let native_module = lower_module(&runtime_module)?;
    let native_values = eval_module(&native_module)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    let abi_values = eval_abi_module(&abi_module)?;
    let mut jit = compile_abi_module(&abi_module)?;
    let cranelift_values = jit.run_roots_i64()?;

    let vm_results = runtime::compile_vm_module(runtime_module)?.eval_roots()?;
    if vm_results.len() != native_values.len()
        || vm_results.len() != abi_values.len()
        || vm_results.len() != cranelift_values.len()
    {
        return Err(NativeSourceCompareError::RootCountMismatch {
            vm: vm_results.len(),
            native: native_values.len(),
            abi: abi_values.len(),
            cranelift: cranelift_values.len(),
        });
    }

    for (index, (((vm_result, native_value), abi_value), cranelift_value)) in vm_results
        .into_iter()
        .zip(native_values)
        .zip(abi_values)
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
        let abi_scalar = scalar_i64(abi_value.clone()).ok_or(
            NativeSourceCompareError::UnsupportedAbiScalar {
                index,
                value: abi_value,
            },
        )?;
        if vm_scalar != native_scalar {
            return Err(NativeSourceCompareError::NativeMismatch {
                index,
                vm: vm_scalar,
                native: native_scalar,
            });
        }
        if vm_scalar != abi_scalar {
            return Err(NativeSourceCompareError::AbiMismatch {
                index,
                vm: vm_scalar,
                abi: abi_scalar,
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
    use yulang_typed_ir as typed_ir;

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

    fn match_expr(scrutinee: runtime::Expr, arms: Vec<runtime::MatchArm>) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms,
                evidence: runtime::JoinEvidence {
                    result: typed_ir::Type::Unknown,
                },
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

    fn bind_pattern(name: &str) -> runtime::Pattern {
        runtime::Pattern::Bind {
            name: typed_ir::Name(name.to_string()),
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

    fn int_lit(value: &str) -> runtime::Expr {
        unknown_lit(typed_ir::Lit::Int(value.to_string()))
    }

    fn string_lit(value: &str) -> runtime::Expr {
        unknown_lit(typed_ir::Lit::String(value.to_string()))
    }

    fn primitive_call(op: typed_ir::PrimitiveOp, args: Vec<runtime::Expr>) -> runtime::Expr {
        args.into_iter()
            .fold(primitive(op), |callee, arg| apply(callee, arg))
    }

    fn tuple(items: Vec<runtime::Expr>) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::Tuple(items), runtime::Type::unknown())
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

    fn range_included_excluded(start: &str, end: &str) -> runtime::Expr {
        variant(
            "within",
            Some(tuple(vec![
                variant("included", Some(int_lit(start))),
                variant("excluded", Some(int_lit(end))),
            ])),
        )
    }

    fn record(fields: Vec<(&str, runtime::Expr)>) -> runtime::Expr {
        record_with_spread(fields, None)
    }

    fn record_with_spread(
        fields: Vec<(&str, runtime::Expr)>,
        spread: Option<runtime::RecordSpreadExpr>,
    ) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|(name, value)| runtime::RecordExprField {
                        name: typed_ir::Name(name.to_string()),
                        value,
                    })
                    .collect(),
                spread,
            },
            runtime::Type::unknown(),
        )
    }

    fn select(base: runtime::Expr, field: &str) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Select {
                base: Box::new(base),
                field: typed_ir::Name(field.to_string()),
            },
            runtime::Type::unknown(),
        )
    }

    fn list(items: Vec<runtime::Expr>) -> runtime::Expr {
        items.into_iter().fold(
            apply(
                primitive(typed_ir::PrimitiveOp::ListEmpty),
                unknown_lit(typed_ir::Lit::Unit),
            ),
            |acc, item| {
                apply(
                    apply(primitive(typed_ir::PrimitiveOp::ListMerge), acc),
                    apply(primitive(typed_ir::PrimitiveOp::ListSingleton), item),
                )
            },
        )
    }

    fn list_pattern(
        prefix: Vec<runtime::Pattern>,
        spread: Option<runtime::Pattern>,
        suffix: Vec<runtime::Pattern>,
    ) -> runtime::Pattern {
        runtime::Pattern::List {
            prefix,
            spread: spread.map(Box::new),
            suffix,
            ty: runtime::Type::unknown(),
        }
    }

    fn record_pattern(
        fields: Vec<(&str, runtime::Pattern)>,
        spread: Option<runtime::RecordSpreadPattern>,
    ) -> runtime::Pattern {
        runtime::Pattern::Record {
            fields: fields
                .into_iter()
                .map(|(name, pattern)| runtime::RecordPatternField {
                    name: typed_ir::Name(name.to_string()),
                    pattern,
                    default: None,
                })
                .collect(),
            spread,
            ty: runtime::Type::unknown(),
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
            path: typed_ir::Path::default(),
            bindings,
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        runtime::Module {
            path: typed_ir::Path::default(),
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
                primitive(typed_ir::PrimitiveOp::IntAdd),
                unknown_lit(typed_ir::Lit::Int("20".to_string())),
            ),
            unknown_lit(typed_ir::Lit::Int("22".to_string())),
        );
        let module = module_with_root(expr);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_if_with_vm() {
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
        let module = module_with_root(expr);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_simple_block_binding_with_vm() {
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
                    apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
            ),
        );
        let root = apply(
            var("inc"),
            unknown_lit(typed_ir::Lit::Int("41".to_string())),
        );
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
                    apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
            ),
        );
        let twice = binding(
            "twice",
            lambda("x", apply(var("inc"), apply(var("inc"), var("x")))),
        );
        let root = apply(
            var("twice"),
            unknown_lit(typed_ir::Lit::Int("40".to_string())),
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
        let module = module_with_binding_and_root(countdown, root);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_immediate_lambda_call_with_vm() {
        let expr = apply(
            lambda(
                "x",
                apply(
                    apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
            ),
            unknown_lit(typed_ir::Lit::Int("41".to_string())),
        );
        let module = module_with_root(expr);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_lambda_capture_with_vm() {
        let expr = block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("y"),
                value: unknown_lit(typed_ir::Lit::Int("10".to_string())),
            }],
            apply(
                lambda(
                    "x",
                    apply(
                        apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("x")),
                        var("y"),
                    ),
                ),
                unknown_lit(typed_ir::Lit::Int("32".to_string())),
            ),
        );
        let module = module_with_root(expr);

        compare_module(&module).expect("native control matches VM");
    }

    #[test]
    fn compares_if_with_vm_native_abi_and_cranelift() {
        let module = module_with_root(if_expr(
            apply(
                apply(
                    primitive(typed_ir::PrimitiveOp::IntLt),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
                unknown_lit(typed_ir::Lit::Int("2".to_string())),
            ),
            unknown_lit(typed_ir::Lit::Int("10".to_string())),
            unknown_lit(typed_ir::Lit::Int("20".to_string())),
        ));

        compare_module_i64(&module).expect("scalar paths match");
    }

    #[test]
    fn compares_record_select_with_value_cranelift() {
        let module = module_with_root(select(
            record(vec![("x", int_lit("1")), ("y", int_lit("2"))]),
            "x",
        ));

        compare_module_value(&module).expect("value paths match");
    }

    #[test]
    fn compares_record_spread_expr_with_value_cranelift() {
        let base = record(vec![("x", int_lit("1"))]);
        let module = module_with_root(select(
            record_with_spread(
                vec![("y", int_lit("2"))],
                Some(runtime::RecordSpreadExpr::Head(Box::new(base))),
            ),
            "x",
        ));

        compare_module_value(&module).expect("value paths match");
    }

    #[test]
    fn compares_list_spread_pattern_with_value_cranelift() {
        let arm = runtime::MatchArm {
            pattern: list_pattern(
                vec![bind_pattern("head")],
                Some(bind_pattern("middle")),
                vec![bind_pattern("tail")],
            ),
            guard: None,
            body: var("middle"),
        };
        let module = module_with_root(match_expr(
            list(vec![int_lit("1"), int_lit("2"), int_lit("3")]),
            vec![arm],
        ));

        compare_module_value(&module).expect("value paths match");
    }

    #[test]
    fn compares_record_spread_pattern_with_value_cranelift() {
        let arm = runtime::MatchArm {
            pattern: record_pattern(
                vec![("x", bind_pattern("x"))],
                Some(runtime::RecordSpreadPattern::Tail(Box::new(bind_pattern(
                    "rest",
                )))),
            ),
            guard: None,
            body: select(var("rest"), "y"),
        };
        let module = module_with_root(match_expr(
            record(vec![("x", int_lit("1")), ("y", int_lit("2"))]),
            vec![arm],
        ));

        compare_module_value(&module).expect("value paths match");
    }

    #[test]
    fn compares_string_value_primitives_with_value_cranelift() {
        for root in [
            primitive_call(
                typed_ir::PrimitiveOp::StringEq,
                vec![string_lit("yu"), string_lit("yu")],
            ),
            primitive_call(
                typed_ir::PrimitiveOp::StringIndex,
                vec![string_lit("aあ🙂z"), int_lit("2")],
            ),
            primitive_call(
                typed_ir::PrimitiveOp::StringIndexRangeRaw,
                vec![string_lit("aあ🙂z"), int_lit("1"), int_lit("3")],
            ),
            primitive_call(
                typed_ir::PrimitiveOp::StringSpliceRaw,
                vec![
                    string_lit("aあ🙂z"),
                    int_lit("1"),
                    int_lit("3"),
                    string_lit("bc"),
                ],
            ),
            primitive_call(
                typed_ir::PrimitiveOp::StringIndexRange,
                vec![string_lit("aあ🙂z"), range_included_excluded("1", "3")],
            ),
            primitive_call(
                typed_ir::PrimitiveOp::StringSplice,
                vec![
                    string_lit("aあ🙂z"),
                    range_included_excluded("1", "3"),
                    string_lit("bc"),
                ],
            ),
        ] {
            compare_module_value(&module_with_root(root)).expect("value paths match");
        }
    }

    #[test]
    fn compares_list_value_primitives_with_value_cranelift() {
        for root in [
            primitive_call(
                typed_ir::PrimitiveOp::ListIndexRange,
                vec![
                    list(vec![int_lit("1"), int_lit("2"), int_lit("3"), int_lit("4")]),
                    range_included_excluded("1", "3"),
                ],
            ),
            primitive_call(
                typed_ir::PrimitiveOp::ListSpliceRaw,
                vec![
                    list(vec![int_lit("1"), int_lit("2"), int_lit("3"), int_lit("4")]),
                    int_lit("1"),
                    int_lit("3"),
                    list(vec![int_lit("8"), int_lit("9")]),
                ],
            ),
            primitive_call(
                typed_ir::PrimitiveOp::ListSplice,
                vec![
                    list(vec![int_lit("1"), int_lit("2"), int_lit("3"), int_lit("4")]),
                    range_included_excluded("1", "3"),
                    list(vec![int_lit("8"), int_lit("9")]),
                ],
            ),
            primitive_call(
                typed_ir::PrimitiveOp::ListViewRaw,
                vec![list(vec![int_lit("1"), int_lit("2")])],
            ),
        ] {
            compare_module_value(&module_with_root(root)).expect("value paths match");
        }
    }
}
