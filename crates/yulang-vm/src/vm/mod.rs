use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::path::PathBuf;
use std::rc::Rc;

use yulang_runtime::RuntimeError;
use yulang_runtime::types::effect_is_empty;
use yulang_runtime_ir::{
    EffectIdRef, EffectIdVar, FinalizedBinding as Binding, FinalizedExpr as Expr,
    FinalizedExprKind as ExprKind, FinalizedHandleArm as HandleArm, FinalizedMatchArm as MatchArm,
    FinalizedModule as Module, FinalizedPattern as Pattern,
    FinalizedRecordExprField as RecordExprField, FinalizedRecordSpreadExpr as RecordSpreadExpr,
    FinalizedStmt as Stmt, FinalizedType as Type,
};
use yulang_typed_ir as typed_ir;

use crate::runtime::bytes_tree::BytesTree;
use crate::runtime::list_tree::{ListTree, ListView};
use crate::runtime::string_tree::StringTree;

pub struct VmModule {
    module: Module,
}

impl VmModule {
    pub fn module(&self) -> &Module {
        &self.module
    }

    pub fn eval_root_expr(&self, index: usize) -> Result<VmResult, VmError> {
        VmInterpreter::new(&self.module).eval_root_expr(index)
    }

    pub fn eval_root_expr_profiled(&self, index: usize) -> Result<(VmResult, VmProfile), VmError> {
        let mut interpreter = VmInterpreter::new(&self.module);
        let result = interpreter.eval_root_expr(index)?;
        Ok((result, interpreter.profile()))
    }

    pub fn eval_roots(&self) -> Result<Vec<VmResult>, VmError> {
        Ok(self.eval_roots_profiled()?.0)
    }

    pub fn eval_roots_profiled(&self) -> Result<(Vec<VmResult>, VmProfile), VmError> {
        let mut interpreter = VmInterpreter::new(&self.module);
        let results = (0..self.module.root_exprs.len())
            .map(|index| interpreter.eval_root_expr(index))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((results, interpreter.profile()))
    }

    pub fn resume_request(&self, request: VmRequest, value: VmValue) -> Result<VmResult, VmError> {
        VmInterpreter::new(&self.module).resume(request.continuation, value)
    }

    pub fn force_value_profiled(&self, value: VmValue) -> Result<(VmResult, VmProfile), VmError> {
        let mut interpreter = VmInterpreter::new(&self.module);
        let result = interpreter.bind_here(value)?;
        Ok((result, interpreter.profile()))
    }

    pub fn resume_request_profiled(
        &self,
        request: VmRequest,
        value: VmValue,
    ) -> Result<(VmResult, VmProfile), VmError> {
        let mut interpreter = VmInterpreter::new(&self.module);
        let result = interpreter.resume(request.continuation, value)?;
        Ok((result, interpreter.profile()))
    }
}

pub trait IntoVmModule {
    fn into_vm_module(self) -> Module;
}

impl IntoVmModule for Module {
    fn into_vm_module(self) -> Module {
        self
    }
}

impl IntoVmModule for yulang_runtime::Module {
    fn into_vm_module(self) -> Module {
        lift_legacy_runtime_module(self)
    }
}

pub fn compile_vm_module<M: IntoVmModule>(module: M) -> Result<VmModule, VmError> {
    let module = module.into_vm_module();
    let effects = EffectPathResolver::collect(&module);
    let module = erase_module(module, &effects)?;
    Ok(VmModule { module })
}

fn lift_legacy_runtime_module(module: yulang_runtime::Module) -> Module {
    Module {
        path: module.path,
        bindings: module
            .bindings
            .into_iter()
            .map(|binding| Binding {
                name: binding.name,
                type_params: binding.type_params,
                scheme: binding.scheme,
                body: lift_legacy_runtime_expr(binding.body),
            })
            .collect(),
        root_exprs: module
            .root_exprs
            .into_iter()
            .map(lift_legacy_runtime_expr)
            .collect(),
        roots: module.roots,
        role_impls: module.role_impls,
    }
}

fn lift_legacy_runtime_expr(expr: yulang_runtime::Expr) -> Expr {
    let ty = lift_legacy_runtime_type(expr.ty);
    let kind = match expr.kind {
        yulang_runtime_ir::ExprKind::Var(path) => ExprKind::Var(path),
        yulang_runtime_ir::ExprKind::EffectOp(path) => ExprKind::EffectOp(path),
        yulang_runtime_ir::ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
        yulang_runtime_ir::ExprKind::Lit(lit) => ExprKind::Lit(lit),
        yulang_runtime_ir::ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(lift_legacy_runtime_expr(*body)),
        },
        yulang_runtime_ir::ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(lift_legacy_runtime_expr(*callee)),
            arg: Box::new(lift_legacy_runtime_expr(*arg)),
            evidence,
            instantiation,
        },
        yulang_runtime_ir::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(lift_legacy_runtime_expr(*cond)),
            then_branch: Box::new(lift_legacy_runtime_expr(*then_branch)),
            else_branch: Box::new(lift_legacy_runtime_expr(*else_branch)),
            evidence,
        },
        yulang_runtime_ir::ExprKind::Tuple(items) => {
            ExprKind::Tuple(items.into_iter().map(lift_legacy_runtime_expr).collect())
        }
        yulang_runtime_ir::ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordExprField {
                    name: field.name,
                    value: lift_legacy_runtime_expr(field.value),
                })
                .collect(),
            spread: spread.map(lift_legacy_runtime_record_spread_expr),
        },
        yulang_runtime_ir::ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(lift_legacy_runtime_expr(*value))),
        },
        yulang_runtime_ir::ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(lift_legacy_runtime_expr(*base)),
            field,
        },
        yulang_runtime_ir::ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(lift_legacy_runtime_expr(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: lift_legacy_runtime_pattern(arm.pattern),
                    guard: arm.guard.map(lift_legacy_runtime_expr),
                    body: lift_legacy_runtime_expr(arm.body),
                })
                .collect(),
            evidence,
        },
        yulang_runtime_ir::ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts.into_iter().map(lift_legacy_runtime_stmt).collect(),
            tail: tail.map(|tail| Box::new(lift_legacy_runtime_expr(*tail))),
        },
        yulang_runtime_ir::ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(lift_legacy_runtime_expr(*body)),
            arms: arms
                .into_iter()
                .map(|arm| HandleArm {
                    effect: arm.effect,
                    payload: lift_legacy_runtime_pattern(arm.payload),
                    resume: arm.resume.map(|resume| yulang_runtime_ir::ResumeBinding {
                        name: resume.name,
                        ty: lift_legacy_runtime_type(resume.ty),
                    }),
                    guard: arm.guard.map(lift_legacy_runtime_expr),
                    body: lift_legacy_runtime_expr(arm.body),
                })
                .collect(),
            evidence,
            handler,
        },
        yulang_runtime_ir::ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(lift_legacy_runtime_expr(*expr)),
        },
        yulang_runtime_ir::ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect,
            value: lift_legacy_runtime_type(value),
            expr: Box::new(lift_legacy_runtime_expr(*expr)),
        },
        yulang_runtime_ir::ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(lift_legacy_runtime_expr(*body)),
        },
        yulang_runtime_ir::ExprKind::PeekId => ExprKind::PeekId,
        yulang_runtime_ir::ExprKind::FindId { id } => ExprKind::FindId { id },
        yulang_runtime_ir::ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(lift_legacy_runtime_expr(*thunk)),
        },
        yulang_runtime_ir::ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(lift_legacy_runtime_expr(*expr)),
        },
        yulang_runtime_ir::ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(lift_legacy_runtime_expr(*expr)),
        },
    };
    Expr::typed(kind, ty)
}

fn lift_legacy_runtime_stmt(stmt: yulang_runtime::Stmt) -> Stmt {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => Stmt::Let {
            pattern: lift_legacy_runtime_pattern(pattern),
            value: lift_legacy_runtime_expr(value),
        },
        yulang_runtime_ir::Stmt::Expr(expr) => Stmt::Expr(lift_legacy_runtime_expr(expr)),
        yulang_runtime_ir::Stmt::Module { def, body } => Stmt::Module {
            def,
            body: lift_legacy_runtime_expr(body),
        },
    }
}

fn lift_legacy_runtime_pattern(pattern: yulang_runtime::Pattern) -> Pattern {
    match pattern {
        yulang_runtime_ir::Pattern::Wildcard { ty } => Pattern::Wildcard {
            ty: lift_legacy_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Bind { name, ty } => Pattern::Bind {
            name,
            ty: lift_legacy_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Lit { lit, ty } => Pattern::Lit {
            lit,
            ty: lift_legacy_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Tuple { items, ty } => Pattern::Tuple {
            items: items.into_iter().map(lift_legacy_runtime_pattern).collect(),
            ty: lift_legacy_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => Pattern::List {
            prefix: prefix
                .into_iter()
                .map(lift_legacy_runtime_pattern)
                .collect(),
            spread: spread.map(|spread| Box::new(lift_legacy_runtime_pattern(*spread))),
            suffix: suffix
                .into_iter()
                .map(lift_legacy_runtime_pattern)
                .collect(),
            ty: lift_legacy_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Record { fields, spread, ty } => Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::RecordPatternField {
                    name: field.name,
                    pattern: lift_legacy_runtime_pattern(field.pattern),
                    default: field.default.map(lift_legacy_runtime_expr),
                })
                .collect(),
            spread: spread.map(lift_legacy_runtime_record_spread_pattern),
            ty: lift_legacy_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Variant { tag, value, ty } => Pattern::Variant {
            tag,
            value: value.map(|value| Box::new(lift_legacy_runtime_pattern(*value))),
            ty: lift_legacy_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Or { left, right, ty } => Pattern::Or {
            left: Box::new(lift_legacy_runtime_pattern(*left)),
            right: Box::new(lift_legacy_runtime_pattern(*right)),
            ty: lift_legacy_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::As { pattern, name, ty } => Pattern::As {
            pattern: Box::new(lift_legacy_runtime_pattern(*pattern)),
            name,
            ty: lift_legacy_runtime_type(ty),
        },
    }
}

fn lift_legacy_runtime_record_spread_expr(
    spread: yulang_runtime::RecordSpreadExpr,
) -> RecordSpreadExpr {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr) => {
            RecordSpreadExpr::Head(Box::new(lift_legacy_runtime_expr(*expr)))
        }
        yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            RecordSpreadExpr::Tail(Box::new(lift_legacy_runtime_expr(*expr)))
        }
    }
}

fn lift_legacy_runtime_record_spread_pattern(
    spread: yulang_runtime::RecordSpreadPattern,
) -> yulang_runtime_ir::FinalizedRecordSpreadPattern {
    match spread {
        yulang_runtime_ir::RecordSpreadPattern::Head(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Head(Box::new(lift_legacy_runtime_pattern(
                *pattern,
            )))
        }
        yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Tail(Box::new(lift_legacy_runtime_pattern(
                *pattern,
            )))
        }
    }
}

fn lift_legacy_runtime_type(ty: yulang_runtime::Type) -> Type {
    match ty {
        yulang_runtime::Type::Unknown => Type::Unknown,
        yulang_runtime::Type::Core(ty) => lift_core_type(ty),
        yulang_runtime::Type::Fun { param, ret } => Type::fun(
            lift_legacy_runtime_type(*param),
            lift_legacy_runtime_type(*ret),
        ),
        yulang_runtime::Type::Thunk { effect, value } => {
            Type::thunk(effect, lift_legacy_runtime_type(*value))
        }
    }
}

fn lift_core_type(ty: typed_ir::Type) -> Type {
    match ty {
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => Type::fun(
            lift_core_type_with_effect(*param, *param_effect),
            lift_core_type_with_effect(*ret, *ret_effect),
        ),
        other => Type::value(other),
    }
}

fn lift_core_type_with_effect(value: typed_ir::Type, effect: typed_ir::Type) -> Type {
    let value = lift_core_type(value);
    if effect_is_empty(&effect) {
        value
    } else {
        Type::thunk(effect, value)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum VmError {
    Runtime(RuntimeError),
    ResidualPolymorphicBinding {
        path: typed_ir::Path,
        vars: Vec<typed_ir::TypeVar>,
    },
    MissingRootExpr(usize),
    UnboundVariable(typed_ir::Path),
    PatternMismatch,
    ExpectedBool(VmValue),
    ExpectedInt(VmValue),
    ExpectedFloat(VmValue),
    ExpectedString(VmValue),
    ExpectedChar(VmValue),
    ExpectedBytes(VmValue),
    ExpectedPath(VmValue),
    ExpectedList(VmValue),
    ExpectedRecord(VmValue),
    ExpectedVariant(VmValue),
    ExpectedClosure(VmValue),
    ExpectedThunk(VmValue),
    ExpectedEffectId(VmValue),
    YadaYada,
    InvalidPrimitiveArity {
        expected: usize,
        actual: usize,
    },
    UnsupportedPrimitive(typed_ir::PrimitiveOp),
    UnsupportedEffectIdVar(usize),
    UnsupportedFindId,
    UnexpectedRequest(typed_ir::Path),
    HostIo(String),
}

impl fmt::Display for VmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for VmError {}

mod continuation;
mod control;
mod erase;
mod guard;
mod interpreter;
mod model;
pub mod primitive;
mod value;

use erase::*;
use guard::*;
use interpreter::*;
pub(crate) use model::VmFileHandleState;
use model::*;
pub use model::{
    VmContinuation, VmFileHandle, VmPrimitive, VmProfile, VmRequest, VmResult, VmValue,
};
use primitive::*;
use value::*;

pub use control::{CONTROL_VM_ARTIFACT_VERSION, ControlVmModule, compile_control_vm_module};

#[cfg(test)]
mod tests;
