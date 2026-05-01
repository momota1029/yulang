use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::rc::Rc;

use yulang_core_ir as core_ir;

use crate::diagnostic::RuntimeError;
use crate::invariant::{RuntimeStage, check_runtime_invariants};
use crate::ir::{
    Binding, EffectIdRef, EffectIdVar, Expr, ExprKind, HandleArm, MatchArm, Module, Pattern,
    RecordExprField, RecordSpreadExpr, Stmt, Type,
};
use crate::runtime::list_tree::{ListTree, ListView};
use crate::runtime::string_tree::StringTree;
use crate::types::effect_is_empty;

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

    pub fn eval_roots(&self) -> Result<Vec<VmResult>, VmError> {
        let mut interpreter = VmInterpreter::new(&self.module);
        (0..self.module.root_exprs.len())
            .map(|index| interpreter.eval_root_expr(index))
            .collect()
    }
}

pub fn compile_vm_module(module: Module) -> Result<VmModule, VmError> {
    check_runtime_invariants(&module, RuntimeStage::BeforeVm).map_err(VmError::Runtime)?;
    let effects = EffectPathResolver::collect(&module);
    Ok(VmModule {
        module: erase_module(module, &effects)?,
    })
}

#[derive(Debug, Clone, PartialEq)]
pub enum VmError {
    Runtime(RuntimeError),
    ResidualPolymorphicBinding {
        path: core_ir::Path,
        vars: Vec<core_ir::TypeVar>,
    },
    MissingRootExpr(usize),
    UnboundVariable(core_ir::Path),
    PatternMismatch,
    ExpectedBool(VmValue),
    ExpectedInt(VmValue),
    ExpectedFloat(VmValue),
    ExpectedString(VmValue),
    ExpectedList(VmValue),
    ExpectedRecord(VmValue),
    ExpectedVariant(VmValue),
    ExpectedClosure(VmValue),
    ExpectedThunk(VmValue),
    ExpectedEffectId(VmValue),
    InvalidPrimitiveArity {
        expected: usize,
        actual: usize,
    },
    UnsupportedPrimitive(core_ir::PrimitiveOp),
    UnsupportedEffectIdVar(usize),
    UnsupportedFindId,
    UnexpectedRequest(core_ir::Path),
}

impl fmt::Display for VmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for VmError {}

mod continuation;
mod erase;
mod guard;
mod interpreter;
mod model;
mod primitive;
mod value;

use erase::*;
use guard::*;
use interpreter::*;
use model::*;
pub use model::{VmContinuation, VmPrimitive, VmRequest, VmResult, VmValue};
use primitive::*;
use value::*;

#[cfg(test)]
mod tests;
