use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::path::PathBuf;
use std::rc::Rc;

use yulang_runtime_ir::{
    EffectIdRef, EffectIdVar, FinalizedBinding as Binding, FinalizedExpr as Expr,
    FinalizedExprKind as ExprKind, FinalizedHandleArm as HandleArm, FinalizedMatchArm as MatchArm,
    FinalizedModule as Module, FinalizedPattern as Pattern,
    FinalizedRecordExprField as RecordExprField, FinalizedRecordSpreadExpr as RecordSpreadExpr,
    FinalizedStmt as Stmt, RuntimeType as Type,
};
use yulang_runtime_types::RuntimeError;
use yulang_runtime_types::types::effect_is_empty;
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

pub fn compile_vm_module<M: IntoVmModule>(module: M) -> Result<VmModule, VmError> {
    let module = module.into_vm_module();
    let effects = EffectPathResolver::collect(&module);
    let module = erase_module(module, &effects)?;
    Ok(VmModule { module })
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
