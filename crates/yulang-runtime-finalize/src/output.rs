use yulang_runtime_ir::{Module, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::diagnostic::{FinalizeDiagnostic, FinalizeResult};
use crate::principal::InstanceKey;

pub fn finalize_module(module: Module) -> FinalizeResult<FinalizeOutput> {
    Ok(FinalizeOutput {
        module,
        report: FinalizeReport::default(),
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FinalizeOutput {
    pub module: Module,
    pub report: FinalizeReport,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FinalizeReport {
    pub planned_instances: Vec<InstanceKey>,
    pub diagnostics: Vec<FinalizeDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TopLevelDemand {
    pub root: TopLevelRoot,
    pub expected_value: RuntimeType,
    pub expected_effect: typed_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TopLevelRoot {
    Expr(usize),
    Named(typed_ir::Path),
}
