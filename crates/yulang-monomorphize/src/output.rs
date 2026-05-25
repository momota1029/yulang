use yulang_runtime_ir::{FinalizedModule as Module, FinalizedType as RuntimeType};

use crate::{MonomorphizeInstanceCacheProfile, GraphSolution};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MonomorphizeOutput {
    pub module: Module,
    pub report: MonomorphizeReport,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct MonomorphizeReport {
    pub root_graph_inputs: Vec<RootGraphInput>,
    pub root_graph_solutions: Vec<RootGraphSolution>,
    pub cache_profile: MonomorphizeInstanceCacheProfile,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootGraphInput {
    pub root: RootGraphRoot,
    pub known_type: Option<RuntimeType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RootGraphRoot {
    Expr(usize),
    Binding(yulang_typed_ir::Path),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootGraphSolution {
    pub root: RootGraphRoot,
    pub occurrence: usize,
    pub binding: yulang_typed_ir::Path,
    pub alias: yulang_typed_ir::Path,
    pub callee_type: RuntimeType,
    pub result_type: RuntimeType,
    pub graph: GraphSolution,
    pub type_substitutions: Vec<yulang_typed_ir::TypeSubstitution>,
}
