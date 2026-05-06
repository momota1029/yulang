use crate::names::Path;
use crate::types::{Type, TypeBounds};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CoreGraphView {
    pub bindings: Vec<BindingGraphNode>,
    pub root_exprs: Vec<ExprGraphNode>,
    pub runtime_symbols: Vec<RuntimeSymbol>,
}

pub type TypeGraphView = CoreGraphView;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BindingGraphNode {
    pub binding: Path,
    pub scheme_body: Type,
    pub body_bounds: TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExprGraphNode {
    pub owner: GraphOwner,
    pub bounds: TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeSymbol {
    pub path: Path,
    pub kind: RuntimeSymbolKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeSymbolKind {
    Value,
    RoleMethod,
    EffectOperation,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum GraphOwner {
    RootExpr(usize),
}
