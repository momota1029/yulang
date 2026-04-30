use crate::names::Path;
use crate::types::{Type, TypeBounds};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CoreGraphView {
    pub bindings: Vec<BindingGraphNode>,
    pub root_exprs: Vec<ExprGraphNode>,
    pub runtime_symbols: Vec<RuntimeSymbol>,
}

pub type TypeGraphView = CoreGraphView;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BindingGraphNode {
    pub binding: Path,
    pub scheme_body: Type,
    pub body_bounds: TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprGraphNode {
    pub owner: GraphOwner,
    pub bounds: TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeSymbol {
    pub path: Path,
    pub kind: RuntimeSymbolKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeSymbolKind {
    Value,
    RoleMethod,
    EffectOperation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GraphOwner {
    RootExpr(usize),
}
