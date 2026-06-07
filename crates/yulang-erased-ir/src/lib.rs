//! Type-erased inference output IR.
//!
//! This crate owns the IR boundary that monomorphization is allowed to read.
//! Expression nodes represent value structure only: they do not carry inferred
//! node types, effects, annotation evidence, apply evidence, or coercion nodes.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

pub mod types;

pub use types::{
    PrimitiveOp, RecordField, RecordSpread, RecordType, RoleRequirement, RoleRequirementArg,
    Scheme, Type, TypeArg, TypeBounds, TypeSubstitution, TypeVar, VariantCase, VariantType,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct DefId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RefId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Name(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct Path {
    pub segments: Vec<Name>,
}

impl Path {
    pub fn new(segments: Vec<Name>) -> Self {
        Self { segments }
    }

    pub fn from_name(name: Name) -> Self {
        Self {
            segments: vec![name],
        }
    }

    pub fn push(&mut self, name: Name) {
        self.segments.push(name);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct InferExport {
    pub erased: ErasedProgram,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ErasedProgram {
    pub module: ErasedModule,
    pub refs: RefExportTable,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ErasedModule {
    pub path: Path,
    pub bindings: Vec<InferredBinding>,
    pub root_exprs: Vec<InferredExpr>,
    pub roots: Vec<PrincipalRoot>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InferredBinding {
    pub name: Path,
    pub scheme: Scheme,
    pub body: InferredExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InferredExpr {
    pub typ: TypeBounds,
    pub eff: TypeBounds,
    pub ir: ErasedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrincipalRoot {
    Binding(Path),
    Expr(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct RefExportTable {
    pub direct: BTreeMap<RefId, DefId>,
    pub resolved_typeclass: BTreeMap<RefId, ResolvedTypeClassRef>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolvedTypeClassRef {
    pub class: Path,
    pub member: DefId,
    pub impl_def: Option<DefId>,
    pub impl_member: DefId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeClassObligation {
    pub ref_id: RefId,
    pub class: Path,
    pub member: DefId,
    pub args: Vec<Type>,
    pub associated: Vec<AssociatedTypeConstraint>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AssociatedTypeConstraint {
    pub name: Name,
    pub bounds: TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ErasedExpr {
    Def(DefId),
    Ref(RefId),
    PrimitiveOp(PrimitiveOp),
    Lit(Lit),
    Lambda {
        param: DefId,
        body: Box<ErasedExpr>,
    },
    Apply {
        callee: Box<ErasedExpr>,
        arg: Box<ErasedExpr>,
    },
    RefSet {
        reference: Box<ErasedExpr>,
        value: Box<ErasedExpr>,
    },
    Tuple(Vec<ErasedExpr>),
    Record {
        fields: Vec<RecordExprField>,
        spread: Option<RecordSpreadExpr>,
    },
    Variant {
        tag: Name,
        value: Option<Box<ErasedExpr>>,
        source: VariantExprSource,
    },
    Select {
        base: Box<ErasedExpr>,
        field: Name,
    },
    Match {
        scrutinee: Box<ErasedExpr>,
        arms: Vec<MatchArm>,
    },
    Handle {
        body: Box<ErasedExpr>,
        arms: Vec<HandleArm>,
    },
    Block(ErasedBlock),
    BindHere {
        expr: Box<ErasedExpr>,
    },
    Pack {
        var: TypeVar,
        expr: Box<ErasedExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ErasedBlock {
    pub stmts: Vec<ErasedStmt>,
    pub tail: Option<Box<ErasedExpr>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ErasedStmt {
    Let { pattern: Pattern, value: ErasedExpr },
    Expr(ErasedExpr),
    Module { def: DefId, body: ErasedBlock },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<ErasedExpr>,
    pub body: ErasedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HandleArm {
    pub effect: Path,
    pub payload: Pattern,
    pub resume: Option<DefId>,
    pub guard: Option<ErasedExpr>,
    pub body: ErasedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pattern {
    Wildcard,
    Bind(DefId),
    Lit(Lit),
    Tuple(Vec<Pattern>),
    List {
        prefix: Vec<Pattern>,
        spread: Option<Box<Pattern>>,
        suffix: Vec<Pattern>,
    },
    Record {
        fields: Vec<RecordPatternField>,
        spread: Option<RecordSpreadPattern>,
    },
    Variant {
        tag: Name,
        value: Option<Box<Pattern>>,
    },
    Constructor {
        ref_id: RefId,
        payload: Option<Box<Pattern>>,
    },
    UnresolvedName(Name),
    Or {
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    As {
        pattern: Box<Pattern>,
        def: DefId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordExprField {
    pub name: Name,
    pub value: ErasedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecordSpreadExpr {
    Head(Box<ErasedExpr>),
    Tail(Box<ErasedExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordPatternField {
    pub name: Name,
    pub pattern: Pattern,
    pub default: Option<ErasedExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecordSpreadPattern {
    Head(Box<Pattern>),
    Tail(Box<Pattern>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum VariantExprSource {
    #[default]
    Constructor,
    PolyVariantSyntax,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Lit {
    Int(String),
    Float(String),
    String(String),
    Bool(bool),
    Unit,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn erased_program_round_trips_through_json() {
        let program = ErasedProgram {
            module: ErasedModule {
                path: Path::new(vec![Name("main".to_string())]),
                root_exprs: vec![InferredExpr {
                    typ: TypeBounds::exact(Type::Named {
                        path: Path::from_name(Name("int".to_string())),
                        args: Vec::new(),
                    }),
                    eff: TypeBounds::exact(Type::Never),
                    ir: ErasedExpr::Lit(Lit::Int("1".to_string())),
                }],
                roots: vec![PrincipalRoot::Expr(0)],
                ..ErasedModule::default()
            },
            refs: RefExportTable::default(),
        };

        let json = serde_json::to_string(&program).expect("serialize erased program");
        let round_tripped: ErasedProgram =
            serde_json::from_str(&json).expect("deserialize erased program");
        assert_eq!(round_tripped, program);
    }
}
