use crate::graph::CoreGraphView;
use crate::names::{Name, Path};
use crate::types::{RecordField, RoleRequirement, Scheme, Type, TypeVar};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct PrincipalModule {
    pub path: Path,
    pub bindings: Vec<PrincipalBinding>,
    pub root_exprs: Vec<Expr>,
    pub roots: Vec<PrincipalRoot>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CoreProgram {
    pub program: PrincipalModule,
    pub graph: CoreGraphView,
    pub evidence: PrincipalEvidence,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct PrincipalEvidence {
    pub expected_edges: Vec<ExpectedEdgeEvidence>,
    pub expected_adapter_edges: Vec<ExpectedAdapterEdgeEvidence>,
    pub derived_expected_edges: Vec<DerivedExpectedEdgeEvidence>,
}

impl PrincipalEvidence {
    pub fn expected_edge(&self, id: u32) -> Option<&ExpectedEdgeEvidence> {
        self.expected_edges.iter().find(|edge| edge.id == id)
    }

    pub fn expected_adapter_edge(&self, id: u32) -> Option<&ExpectedAdapterEdgeEvidence> {
        self.expected_adapter_edges
            .iter()
            .find(|edge| edge.id == id)
    }

    pub fn derived_expected_edges_for_parent(
        &self,
        parent: u32,
    ) -> impl Iterator<Item = &DerivedExpectedEdgeEvidence> {
        self.derived_expected_edges
            .iter()
            .filter(move |edge| edge.parent == parent)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpectedEdgeEvidence {
    pub id: u32,
    pub kind: ExpectedEdgeKind,
    pub source_range: Option<SourceRange>,
    pub actual: crate::types::TypeBounds,
    pub expected: crate::types::TypeBounds,
    pub actual_effect: Option<crate::types::TypeBounds>,
    pub expected_effect: Option<crate::types::TypeBounds>,
    pub closed: bool,
    pub informative: bool,
    pub runtime_usable: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExpectedEdgeKind {
    IfCondition,
    IfBranch,
    MatchGuard,
    MatchBranch,
    CatchGuard,
    CatchBranch,
    ApplicationCallee,
    ApplicationArgument,
    Annotation,
    RecordField,
    VariantPayload,
    AssignmentValue,
    RepresentationCoerce,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpectedAdapterEdgeEvidence {
    pub id: u32,
    pub source_expected_edge: Option<u32>,
    pub kind: ExpectedAdapterEdgeKind,
    pub source_range: Option<SourceRange>,
    pub actual_value: Option<crate::types::TypeBounds>,
    pub expected_value: Option<crate::types::TypeBounds>,
    pub actual_effect: Option<crate::types::TypeBounds>,
    pub expected_effect: Option<crate::types::TypeBounds>,
    pub closed: bool,
    pub informative: bool,
    pub runtime_usable: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceRange {
    pub start: u32,
    pub end: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExpectedAdapterEdgeKind {
    EffectOperationArgument,
    ValueToThunk,
    ThunkToValue,
    BindHere,
    HandlerResidual,
    HandlerReturn,
    ResumeArgument,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivedExpectedEdgeEvidence {
    pub parent: u32,
    pub kind: DerivedExpectedEdgeKind,
    pub polarity: EdgePolarity,
    pub path: Vec<EdgePathSegment>,
    pub actual: crate::types::TypeBounds,
    pub expected: crate::types::TypeBounds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EdgePolarity {
    Covariant,
    Contravariant,
    Invariant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DerivedExpectedEdgeKind {
    RecordField,
    TupleItem,
    VariantPayload,
    FunctionParam,
    FunctionReturn,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum EdgePathSegment {
    Field(Name),
    TupleIndex(usize),
    VariantCase(Name),
    PayloadIndex(usize),
    FunctionParam,
    FunctionReturn,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ParamEffectAnnotation {
    Wildcard,
    Region(Name),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FunctionSigAllowedEffects {
    Wildcard,
    Effects(Vec<Path>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipalBinding {
    pub name: Path,
    pub scheme: Scheme,
    pub body: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrimitiveOp {
    BoolNot,
    BoolEq,
    ListEmpty,
    ListSingleton,
    ListLen,
    ListMerge,
    ListIndex,
    ListIndexRange,
    ListSplice,
    ListIndexRangeRaw,
    ListSpliceRaw,
    ListViewRaw,
    StringLen,
    StringIndex,
    StringIndexRange,
    StringSplice,
    StringIndexRangeRaw,
    StringSpliceRaw,
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntEq,
    IntLt,
    IntLe,
    IntGt,
    IntGe,
    FloatAdd,
    FloatSub,
    FloatMul,
    FloatDiv,
    FloatEq,
    FloatLt,
    FloatLe,
    FloatGt,
    FloatGe,
    StringConcat,
    IntToString,
    IntToHex,
    IntToUpperHex,
    FloatToString,
    BoolToString,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApplyEvidence {
    pub callee_source_edge: Option<u32>,
    pub arg_source_edge: Option<u32>,
    pub callee: crate::types::TypeBounds,
    pub expected_callee: Option<crate::types::TypeBounds>,
    pub arg: crate::types::TypeBounds,
    pub expected_arg: Option<crate::types::TypeBounds>,
    pub result: crate::types::TypeBounds,
    pub principal_callee: Option<crate::types::Type>,
    pub substitutions: Vec<crate::types::TypeSubstitution>,
    pub substitution_candidates: Vec<PrincipalSubstitutionCandidate>,
    pub role_method: bool,
    pub principal_elaboration: Option<PrincipalElaborationPlan>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipalElaborationPlan {
    pub target: Option<Path>,
    pub principal_callee: Type,
    pub substitutions: Vec<crate::types::TypeSubstitution>,
    pub args: Vec<PrincipalElaborationArg>,
    pub result: PrincipalElaborationResult,
    pub adapters: Vec<PrincipalAdapterHole>,
    pub complete: bool,
    pub incomplete_reasons: Vec<PrincipalElaborationIncompleteReason>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipalElaborationArg {
    pub index: usize,
    pub intrinsic: crate::types::TypeBounds,
    pub contextual: Option<crate::types::TypeBounds>,
    pub expected_runtime: Option<Type>,
    pub source_edge: Option<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipalElaborationResult {
    pub intrinsic: crate::types::TypeBounds,
    pub contextual: Option<crate::types::TypeBounds>,
    pub expected_runtime: Option<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipalAdapterHole {
    pub kind: PrincipalAdapterKind,
    pub source_edge: Option<u32>,
    pub actual: Type,
    pub expected: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrincipalAdapterKind {
    Coerce,
    ValueToThunk,
    ThunkToValue,
    BindHere,
    HandlerResidual,
    HandlerReturn,
    ResumeArgument,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrincipalElaborationIncompleteReason {
    MissingPrincipalCallee,
    MissingTarget,
    MissingSubstitution(TypeVar),
    ConflictingSubstitution(TypeVar),
    OpenCandidate(TypeVar),
    OpenArgType(usize),
    OpenResultType,
    MissingAdapterHole(PrincipalAdapterKind),
    HandlerBoundaryWithoutPlan,
    AmbiguousRoleImpl,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipalSubstitutionCandidate {
    pub var: TypeVar,
    pub relation: PrincipalCandidateRelation,
    pub ty: Type,
    pub source_edge: Option<u32>,
    pub path: Vec<PrincipalSlotPathSegment>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrincipalCandidateRelation {
    Lower,
    Upper,
    Exact,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrincipalSlotPathSegment {
    Callee,
    Arg,
    Result,
    Field(Name),
    TupleIndex(usize),
    VariantCase(Name),
    PayloadIndex(usize),
    FunctionParam,
    FunctionReturn,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct JoinEvidence {
    pub result: crate::types::TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoerceEvidence {
    pub source_edge: Option<u32>,
    pub actual: crate::types::TypeBounds,
    pub expected: crate::types::TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrincipalRoot {
    Binding(Path),
    Expr(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct Module {
    pub path: Path,
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Binding {
    pub visibility: BindingVisibility,
    pub name: Name,
    pub scheme: Scheme,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoleDecl {
    pub name: Path,
    pub params: Vec<TypeVar>,
    pub associated_types: Vec<Name>,
    pub members: Vec<RoleMember>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImplDecl {
    pub role: Path,
    pub inputs: Vec<Type>,
    pub requirements: Vec<RoleRequirement>,
    pub associated_types: Vec<RecordField<Type>>,
    pub members: Vec<ImplMember>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Item {
    Binding(Binding),
    Role(RoleDecl),
    Impl(ImplDecl),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expr {
    Var(Path),
    PrimitiveOp(PrimitiveOp),
    Lit(Lit),
    Lambda {
        param: Name,
        param_effect_annotation: Option<ParamEffectAnnotation>,
        param_function_allowed_effects: Option<FunctionSigAllowedEffects>,
        body: Box<Expr>,
    },
    Apply {
        callee: Box<Expr>,
        arg: Box<Expr>,
        evidence: Option<ApplyEvidence>,
    },
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
        evidence: Option<JoinEvidence>,
    },
    Tuple(Vec<Expr>),
    Record {
        fields: Vec<RecordExprField>,
        spread: Option<RecordSpreadExpr>,
    },
    Variant {
        tag: Name,
        value: Option<Box<Expr>>,
    },
    Select {
        base: Box<Expr>,
        field: Name,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        evidence: Option<JoinEvidence>,
    },
    Block {
        stmts: Vec<Stmt>,
        tail: Option<Box<Expr>>,
    },
    Handle {
        body: Box<Expr>,
        arms: Vec<HandleArm>,
        evidence: Option<JoinEvidence>,
    },
    Coerce {
        expr: Box<Expr>,
        evidence: Option<CoerceEvidence>,
    },
    Pack {
        var: TypeVar,
        expr: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pattern {
    Wildcard,
    Bind(Name),
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
    Or {
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    As {
        pattern: Box<Pattern>,
        name: Name,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoleMember {
    pub name: Name,
    pub scheme: Scheme,
    pub has_receiver: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImplMember {
    pub name: Name,
    pub body: Binding,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordExprField {
    pub name: Name,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecordSpreadExpr {
    Head(Box<Expr>),
    Tail(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordPatternField {
    pub name: Name,
    pub pattern: Pattern,
    pub default: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecordSpreadPattern {
    Head(Box<Pattern>),
    Tail(Box<Pattern>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Stmt {
    Let { pattern: Pattern, value: Expr },
    Expr(Expr),
    Module { def: Path, body: Box<Expr> },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HandleArm {
    pub effect: Path,
    pub payload: Pattern,
    pub resume: Option<Name>,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BindingVisibility {
    Public,
    Private,
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
    fn core_program_round_trips_through_json() {
        let program = CoreProgram {
            program: PrincipalModule {
                path: Path::new(vec![Name("std".to_string())]),
                bindings: vec![PrincipalBinding {
                    name: Path::new(vec![Name("std".to_string()), Name("one".to_string())]),
                    scheme: Scheme {
                        requirements: Vec::new(),
                        body: Type::Named {
                            path: Path::new(vec![Name("int".to_string())]),
                            args: Vec::new(),
                        },
                    },
                    body: Expr::Lit(Lit::Int("1".to_string())),
                }],
                root_exprs: Vec::new(),
                roots: vec![PrincipalRoot::Binding(Path::new(vec![
                    Name("std".to_string()),
                    Name("one".to_string()),
                ]))],
            },
            graph: CoreGraphView::default(),
            evidence: PrincipalEvidence::default(),
        };

        let json = serde_json::to_string(&program).expect("serialize core program");
        let round_tripped: CoreProgram =
            serde_json::from_str(&json).expect("deserialize core program");
        assert_eq!(round_tripped, program);
    }
}
