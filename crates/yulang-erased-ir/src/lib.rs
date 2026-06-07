//! Type-erased inference output IR.
//!
//! This crate owns the IR boundary that monomorphization is allowed to read.
//! Expression nodes represent value structure only: they do not carry inferred
//! node types, effects, annotation evidence, apply evidence, or coercion nodes.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

pub mod types;

pub use types::{
    EffectVar, PrimitiveOp, RecordField, RecordSpread, RecordType, RoleRequirement,
    RoleRequirementArg, Scheme, Type, TypeArg, TypeBounds, TypeSubstitution, TypeVar, VariantCase,
    VariantType,
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
    pub hygiene: HygieneExportTable,
}

impl ErasedProgram {
    pub fn ref_coverage(&self) -> RefCoverageReport {
        let mut used = BTreeSet::new();
        collect_module_refs(&self.module, &mut used);

        let mut covered = BTreeSet::new();
        let mut conflicting = BTreeSet::new();
        for ref_id in self.refs.direct.keys().copied() {
            if !covered.insert(ref_id) {
                conflicting.insert(ref_id);
            }
        }
        for ref_id in self.refs.resolved_typeclass.keys().copied() {
            if !covered.insert(ref_id) {
                conflicting.insert(ref_id);
            }
        }
        for obligation in self.typeclass_obligations() {
            if !covered.insert(obligation.ref_id) {
                conflicting.insert(obligation.ref_id);
            }
        }

        RefCoverageReport {
            uncovered: used.difference(&covered).copied().collect(),
            conflicting: conflicting.into_iter().collect(),
        }
    }

    pub fn typeclass_obligations(&self) -> impl Iterator<Item = &TypeClassObligation> {
        self.module
            .bindings
            .iter()
            .flat_map(|binding| binding.scheme.typeclass_obligations.iter())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct RefCoverageReport {
    pub uncovered: Vec<RefId>,
    pub conflicting: Vec<RefId>,
}

impl RefCoverageReport {
    pub fn is_clean(&self) -> bool {
        self.uncovered.is_empty() && self.conflicting.is_empty()
    }
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
    pub def: DefId,
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

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct HygieneExportTable {
    pub lambda_params: BTreeMap<DefId, LambdaParamHygiene>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LambdaParamHygiene {
    pub effect_boundary: Option<ParamEffectBoundary>,
    pub function_allowed_effects: Option<FunctionAllowedEffectsBoundary>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ParamEffectBoundary {
    Wildcard,
    Region(Name),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FunctionAllowedEffectsBoundary {
    Wildcard,
    Effects(Vec<Path>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolvedTypeClassRef {
    pub class: Path,
    pub member: DefId,
    pub impl_def: Option<DefId>,
    pub impl_member: DefId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeClassObligation {
    pub ref_id: RefId,
    pub class: Path,
    pub member: DefId,
    pub args: Vec<Type>,
    pub associated: Vec<AssociatedTypeConstraint>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
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

fn collect_module_refs(module: &ErasedModule, out: &mut BTreeSet<RefId>) {
    for binding in &module.bindings {
        collect_expr_refs(&binding.body.ir, out);
    }
    for root in &module.root_exprs {
        collect_expr_refs(&root.ir, out);
    }
}

fn collect_expr_refs(expr: &ErasedExpr, out: &mut BTreeSet<RefId>) {
    match expr {
        ErasedExpr::Ref(ref_id) => {
            out.insert(*ref_id);
        }
        ErasedExpr::Lambda { body, .. }
        | ErasedExpr::BindHere { expr: body }
        | ErasedExpr::Pack { expr: body, .. } => collect_expr_refs(body, out),
        ErasedExpr::Apply { callee, arg } => {
            collect_expr_refs(callee, out);
            collect_expr_refs(arg, out);
        }
        ErasedExpr::RefSet { reference, value } => {
            collect_expr_refs(reference, out);
            collect_expr_refs(value, out);
        }
        ErasedExpr::Tuple(items) => {
            for item in items {
                collect_expr_refs(item, out);
            }
        }
        ErasedExpr::Record { fields, spread } => {
            for field in fields {
                collect_expr_refs(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_expr_refs(expr, out);
                    }
                }
            }
        }
        ErasedExpr::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_refs(value, out);
            }
        }
        ErasedExpr::Select { base, .. } => collect_expr_refs(base, out),
        ErasedExpr::Match { scrutinee, arms } => {
            collect_expr_refs(scrutinee, out);
            for arm in arms {
                collect_pattern_refs(&arm.pattern, out);
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ErasedExpr::Handle { body, arms } => {
            collect_expr_refs(body, out);
            for arm in arms {
                collect_pattern_refs(&arm.payload, out);
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ErasedExpr::Block(block) => collect_block_refs(block, out),
        ErasedExpr::Def(_) | ErasedExpr::PrimitiveOp(_) | ErasedExpr::Lit(_) => {}
    }
}

fn collect_block_refs(block: &ErasedBlock, out: &mut BTreeSet<RefId>) {
    for stmt in &block.stmts {
        match stmt {
            ErasedStmt::Let { pattern, value } => {
                collect_pattern_refs(pattern, out);
                collect_expr_refs(value, out);
            }
            ErasedStmt::Expr(expr) => collect_expr_refs(expr, out),
            ErasedStmt::Module { body, .. } => collect_block_refs(body, out),
        }
    }
    if let Some(tail) = &block.tail {
        collect_expr_refs(tail, out);
    }
}

fn collect_pattern_refs(pattern: &Pattern, out: &mut BTreeSet<RefId>) {
    match pattern {
        Pattern::Tuple(items) => {
            for item in items {
                collect_pattern_refs(item, out);
            }
        }
        Pattern::Or { left, right } => {
            collect_pattern_refs(left, out);
            collect_pattern_refs(right, out);
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix {
                collect_pattern_refs(item, out);
            }
            if let Some(spread) = spread {
                collect_pattern_refs(spread, out);
            }
            for item in suffix {
                collect_pattern_refs(item, out);
            }
        }
        Pattern::Record { fields, spread } => {
            for field in fields {
                collect_pattern_refs(&field.pattern, out);
                if let Some(default) = &field.default {
                    collect_expr_refs(default, out);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_refs(pattern, out);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_refs(value, out);
            }
        }
        Pattern::Constructor { ref_id, payload } => {
            out.insert(*ref_id);
            if let Some(payload) = payload {
                collect_pattern_refs(payload, out);
            }
        }
        Pattern::As { pattern, .. } => collect_pattern_refs(pattern, out),
        Pattern::Wildcard | Pattern::Bind(_) | Pattern::Lit(_) | Pattern::UnresolvedName(_) => {}
    }
}

#[cfg(test)]
mod coverage_tests {
    use super::*;

    #[test]
    fn ref_coverage_accepts_direct_resolved_and_obligation_refs() {
        let mut program = ErasedProgram::default();
        program.refs.direct.insert(RefId(1), DefId(10));
        program.refs.resolved_typeclass.insert(
            RefId(2),
            ResolvedTypeClassRef {
                class: Path::from_name(Name("Display".to_string())),
                member: DefId(20),
                impl_def: Some(DefId(21)),
                impl_member: DefId(22),
            },
        );
        program.module.bindings.push(binding_with_ref(
            "use_refs",
            ErasedExpr::Tuple(vec![
                ErasedExpr::Ref(RefId(1)),
                ErasedExpr::Ref(RefId(2)),
                ErasedExpr::Ref(RefId(3)),
            ]),
            vec![TypeClassObligation {
                ref_id: RefId(3),
                class: Path::from_name(Name("Show".to_string())),
                member: DefId(30),
                args: Vec::new(),
                associated: Vec::new(),
            }],
        ));

        assert!(program.ref_coverage().is_clean());
    }

    #[test]
    fn ref_coverage_reports_uncovered_and_conflicting_refs() {
        let mut program = ErasedProgram::default();
        program.refs.direct.insert(RefId(1), DefId(10));
        program.refs.resolved_typeclass.insert(
            RefId(1),
            ResolvedTypeClassRef {
                class: Path::from_name(Name("Display".to_string())),
                member: DefId(20),
                impl_def: Some(DefId(21)),
                impl_member: DefId(22),
            },
        );
        program
            .module
            .root_exprs
            .push(inferred_expr(ErasedExpr::Ref(RefId(9))));

        let coverage = program.ref_coverage();
        assert_eq!(coverage.uncovered, vec![RefId(9)]);
        assert_eq!(coverage.conflicting, vec![RefId(1)]);
    }

    fn binding_with_ref(
        name: &str,
        ir: ErasedExpr,
        obligations: Vec<TypeClassObligation>,
    ) -> InferredBinding {
        InferredBinding {
            def: DefId(0),
            name: Path::from_name(Name(name.to_string())),
            scheme: Scheme {
                body: Type::Unknown,
                quantified_types: Vec::new(),
                quantified_effects: Vec::new(),
                quantified_refs: obligations
                    .iter()
                    .map(|obligation| obligation.ref_id)
                    .collect(),
                typeclass_obligations: obligations,
                requirements: Vec::new(),
            },
            body: inferred_expr(ir),
        }
    }

    fn inferred_expr(ir: ErasedExpr) -> InferredExpr {
        InferredExpr {
            typ: TypeBounds::default(),
            eff: TypeBounds::default(),
            ir,
        }
    }
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
            hygiene: HygieneExportTable::default(),
        };

        let json = serde_json::to_string(&program).expect("serialize erased program");
        let round_tripped: ErasedProgram =
            serde_json::from_str(&json).expect("deserialize erased program");
        assert_eq!(round_tripped, program);
    }
}
