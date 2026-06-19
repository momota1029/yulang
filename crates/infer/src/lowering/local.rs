//! Local binding and lambda-shape state shared by expression lowering modules.

use super::*;

#[derive(Clone)]
pub(super) struct LocalBinding {
    pub(super) name: Name,
    pub(super) def: DefId,
    pub(super) value: TypeVar,
    pub(super) effect: Option<LocalEffect>,
    pub(super) call_return_effect: LocalCallReturnEffect,
    pub(super) unannotated_call_frame: Option<usize>,
    pub(super) recursive_effect_passthrough: bool,
    pub(super) scheme: Option<Scheme>,
}

#[derive(Clone)]
pub(super) struct SubSyntaxScope {
    pub(super) bare_return: SubReturnTarget,
    pub(super) labels: Vec<SubLabelReturnTarget>,
}

#[derive(Clone)]
pub(super) struct SubReturnTarget {
    pub(super) label: String,
    pub(super) def: DefId,
}

#[derive(Clone)]
pub(super) struct SubLabelReturnTarget {
    pub(super) label_def: DefId,
    pub(super) target: SubReturnTarget,
}

#[derive(Clone)]
pub(super) enum LocalEffect {
    Var(TypeVar),
    /// The ordinary effect seen by `x` and the stack-protected view used by
    /// `catch x:` are deliberately separate. Forwarding `x` must keep the full
    /// effect, while handler lowering may inspect `inner` through `weight`.
    Stack {
        effect: TypeVar,
        inner: TypeVar,
        weight: StackWeight,
    },
}

impl LocalEffect {
    pub(super) fn collect_vars(&self, vars: &mut FxHashSet<TypeVar>) {
        match self {
            LocalEffect::Var(effect) => {
                vars.insert(*effect);
            }
            LocalEffect::Stack { effect, inner, .. } => {
                vars.insert(*effect);
                vars.insert(*inner);
            }
        }
    }
}

pub(super) struct LoweredLocalStmt {
    pub(super) stmt: Stmt,
    pub(super) effect: TypeVar,
}

#[derive(Clone)]
pub(super) struct PreparedVarPatternBinding {
    pub(super) source: Name,
    pub(super) init_name: Name,
    pub(super) reference_name: Name,
    pub(super) local_act: SyntheticVarActUse,
}

pub(super) struct ActiveVarPatternBindings {
    pub(super) reference_stmts: Vec<LoweredLocalStmt>,
    pub(super) run_inputs: Vec<ActiveVarPatternRunInput>,
}

pub(super) struct ActiveVarPatternRunInput {
    pub(super) local_act: SyntheticVarActUse,
    pub(super) init_name: Name,
    pub(super) init_value: TypeVar,
}

pub(super) struct ApplicationReturnEffect {
    pub(super) upper: NegId,
    pub(super) lower: PosId,
}

#[derive(Clone)]
pub(super) struct LoweredLambdaParam {
    pub(super) pat: PatId,
    pub(super) value: TypeVar,
    pub(super) annotation: LambdaPatternAnnotation,
}

#[derive(Clone)]
pub(super) struct DefinedLambdaSkeleton {
    pub(super) body_effect: TypeVar,
    pub(super) body_value: TypeVar,
    pub(super) layers: Vec<DefinedLambdaSkeletonLayer>,
}

#[derive(Clone)]
pub(super) struct DefinedLambdaSkeletonLayer {
    pub(super) function_effect: TypeVar,
    pub(super) function_value: TypeVar,
    pub(super) output_effect: TypeVar,
    pub(super) output_value: TypeVar,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum SkeletonPredicateMode {
    All,
    KnownBeforeBody,
    NonEmptyOnly,
}

impl SkeletonPredicateMode {
    pub(super) fn connects_empty_predicate(self, param: &LoweredLambdaParam) -> bool {
        match self {
            SkeletonPredicateMode::All => true,
            SkeletonPredicateMode::KnownBeforeBody => {
                param.annotation.call_return_effect == LocalCallReturnEffect::Annotated
            }
            SkeletonPredicateMode::NonEmptyOnly => false,
        }
    }
}

#[derive(Clone)]
pub(super) struct ActiveDefinedLambdaSkeleton {
    pub(super) before_frames: usize,
    pub(super) params: Vec<LoweredLambdaParam>,
    pub(super) skeleton: DefinedLambdaSkeleton,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct DefinedSkeletonPredicateKey {
    pub(super) output_effect: TypeVar,
    pub(super) output_value: TypeVar,
    pub(super) current_effect: TypeVar,
    pub(super) current_value: TypeVar,
    pub(super) subtracts: Vec<StackWeight>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LocalCallReturnEffect {
    Unannotated,
    Annotated,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LambdaScope {
    Defined,
    Anonymous,
}

pub(super) struct PipeArg {
    pub(super) expr: Computation,
}

#[derive(Clone)]
pub(super) struct FunctionPredicateFrame {
    pub(super) scope: LambdaScope,
    pub(super) subtracts: Vec<StackWeight>,
    pub(super) unannotated_call_subtract: Option<SubtractId>,
}

impl FunctionPredicateFrame {
    pub(super) fn new(scope: LambdaScope) -> Self {
        Self {
            scope,
            subtracts: Vec::new(),
            unannotated_call_subtract: None,
        }
    }
}

#[derive(Clone)]
pub(super) struct LambdaPatternAnnotation {
    pub(super) arg_eff: NegId,
    pub(super) skeleton_arg_eff: NegId,
    pub(super) local_effect: Option<LocalEffect>,
    pub(super) subtracts: Vec<StackWeight>,
    pub(super) call_return_effect: LocalCallReturnEffect,
}

pub(super) fn collect_pos_id_vars(types: &TypeArena, id: PosId, out: &mut FxHashSet<TypeVar>) {
    match types.pos(id) {
        Pos::Bot => {}
        Pos::Var(var) => {
            out.insert(*var);
        }
        Pos::Con(_, args) => collect_neu_ids_vars(types, args, out),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neg_id_vars(types, *arg, out);
            collect_neg_id_vars(types, *arg_eff, out);
            collect_pos_id_vars(types, *ret_eff, out);
            collect_pos_id_vars(types, *ret, out);
        }
        Pos::Record(fields) => {
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
        }
        Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { tail, fields } => {
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
            collect_pos_id_vars(types, *tail, out);
        }
        Pos::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_pos_id_vars(types, *payload, out);
                }
            }
        }
        Pos::Tuple(items) | Pos::Row(items) => {
            for item in items {
                collect_pos_id_vars(types, *item, out);
            }
        }
        Pos::Stack { inner, .. } => collect_pos_id_vars(types, *inner, out),
        Pos::NonSubtract(pos, _) => collect_pos_id_vars(types, *pos, out),
        Pos::Union(lhs, rhs) => {
            collect_pos_id_vars(types, *lhs, out);
            collect_pos_id_vars(types, *rhs, out);
        }
    }
}

pub(super) fn collect_neg_id_vars(types: &TypeArena, id: NegId, out: &mut FxHashSet<TypeVar>) {
    match types.neg(id) {
        Neg::Top | Neg::Bot => {}
        Neg::Var(var) => {
            out.insert(*var);
        }
        Neg::Con(_, args) => collect_neu_ids_vars(types, args, out),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_pos_id_vars(types, *arg, out);
            collect_pos_id_vars(types, *arg_eff, out);
            collect_neg_id_vars(types, *ret_eff, out);
            collect_neg_id_vars(types, *ret, out);
        }
        Neg::Record(fields) => {
            for field in fields {
                collect_neg_id_vars(types, field.value, out);
            }
        }
        Neg::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_neg_id_vars(types, *payload, out);
                }
            }
        }
        Neg::Tuple(items) => {
            for item in items {
                collect_neg_id_vars(types, *item, out);
            }
        }
        Neg::Row(items, tail) => {
            for item in items {
                collect_neg_id_vars(types, *item, out);
            }
            collect_neg_id_vars(types, *tail, out);
        }
        Neg::Stack { inner, .. } => collect_neg_id_vars(types, *inner, out),
        Neg::Intersection(lhs, rhs) => {
            collect_neg_id_vars(types, *lhs, out);
            collect_neg_id_vars(types, *rhs, out);
        }
    }
}

fn collect_neu_ids_vars(types: &TypeArena, ids: &[NeuId], out: &mut FxHashSet<TypeVar>) {
    for id in ids {
        collect_neu_id_vars(types, *id, out);
    }
}

fn collect_neu_id_vars(types: &TypeArena, id: NeuId, out: &mut FxHashSet<TypeVar>) {
    match types.neu(id) {
        Neu::Bounds(lower, upper) => {
            collect_pos_id_vars(types, *lower, out);
            collect_neg_id_vars(types, *upper, out);
        }
        Neu::Con(_, args) => collect_neu_ids_vars(types, args, out),
        Neu::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neu_id_vars(types, *arg, out);
            collect_neu_id_vars(types, *arg_eff, out);
            collect_neu_id_vars(types, *ret_eff, out);
            collect_neu_id_vars(types, *ret, out);
        }
        Neu::Record(fields) => {
            for field in fields {
                collect_neu_id_vars(types, field.value, out);
            }
        }
        Neu::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_neu_id_vars(types, *payload, out);
                }
            }
        }
        Neu::Tuple(items) => collect_neu_ids_vars(types, items, out),
    }
}
