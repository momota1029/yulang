//! subtype constraint を即時伝播する machine。
//!
//! lowering は `PosId <: NegId` を machine に渡すだけで、上下界 table の更新と再伝播はここが持つ。
//! 伝播で増えた下界・上界は event として外へ出し、selection や SCC の別 machine が反応できる。
//!
//! effect row の subtract は subtype bound とは別の事実として保持する。
//! `non_subtracts` のような保護 table は置かず、`SubtractId` の集合を weighted edge として
//! subtype constraint に載せて伝播する。

use std::collections::VecDeque;

use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, SubtractId, Subtractability, TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

/// subtype constraint の伝播 machine。
///
/// `TypeArena`、未処理 queue、変数ごとの上下界、subtract fact、outbox event をまとめて所有する。
/// public entrypoint は work を queue に積んだあと `drain()` する。将来 lowering と並列化する場合も、
/// この queue / event 境界を通信点にできる。
pub struct ConstraintMachine {
    types: TypeArena,
    queue: VecDeque<ConstraintWork>,
    bounds: TypeBounds,
    subtracts: SubtractTable,
    seen: FxHashSet<SubtypeConstraint>,
    events: Vec<ConstraintEvent>,
}

impl ConstraintMachine {
    pub fn new() -> Self {
        Self {
            types: TypeArena::new(),
            queue: VecDeque::new(),
            bounds: TypeBounds::new(),
            subtracts: SubtractTable::new(),
            seen: FxHashSet::default(),
            events: Vec::new(),
        }
    }

    pub fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.types.alloc_pos(pos)
    }

    pub fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.types.alloc_neg(neg)
    }

    pub fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.types.alloc_neu(neu)
    }

    pub fn types(&self) -> &TypeArena {
        &self.types
    }

    pub fn bounds(&self) -> &TypeBounds {
        &self.bounds
    }

    pub fn subtracts(&self) -> &SubtractTable {
        &self.subtracts
    }

    pub fn events(&self) -> &[ConstraintEvent] {
        &self.events
    }

    pub fn take_events(&mut self) -> Vec<ConstraintEvent> {
        std::mem::take(&mut self.events)
    }

    pub fn subtype(&mut self, lower: PosId, upper: NegId) {
        self.weighted_subtype(lower, ConstraintWeights::empty(), upper);
    }

    pub fn weighted_subtype(&mut self, lower: PosId, weights: ConstraintWeights, upper: NegId) {
        self.enqueue_subtype(lower, weights, upper);
        self.drain();
    }

    pub fn subtract_fact(
        &mut self,
        effect: TypeVar,
        id: SubtractId,
        subtractability: Subtractability,
    ) {
        self.queue
            .push_back(ConstraintWork::SubtractFact(QueuedSubtractFact {
                effect,
                fact: SubtractFact {
                    id,
                    subtractability,
                },
            }));
        self.drain();
    }

    pub fn drain(&mut self) {
        while let Some(work) = self.queue.pop_front() {
            self.step(work);
        }
    }

    fn enqueue_subtype(&mut self, lower: PosId, weights: ConstraintWeights, upper: NegId) {
        self.queue
            .push_back(ConstraintWork::Subtype(SubtypeConstraint {
                lower,
                upper,
                weights,
            }));
    }

    fn step(&mut self, work: ConstraintWork) {
        match work {
            ConstraintWork::Subtype(constraint) => self.step_subtype(constraint),
            ConstraintWork::SubtractFact(fact) => {
                let id = fact.fact.id;
                if self.subtracts.record(fact.effect, fact.fact) {
                    self.events.push(ConstraintEvent::SubtractFactAdded {
                        effect: fact.effect,
                        id,
                    });
                }
            }
        }
    }

    fn step_subtype(&mut self, constraint: SubtypeConstraint) {
        if !self.seen.insert(constraint.clone()) {
            return;
        }

        match (
            self.types.pos(constraint.lower).clone(),
            self.types.neg(constraint.upper).clone(),
        ) {
            (Pos::Bot, _) | (_, Neg::Top) => {}
            (Pos::Var(source), Neg::Var(target)) => {
                self.add_lower_bound(target, constraint.lower, constraint.weights.clone());
                self.add_upper_bound(source, constraint.upper, constraint.weights);
            }
            (Pos::Var(source), _) => {
                self.add_upper_bound(source, constraint.upper, constraint.weights);
            }
            (_, Neg::Var(target)) => {
                self.add_lower_bound(target, constraint.lower, constraint.weights);
            }
            (
                Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                },
                Neg::Fun {
                    arg: upper_arg,
                    arg_eff: upper_arg_eff,
                    ret_eff: upper_ret_eff,
                    ret: upper_ret,
                },
            ) => {
                let swapped = constraint.weights.swapped();
                self.enqueue_subtype(upper_arg, swapped.clone(), arg);
                self.enqueue_subtype(upper_arg_eff, swapped, arg_eff);
                self.enqueue_subtype(ret_eff, constraint.weights.clone(), upper_ret_eff);
                self.enqueue_subtype(ret, constraint.weights, upper_ret);
            }
            (Pos::Tuple(lowers), Neg::Tuple(uppers)) if lowers.len() == uppers.len() => {
                for (lower, upper) in lowers.into_iter().zip(uppers) {
                    self.enqueue_subtype(lower, constraint.weights.clone(), upper);
                }
            }
            (Pos::Union(left, right), _) => {
                self.enqueue_subtype(left, constraint.weights.clone(), constraint.upper);
                self.enqueue_subtype(right, constraint.weights, constraint.upper);
            }
            (_, Neg::Intersection(left, right)) => {
                self.enqueue_subtype(constraint.lower, constraint.weights.clone(), left);
                self.enqueue_subtype(constraint.lower, constraint.weights, right);
            }
            _ => {}
        }
    }

    fn add_lower_bound(&mut self, target: TypeVar, pos: PosId, weights: ConstraintWeights) {
        if !self.bounds.add_lower(target, pos, weights.clone()) {
            return;
        }
        self.events.push(ConstraintEvent::LowerBoundAdded {
            var: target,
            bound: pos,
            weights: weights.clone(),
        });

        let uppers = self
            .bounds
            .of(target)
            .map(|bounds| bounds.uppers.clone())
            .unwrap_or_default();
        for upper in uppers {
            self.enqueue_subtype(pos, weights.union(&upper.weights), upper.neg);
        }
    }

    fn add_upper_bound(&mut self, source: TypeVar, neg: NegId, weights: ConstraintWeights) {
        if !self.bounds.add_upper(source, neg, weights.clone()) {
            return;
        }
        self.events.push(ConstraintEvent::UpperBoundAdded {
            var: source,
            bound: neg,
            weights: weights.clone(),
        });

        let lowers = self
            .bounds
            .of(source)
            .map(|bounds| bounds.lowers.clone())
            .unwrap_or_default();
        for lower in lowers {
            self.enqueue_subtype(lower.pos, lower.weights.union(&weights), neg);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// constraint machine から外側へ出る通知。
///
/// selection は lower bound の追加を見て pending site を起こす。SCC や diagnostics も、
/// constraint core に直接入り込まず event を介して反応する。
pub enum ConstraintEvent {
    LowerBoundAdded {
        var: TypeVar,
        bound: PosId,
        weights: ConstraintWeights,
    },
    UpperBoundAdded {
        var: TypeVar,
        bound: NegId,
        weights: ConstraintWeights,
    },
    SubtractFactAdded {
        effect: TypeVar,
        id: SubtractId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ConstraintWork {
    Subtype(SubtypeConstraint),
    SubtractFact(QueuedSubtractFact),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct QueuedSubtractFact {
    effect: TypeVar,
    fact: SubtractFact,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// 型変数ごとの weighted lower / upper bounds。
///
/// 新しい lower が入ると既存 upper へ、新しい upper が入ると既存 lower へ subtype を再投入する。
/// そのとき weight は union し、どの subtract を通ってきた制約かを失わない。
pub struct TypeBounds {
    vars: FxHashMap<TypeVar, VarBounds>,
}

impl TypeBounds {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn of(&self, var: TypeVar) -> Option<&VarBounds> {
        self.vars.get(&var)
    }

    fn add_lower(&mut self, var: TypeVar, pos: PosId, weights: ConstraintWeights) -> bool {
        let bounds = self.vars.entry(var).or_default();
        let bound = WeightedLowerBound { pos, weights };
        if bounds.lowers.contains(&bound) {
            return false;
        }
        bounds.lowers.push(bound);
        true
    }

    fn add_upper(&mut self, var: TypeVar, neg: NegId, weights: ConstraintWeights) -> bool {
        let bounds = self.vars.entry(var).or_default();
        let bound = WeightedUpperBound { neg, weights };
        if bounds.uppers.contains(&bound) {
            return false;
        }
        bounds.uppers.push(bound);
        true
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// 1つの型変数に蓄積された上下界。
///
/// bounds は追加順の Vec で持つ。現段階では探索や差分削除よりも、イベント順と単純な再伝播を優先する。
pub struct VarBounds {
    lowers: Vec<WeightedLowerBound>,
    uppers: Vec<WeightedUpperBound>,
}

impl VarBounds {
    pub fn lowers(&self) -> &[WeightedLowerBound] {
        &self.lowers
    }

    pub fn uppers(&self) -> &[WeightedUpperBound] {
        &self.uppers
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// lower bound と、その bound へ到達するまでに通った subtract weight。
pub struct WeightedLowerBound {
    pub pos: PosId,
    pub weights: ConstraintWeights,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// upper bound と、その bound へ到達するまでに通った subtract weight。
pub struct WeightedUpperBound {
    pub neg: NegId,
    pub weights: ConstraintWeights,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// effect 変数ごとの `S-subtract` fact。
///
/// これは subtype bound ではない。effect row から何を引けるかという事実を独立に持ち、
/// scheme 化や subtract 解釈の段階で読む。
pub struct SubtractTable {
    facts: FxHashMap<TypeVar, Vec<SubtractFact>>,
}

impl SubtractTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn facts(&self, effect: TypeVar) -> &[SubtractFact] {
        self.facts.get(&effect).map(Vec::as_slice).unwrap_or(&[])
    }

    fn record(&mut self, effect: TypeVar, fact: SubtractFact) -> bool {
        let facts = self.facts.entry(effect).or_default();
        if facts.contains(&fact) {
            return false;
        }
        facts.push(fact);
        true
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
/// subtype edge の片側に載る subtract weight。
///
/// 中身は sorted set。集合として扱うことで、同じ `SubtractId` を複数回通っても意味が増えない。
pub struct ConstraintWeight {
    ids: Vec<SubtractId>,
}

impl ConstraintWeight {
    pub fn empty() -> Self {
        Self { ids: Vec::new() }
    }

    pub fn from_ids(ids: impl IntoIterator<Item = SubtractId>) -> Self {
        let mut ids = ids.into_iter().collect::<Vec<_>>();
        ids.sort_by_key(|id| id.0);
        ids.dedup();
        Self { ids }
    }

    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    pub fn contains(&self, id: SubtractId) -> bool {
        self.ids.contains(&id)
    }

    pub fn iter(&self) -> impl Iterator<Item = SubtractId> + '_ {
        self.ids.iter().copied()
    }

    pub fn union(&self, other: &Self) -> Self {
        Self::from_ids(self.iter().chain(other.iter()))
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
/// subtype edge の左右に載る subtract weight。
///
/// 関数引数のように polarity が反転する場所では `swapped()` で左右を入れ替える。
/// bounds の再伝播では `union()` し、経路の情報をまとめる。
pub struct ConstraintWeights {
    pub left: ConstraintWeight,
    pub right: ConstraintWeight,
}

impl ConstraintWeights {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.left.is_empty() && self.right.is_empty()
    }

    pub fn swapped(&self) -> Self {
        Self {
            left: self.right.clone(),
            right: self.left.clone(),
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        Self {
            left: self.left.union(&other.left),
            right: self.right.union(&other.right),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// 1本の weighted subtype constraint。
///
/// `lower <: upper` という直接の要求と、その要求が通ってきた subtract weight を一体で持つ。
pub struct SubtypeConstraint {
    pub lower: PosId,
    pub upper: NegId,
    pub weights: ConstraintWeights,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// 1つの `S-subtract` fact。
///
/// `id` は weight として subtype edge に載る識別子、`subtractability` はその ID が表す引き算の内容。
pub struct SubtractFact {
    pub id: SubtractId,
    pub subtractability: Subtractability,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constraint_weight_is_a_sorted_set() {
        let a = SubtractId(2);
        let b = SubtractId(1);
        let weight = ConstraintWeight::from_ids([a, b, a]);

        assert_eq!(weight.iter().collect::<Vec<_>>(), vec![b, a]);
        assert!(weight.contains(a));
        assert!(weight.contains(b));
    }

    #[test]
    fn constraint_weights_swap_left_and_right() {
        let left = SubtractId(0);
        let right = SubtractId(1);
        let weights = ConstraintWeights {
            left: ConstraintWeight::from_ids([left]),
            right: ConstraintWeight::from_ids([right]),
        };

        let swapped = weights.swapped();
        assert!(swapped.left.contains(right));
        assert!(swapped.right.contains(left));
    }

    #[test]
    fn machine_records_subtract_facts_outside_subtype_bounds() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(0);
        let subtract = SubtractId(1);

        machine.subtract_fact(effect, subtract, Subtractability::All);
        machine.subtract_fact(effect, subtract, Subtractability::All);

        assert_eq!(
            machine.subtracts().facts(effect),
            &[SubtractFact {
                id: subtract,
                subtractability: Subtractability::All
            }]
        );
        assert!(machine.bounds().of(effect).is_none());
        assert_eq!(
            machine.take_events(),
            vec![ConstraintEvent::SubtractFactAdded {
                effect,
                id: subtract
            }]
        );
    }

    #[test]
    fn subtype_to_neg_var_records_weighted_lower_bound() {
        let mut machine = ConstraintMachine::new();
        let target = TypeVar(0);
        let lower = machine.alloc_pos(Pos::Con(vec!["int".into()], vec![]));
        let upper = machine.alloc_neg(Neg::Var(target));
        let subtract = SubtractId(0);
        let weights = ConstraintWeights {
            left: ConstraintWeight::from_ids([subtract]),
            right: ConstraintWeight::empty(),
        };

        machine.weighted_subtype(lower, weights.clone(), upper);

        let bounds = machine.bounds().of(target).expect("target bounds");
        assert_eq!(
            bounds.lowers(),
            &[WeightedLowerBound {
                pos: lower,
                weights: weights.clone()
            }]
        );
        assert!(bounds.uppers().is_empty());
        assert_eq!(
            machine.events(),
            &[ConstraintEvent::LowerBoundAdded {
                var: target,
                bound: lower,
                weights
            }]
        );
    }

    #[test]
    fn pos_var_to_subtype_records_weighted_upper_bound() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Con(vec!["int".into()], vec![]));
        let subtract = SubtractId(0);
        let weights = ConstraintWeights {
            left: ConstraintWeight::empty(),
            right: ConstraintWeight::from_ids([subtract]),
        };

        machine.weighted_subtype(lower, weights.clone(), upper);

        let bounds = machine.bounds().of(source).expect("source bounds");
        assert!(bounds.lowers().is_empty());
        assert_eq!(
            bounds.uppers(),
            &[WeightedUpperBound {
                neg: upper,
                weights
            }]
        );
    }

    #[test]
    fn var_bound_addition_replays_against_opposite_bounds_with_union_weights() {
        let mut machine = ConstraintMachine::new();
        let var = TypeVar(0);
        let lower = machine.alloc_pos(Pos::Con(vec!["int".into()], vec![]));
        let lower_weight = ConstraintWeights {
            left: ConstraintWeight::from_ids([SubtractId(0)]),
            right: ConstraintWeight::empty(),
        };
        let var_neg = machine.alloc_neg(Neg::Var(var));
        machine.weighted_subtype(lower, lower_weight.clone(), var_neg);

        let var_pos = machine.alloc_pos(Pos::Var(var));
        let upper = machine.alloc_neg(Neg::Con(vec!["int".into()], vec![]));
        let upper_weight = ConstraintWeights {
            left: ConstraintWeight::empty(),
            right: ConstraintWeight::from_ids([SubtractId(1)]),
        };
        machine.weighted_subtype(var_pos, upper_weight.clone(), upper);

        assert!(machine.seen.contains(&SubtypeConstraint {
            lower,
            upper,
            weights: lower_weight.union(&upper_weight),
        }));
    }

    #[test]
    fn function_arguments_propagate_with_swapped_weights() {
        let mut machine = ConstraintMachine::new();
        let lhs_arg = machine.alloc_neg(Neg::Con(vec!["lhs_arg".into()], vec![]));
        let lhs_arg_eff = machine.alloc_neg(Neg::Con(vec!["lhs_arg_eff".into()], vec![]));
        let lhs_ret_eff = machine.alloc_pos(Pos::Con(vec!["lhs_ret_eff".into()], vec![]));
        let lhs_ret = machine.alloc_pos(Pos::Con(vec!["lhs_ret".into()], vec![]));
        let lower = machine.alloc_pos(Pos::Fun {
            arg: lhs_arg,
            arg_eff: lhs_arg_eff,
            ret_eff: lhs_ret_eff,
            ret: lhs_ret,
        });

        let rhs_arg = machine.alloc_pos(Pos::Con(vec!["rhs_arg".into()], vec![]));
        let rhs_arg_eff = machine.alloc_pos(Pos::Con(vec!["rhs_arg_eff".into()], vec![]));
        let rhs_ret_eff = machine.alloc_neg(Neg::Con(vec!["rhs_ret_eff".into()], vec![]));
        let rhs_ret = machine.alloc_neg(Neg::Con(vec!["rhs_ret".into()], vec![]));
        let upper = machine.alloc_neg(Neg::Fun {
            arg: rhs_arg,
            arg_eff: rhs_arg_eff,
            ret_eff: rhs_ret_eff,
            ret: rhs_ret,
        });
        let weights = ConstraintWeights {
            left: ConstraintWeight::from_ids([SubtractId(0)]),
            right: ConstraintWeight::from_ids([SubtractId(1)]),
        };

        machine.weighted_subtype(lower, weights.clone(), upper);

        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: rhs_arg,
            upper: lhs_arg,
            weights: weights.swapped(),
        }));
        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: lhs_ret,
            upper: rhs_ret,
            weights,
        }));
    }
}
