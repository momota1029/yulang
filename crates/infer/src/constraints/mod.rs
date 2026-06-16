//! subtype constraint を即時伝播する machine。
//!
//! lowering は `PosId <: NegId` を machine に渡すだけで、上下界 table の更新と再伝播はここが持つ。
//! 伝播で増えた下界・上界は event として外へ出し、selection や SCC の別 machine が反応できる。
//!
//! effect row の subtraction は `stack(T, @S)` と weighted edge として表す。
//! subtract fact table は注釈・データ宣言由来の stack id を記録し、generalize の pruning 入力にする。

mod machine;
mod row_effect;
#[cfg(test)]
mod tests;
mod trace;

use std::collections::VecDeque;

use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, StackWeight, SubtractId, Subtractability,
    TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use trace::{
    ConstraintDrainTrace, trace_bound_replay_progress, trace_bound_replay_start, trace_var_bounds,
};

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
    levels: TypeLevels,
    next_internal_type_var: u32,
    row_residuals: FxHashMap<RowResidualKey, TypeVar>,
    declared_subtracts: FxHashSet<SubtractId>,
    effect_family_paths: FxHashSet<Vec<String>>,
    pre_pop_effect_families: FxHashMap<TypeVar, Vec<ConstraintEffectFamily>>,
    seen: FxHashSet<SubtypeConstraint>,
    var_var_seen: FxHashSet<VarVarConstraint>,
    events: Vec<ConstraintEvent>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// let / lambda nesting の深さ。
///
/// root level より深い変数が浅い変数の bound に入ると、bound 登録前の extrusion で浅い level へ
/// 老化させる。未登録の手書き `TypeVar` は root として扱う。
pub struct TypeLevel(u32);

impl TypeLevel {
    pub fn root() -> Self {
        Self(0)
    }

    pub fn secondary() -> Self {
        Self(u32::MAX)
    }

    pub fn child(self) -> Self {
        Self(self.0.saturating_add(1))
    }

    pub fn depth(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct TypeLevels {
    vars: FxHashMap<TypeVar, TypeLevel>,
    births: FxHashMap<TypeVar, TypeLevel>,
}

impl TypeLevels {
    fn new() -> Self {
        Self::default()
    }

    fn register(&mut self, var: TypeVar, level: TypeLevel) {
        self.vars.entry(var).or_insert(level);
        self.births.entry(var).or_insert(level);
    }

    fn level_of(&self, var: TypeVar) -> TypeLevel {
        self.vars.get(&var).copied().unwrap_or_else(TypeLevel::root)
    }

    fn birth_level_of(&self, var: TypeVar) -> TypeLevel {
        self.births
            .get(&var)
            .copied()
            .unwrap_or_else(TypeLevel::root)
    }

    fn lower_to(&mut self, var: TypeVar, target: TypeLevel) {
        let level = self.vars.entry(var).or_insert_with(TypeLevel::root);
        if target < *level {
            *level = target;
        }
    }
}

#[derive(Debug)]
struct ExtrudeCtx {
    target: TypeLevel,
    visited: FxHashSet<TypeVar>,
}

impl ExtrudeCtx {
    fn new(target: TypeLevel) -> Self {
        Self {
            target,
            visited: FxHashSet::default(),
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
    NominalCastNeeded {
        lower: PosId,
        upper: NegId,
        source: Vec<String>,
        target: Vec<String>,
        weights: ConstraintWeights,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RowResidualKey {
    source: TypeVar,
    retained_families: Vec<EffectFamily>,
    weight: StackWeight,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// 型変数ごとの weighted lower / upper bounds。
///
/// 新しい lower が入ると既存 upper へ、新しい upper が入ると既存 lower へ subtype を再投入する。
/// 同じ型境界でも重みが違えば別の不等式なので、bounds 側では合成せず exact dedup だけを行う。
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
        if !bounds.lower_seen.insert(bound.clone()) {
            return false;
        }
        bounds.lowers.push(bound);
        true
    }

    fn add_upper(&mut self, var: TypeVar, neg: NegId, weights: ConstraintWeights) -> bool {
        let bounds = self.vars.entry(var).or_default();
        let bound = WeightedUpperBound { neg, weights };
        if !bounds.upper_seen.insert(bound.clone()) {
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
    lower_seen: FxHashSet<WeightedLowerBound>,
    upper_seen: FxHashSet<WeightedUpperBound>,
}

impl VarBounds {
    pub fn lowers(&self) -> &[WeightedLowerBound] {
        &self.lowers
    }

    pub fn uppers(&self) -> &[WeightedUpperBound] {
        &self.uppers
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// lower bound と、その bound へ到達するまでに通った subtract weight。
pub struct WeightedLowerBound {
    pub pos: PosId,
    pub weights: ConstraintWeights,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    pub fn fact_by_id(&self, id: SubtractId) -> Option<&SubtractFact> {
        self.facts
            .values()
            .flat_map(|facts| facts.iter())
            .find(|fact| fact.id == id)
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

/// subtype edge の片側に載る stack weight。
pub type ConstraintWeight = StackWeight;

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
/// subtype edge の左右に載る subtract weight。
///
/// 関数引数のように polarity が反転する場所では `swapped()` で左右を入れ替える。
/// bounds の再伝播では `compose_for_replay()` し、経路の情報をまとめる。
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

    pub fn with_left(&self, id: SubtractId) -> Self {
        self.with_left_prefix(StackWeight::pop(id))
    }

    pub fn with_left_prefix(&self, weight: StackWeight) -> Self {
        Self {
            left: weight.compose(&self.left),
            right: self.right.clone(),
        }
    }

    pub fn with_right_suffix(&self, weight: StackWeight) -> Self {
        Self {
            left: self.left.clone(),
            right: weight.compose(&self.right),
        }
    }

    pub fn both_from_right(&self) -> Self {
        Self {
            left: self.right.clone(),
            right: self.right.clone(),
        }
    }

    pub fn compose_for_replay(&self, other: &Self) -> Self {
        // Bounds replay can cycle through invariant positions. Unmatched pop counts carry no
        // extra row-subtraction information after the first pop, but the stack sequence remains
        // visible to row subtraction and future pops.
        //
        // Left weights follow the lower-to-upper path order. Right weights describe upper-side
        // stack wrappers, so replaying through a later upper bound nests that bound outside the
        // earlier one; its weight must be prepended.
        Self {
            left: self.left.compose(&other.left).saturate_unmatched_pops(),
            right: other.right.compose(&self.right).saturate_unmatched_pops(),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct VarVarConstraint {
    lower: TypeVar,
    upper: TypeVar,
    weights: ConstraintWeights,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// 1つの `S-subtract` fact。
///
/// `id` は weight として subtype edge に載る識別子、`subtractability` はその ID が表す引き算の内容。
pub struct SubtractFact {
    pub id: SubtractId,
    pub subtractability: Subtractability,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ConstraintEffectFamily {
    pub(crate) path: Vec<String>,
    pub(crate) args: Vec<NeuId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct EffectFamily {
    path: Vec<String>,
    args: Vec<NeuId>,
}

fn common_stack_subtractability<'a>(
    items: impl Iterator<Item = &'a Subtractability>,
) -> Subtractability {
    items
        .cloned()
        .reduce(intersect_subtractability)
        .unwrap_or(Subtractability::All)
}

fn intersect_subtractability(lhs: Subtractability, rhs: Subtractability) -> Subtractability {
    lhs.intersect(rhs)
}

fn sorted_effect_families(mut families: Vec<EffectFamily>) -> Vec<EffectFamily> {
    families.sort_by(|left, right| left.path.cmp(&right.path));
    families
}

fn find_removed_family<'a>(
    family: &EffectFamily,
    removed: &'a [EffectFamily],
) -> Option<&'a EffectFamily> {
    removed.iter().find(|removed| removed.path == family.path)
}

fn families_from_pairs(families: Vec<(Vec<String>, Vec<NeuId>)>) -> Vec<EffectFamily> {
    families
        .into_iter()
        .map(|(path, args)| EffectFamily { path, args })
        .collect()
}

fn subtractability_families(subtractability: &Subtractability) -> Vec<EffectFamily> {
    match subtractability {
        Subtractability::Empty | Subtractability::All => Vec::new(),
        Subtractability::Set(path, args) | Subtractability::AllExcept(path, args) => {
            vec![EffectFamily {
                path: path.clone(),
                args: args.clone(),
            }]
        }
        Subtractability::SetMany(families) | Subtractability::AllExceptMany(families) => families
            .iter()
            .map(|(path, args)| EffectFamily {
                path: path.clone(),
                args: args.clone(),
            })
            .collect(),
    }
}

#[derive(Default)]
struct EffectFamilyMap {
    by_path: FxHashMap<Vec<String>, usize>,
    entries: Vec<EffectFamily>,
}

enum EffectFamilyInsert {
    Inserted,
    Duplicate {
        existing_args: Vec<NeuId>,
        duplicate_args: Vec<NeuId>,
    },
}

impl EffectFamilyMap {
    fn insert(&mut self, family: EffectFamily) -> EffectFamilyInsert {
        if let Some(index) = self.by_path.get(&family.path).copied() {
            return EffectFamilyInsert::Duplicate {
                existing_args: self.entries[index].args.clone(),
                duplicate_args: family.args,
            };
        }
        self.insert_new(family);
        EffectFamilyInsert::Inserted
    }

    fn insert_first(&mut self, family: EffectFamily) {
        if !self.by_path.contains_key(&family.path) {
            self.insert_new(family);
        }
    }

    fn insert_new(&mut self, family: EffectFamily) {
        let index = self.entries.len();
        self.by_path.insert(family.path.clone(), index);
        self.entries.push(family);
    }

    fn into_entries(self) -> Vec<EffectFamily> {
        self.entries
    }
}

fn find_record_field<'a, T>(
    fields: &'a [RecordField<T>],
    name: &str,
) -> Option<&'a RecordField<T>> {
    fields.iter().find(|field| field.name == name)
}

fn optionalized_neg_field(field: RecordField<NegId>) -> RecordField<NegId> {
    RecordField {
        name: field.name,
        value: field.value,
        optional: true,
    }
}
