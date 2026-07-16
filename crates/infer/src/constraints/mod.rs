//! subtype constraint を即時伝播する machine。
//!
//! lowering は `PosId <: NegId` を machine に渡すだけで、上下界 table の更新と再伝播はここが持つ。
//! 伝播で増えた下界・上界は event として外へ出し、selection や SCC の別 machine が反応できる。
//!
//! effect row の subtraction は `stack(T, @S)` と weighted edge として表す。
//! subtract fact table は注釈・データ宣言由来の stack id を記録し、generalize の pruning 入力にする。

mod directed_weight;
mod machine;
pub(crate) mod mutation;
mod row_effect;
#[cfg(test)]
mod tests;
mod timing;
mod trace;

use std::cell::RefCell;
use std::collections::VecDeque;

use directed_weight::{
    DirectedWeights, LeftConstraintWeight as DirectedLeftConstraintWeight, RightStackWeight,
};
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, StackWeight, SubtractId, Subtractability,
    TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

#[cfg(test)]
pub(crate) use mutation::MethodRoleMutation;
pub(crate) use mutation::{
    DependencyKey, InvalidateAllReason, MethodRoleMutationActivation, MethodRoleMutationOutbox,
    MethodRoleMutationSubscriptions, MutationGeneration,
};

pub use timing::{
    ConstraintTiming, ReplayDuplicateProfile, ReplayFrontierShadowMetrics,
    ReplayRoutingShadowMetrics, ReplayWeightedRoutingShadowMetrics,
};
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
    var_adjacency: FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>,
    subtracts: SubtractTable,
    levels: TypeLevels,
    next_internal_type_var: u32,
    row_residuals: FxHashMap<RowResidualKey, TypeVar>,
    declared_subtracts: FxHashSet<SubtractId>,
    effect_family_paths: FxHashSet<Vec<String>>,
    row_tail_vars: FxHashSet<TypeVar>,
    pre_pop_effect_families: FxHashMap<TypeVar, Vec<ConstraintEffectFamily>>,
    lower_filters: FxHashMap<TypeVar, FxHashSet<Subtractability>>,
    effect_filter_violations: FxHashSet<EffectFilterViolationKey>,
    seen: FxHashSet<SubtypeConstraint>,
    events: Vec<ConstraintEvent>,
    method_role_mutations: MethodRoleMutationOutbox,
    timing: ConstraintTiming,
    epoch: ConstraintEpoch,
    replay_frontier_shadow: Option<ReplayFrontierShadow>,
    replay_routing_shadow: Option<RefCell<ReplayRoutingShadow>>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintEpoch(u64);

impl ConstraintEpoch {
    pub fn as_u64(self) -> u64 {
        self.0
    }

    /// Whether equality with this value can prove that no observed mutation occurred.
    ///
    /// The counter saturates instead of wrapping. Once saturated, later mutations cannot be
    /// distinguished, so correctness-sensitive reuse must treat the epoch as unavailable.
    pub fn can_witness_unchanged_state(self) -> bool {
        self.0 != u64::MAX
    }

    fn bump(&mut self) {
        self.0 = self.0.saturating_add(1);
    }
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
    vars: Vec<Option<TypeLevel>>,
    births: Vec<Option<TypeLevel>>,
}

impl TypeLevels {
    fn new() -> Self {
        Self::default()
    }

    fn register_recording_change(&mut self, var: TypeVar, level: TypeLevel) -> bool {
        let index = var.0 as usize;
        ensure_slot(&mut self.vars, index);
        ensure_slot(&mut self.births, index);
        let current_inserted = self.vars[index].is_none();
        let birth_inserted = self.births[index].is_none();
        self.vars[index].get_or_insert(level);
        self.births[index].get_or_insert(level);
        current_inserted || birth_inserted
    }

    fn level_of(&self, var: TypeVar) -> TypeLevel {
        self.vars
            .get(var.0 as usize)
            .and_then(|level| *level)
            .unwrap_or_else(TypeLevel::root)
    }

    fn birth_level_of(&self, var: TypeVar) -> TypeLevel {
        self.births
            .get(var.0 as usize)
            .and_then(|level| *level)
            .unwrap_or_else(TypeLevel::root)
    }

    fn lower_to(&mut self, var: TypeVar, target: TypeLevel) -> bool {
        let index = var.0 as usize;
        ensure_slot(&mut self.vars, index);
        let level = self.vars[index].get_or_insert_with(TypeLevel::root);
        if target < *level {
            *level = target;
            return true;
        }
        false
    }
}

#[derive(Debug)]
struct ExtrudeCtx {
    target: TypeLevel,
    visited: FxHashSet<TypeVar>,
    visited_pos: FxHashSet<PosId>,
    visited_neg: FxHashSet<NegId>,
    visited_neu: FxHashSet<NeuId>,
}

impl ExtrudeCtx {
    fn new(target: TypeLevel) -> Self {
        Self {
            target,
            visited: FxHashSet::default(),
            visited_pos: FxHashSet::default(),
            visited_neg: FxHashSet::default(),
            visited_neu: FxHashSet::default(),
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
    EffectFilterViolation {
        effect: Option<Vec<String>>,
        filter: Subtractability,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ConstraintWork {
    Subtype(SubtypeConstraint),
    SubtractFact(QueuedSubtractFact),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EnqueueSubtypeResult {
    Enqueued,
    Duplicate,
    Trivial,
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
    weight: LeftConstraintWeight,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// 型変数ごとの weighted lower / upper bounds。
///
/// 新しい lower が入ると既存 upper へ、新しい upper が入ると既存 lower へ subtype を再投入する。
/// 同じ型境界でも重みが違えば別の不等式なので、bounds 側では合成せず exact dedup だけを行う。
pub struct TypeBounds {
    vars: Vec<Option<VarBounds>>,
}

impl TypeBounds {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn of(&self, var: TypeVar) -> Option<&VarBounds> {
        #[cfg(test)]
        crate::analysis::record_owner_bound_read(var);
        self.vars
            .get(var.0 as usize)
            .and_then(|bounds| bounds.as_ref())
    }

    fn add_lower(&mut self, var: TypeVar, pos: PosId, weights: ConstraintWeights) -> bool {
        let bounds = self.bounds_mut(var);
        let bound = WeightedLowerBound { pos, weights };
        if !bounds.lower_seen.insert(bound.clone()) {
            return false;
        }
        if bounds.evidence_lower_seen.remove(&bound) {
            bounds.evidence_lowers.retain(|evidence| evidence != &bound);
        }
        bounds.lowers.push(bound);
        true
    }

    fn add_upper(&mut self, var: TypeVar, neg: NegId, weights: ConstraintWeights) -> bool {
        let bounds = self.bounds_mut(var);
        let bound = WeightedUpperBound { neg, weights };
        if !bounds.upper_seen.insert(bound.clone()) {
            return false;
        }
        if bounds.evidence_upper_seen.remove(&bound) {
            bounds.evidence_uppers.retain(|evidence| evidence != &bound);
        }
        bounds.uppers.push(bound);
        true
    }

    fn add_evidence_lower(&mut self, var: TypeVar, pos: PosId, weights: ConstraintWeights) -> bool {
        let bounds = self.bounds_mut(var);
        let bound = WeightedLowerBound { pos, weights };
        if bounds.lower_seen.contains(&bound) || !bounds.evidence_lower_seen.insert(bound.clone()) {
            return false;
        }
        bounds.evidence_lowers.push(bound);
        true
    }

    fn add_evidence_upper(&mut self, var: TypeVar, neg: NegId, weights: ConstraintWeights) -> bool {
        let bounds = self.bounds_mut(var);
        let bound = WeightedUpperBound { neg, weights };
        if bounds.upper_seen.contains(&bound) || !bounds.evidence_upper_seen.insert(bound.clone()) {
            return false;
        }
        bounds.evidence_uppers.push(bound);
        true
    }

    fn bounds_mut(&mut self, var: TypeVar) -> &mut VarBounds {
        let index = var.0 as usize;
        ensure_slot(&mut self.vars, index);
        self.vars[index].get_or_insert_with(VarBounds::default)
    }

    fn record_var_epoch(&mut self, var: TypeVar, epoch: ConstraintEpoch) {
        self.bounds_mut(var).epoch = epoch;
    }
}

fn ensure_slot<T>(items: &mut Vec<Option<T>>, index: usize) {
    if items.len() <= index {
        items.resize_with(index + 1, || None);
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// 1つの型変数に蓄積された上下界。
///
/// bounds は追加順の Vec で持つ。現段階では探索や差分削除よりも、イベント順と単純な再伝播を優先する。
pub struct VarBounds {
    epoch: ConstraintEpoch,
    lowers: Vec<WeightedLowerBound>,
    uppers: Vec<WeightedUpperBound>,
    evidence_lowers: Vec<WeightedLowerBound>,
    evidence_uppers: Vec<WeightedUpperBound>,
    lower_seen: FxHashSet<WeightedLowerBound>,
    upper_seen: FxHashSet<WeightedUpperBound>,
    evidence_lower_seen: FxHashSet<WeightedLowerBound>,
    evidence_upper_seen: FxHashSet<WeightedUpperBound>,
}

impl VarBounds {
    pub fn epoch(&self) -> ConstraintEpoch {
        self.epoch
    }

    pub fn lowers(&self) -> &[WeightedLowerBound] {
        &self.lowers
    }

    pub fn uppers(&self) -> &[WeightedUpperBound] {
        &self.uppers
    }

    pub fn projection_lowers(&self) -> impl Iterator<Item = &WeightedLowerBound> {
        self.evidence_lowers.iter().chain(self.lowers.iter())
    }

    pub fn projection_uppers(&self) -> impl Iterator<Item = &WeightedUpperBound> {
        self.evidence_uppers.iter().chain(self.uppers.iter())
    }

    pub fn evidence_lower_count(&self) -> usize {
        self.evidence_lowers.len()
    }

    pub fn evidence_upper_count(&self) -> usize {
        self.evidence_uppers.len()
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
        #[cfg(test)]
        crate::analysis::record_owner_subtract_read(effect);
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
pub type LeftConstraintWeight = DirectedLeftConstraintWeight;
pub type RightConstraintWeight = RightStackWeight;

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
/// subtype edge の左右に載る subtract weight。
///
/// 関数引数のように polarity が反転する場所では `swapped()` で左右を入れ替える。
/// bounds の再伝播では `compose_for_replay()` し、経路の情報をまとめる。
/// W-Mix は意味論側の directed projection だが、その後の pop cap は
/// worklist 停止性のための実装ガードであり、型等式としては使わない。
pub struct ConstraintWeights {
    pub left: LeftConstraintWeight,
    pub right: RightConstraintWeight,
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
            left: LeftConstraintWeight::from_right_weight(&self.right),
            right: RightConstraintWeight::from_stack_weight_pops(&self.left.to_stack_weight()),
        }
    }

    pub fn with_left(&self, id: SubtractId) -> Self {
        self.with_left_prefix(StackWeight::pop(id))
    }

    pub fn with_left_prefix(&self, weight: StackWeight) -> Self {
        Self {
            left: LeftConstraintWeight::from_stack_weight(&weight).compose(&self.left),
            right: self.right.clone(),
        }
    }

    pub fn with_right_suffix(&self, weight: StackWeight) -> Self {
        Self {
            left: self.left.clone(),
            right: RightConstraintWeight::from_stack_weight_pops(&weight).compose(&self.right),
        }
    }

    pub fn both_from_right(&self) -> Self {
        Self {
            left: LeftConstraintWeight::from_right_weight(&self.right),
            right: self.right.clone(),
        }
    }

    pub fn compose_for_replay(&self, other: &Self) -> Self {
        // Left weights follow the lower-to-upper path order. Right weights describe upper-side
        // stack wrappers, so replaying through a later upper bound nests that bound outside the
        // earlier one; its weight must be prepended.
        Self {
            left: self.left.compose(&other.left),
            right: other.right.compose(&self.right),
        }
        .normalize_directed_mix()
    }

    pub fn normalize_for_var_var_replay_key(&self) -> Self {
        self.clone().normalize_directed_mix()
    }

    pub fn left_filter_set(&self) -> &Subtractability {
        self.left.filter_set()
    }

    pub fn without_left_filter(&self) -> Self {
        Self {
            left: self.left.without_filter(),
            right: self.right.clone(),
        }
    }

    fn normalize_directed_mix(self) -> Self {
        if self.right.is_empty() {
            return self;
        }

        let mixed = DirectedWeights {
            left: self.left.directed().clone(),
            right: self.right,
        }
        .mix();
        Self {
            left: self.left.with_directed_weight(mixed.left),
            right: mixed.right,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct EffectFilterViolationKey {
    effect: Option<Vec<String>>,
    filter: Subtractability,
}

#[derive(Debug, Default)]
struct ReplayFrontierShadow {
    lower_var_var_seen: FxHashSet<ReplayFrontierVarVarBoundKey>,
    upper_var_var_seen: FxHashSet<ReplayFrontierVarVarBoundKey>,
    lower_var_var: ReplayFrontierShadowMetrics,
    upper_var_var: ReplayFrontierShadowMetrics,
}

impl ReplayFrontierShadow {
    fn from_env() -> Option<Self> {
        std::env::var("YULANG_REPLAY_FRONTIER_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0")
            .then(Self::default)
    }

    fn observe_lower_var_var(
        &mut self,
        pivot: TypeVar,
        endpoint: TypeVar,
        weights: &ConstraintWeights,
    ) -> ReplayFrontierShadowObservation {
        observe_var_var_frontier(
            &mut self.lower_var_var_seen,
            &mut self.lower_var_var,
            pivot,
            endpoint,
            weights,
        )
    }

    fn observe_upper_var_var(
        &mut self,
        pivot: TypeVar,
        endpoint: TypeVar,
        weights: &ConstraintWeights,
    ) -> ReplayFrontierShadowObservation {
        observe_var_var_frontier(
            &mut self.upper_var_var_seen,
            &mut self.upper_var_var,
            pivot,
            endpoint,
            weights,
        )
    }

    fn record_lower_result(
        &mut self,
        observation: ReplayFrontierShadowObservation,
        accepted: usize,
    ) {
        record_var_var_frontier_result(&mut self.lower_var_var, observation, accepted);
    }

    fn record_upper_result(
        &mut self,
        observation: ReplayFrontierShadowObservation,
        accepted: usize,
    ) {
        record_var_var_frontier_result(&mut self.upper_var_var, observation, accepted);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ReplayFrontierVarVarBoundKey {
    pivot: TypeVar,
    endpoint: TypeVar,
    weights: ConstraintWeights,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReplayFrontierShadowObservation {
    NotCandidate,
    New,
    Hit,
}

fn observe_var_var_frontier(
    seen: &mut FxHashSet<ReplayFrontierVarVarBoundKey>,
    metrics: &mut ReplayFrontierShadowMetrics,
    pivot: TypeVar,
    endpoint: TypeVar,
    weights: &ConstraintWeights,
) -> ReplayFrontierShadowObservation {
    metrics.candidates += 1;
    let key = ReplayFrontierVarVarBoundKey {
        pivot,
        endpoint,
        weights: weights.normalize_for_var_var_replay_key(),
    };
    if seen.insert(key) {
        ReplayFrontierShadowObservation::New
    } else {
        metrics.hits += 1;
        ReplayFrontierShadowObservation::Hit
    }
}

fn record_var_var_frontier_result(
    metrics: &mut ReplayFrontierShadowMetrics,
    observation: ReplayFrontierShadowObservation,
    accepted: usize,
) {
    if observation != ReplayFrontierShadowObservation::Hit {
        return;
    }
    if accepted == 0 {
        metrics.safe_hits += 1;
    } else {
        metrics.unsafe_hits += 1;
        metrics.unsafe_accepted += accepted;
    }
}

#[derive(Debug, Default)]
struct ReplayRoutingShadow {
    unweighted_enabled: bool,
    graph: FxHashMap<TypeVar, FxHashSet<TypeVar>>,
    nodes: FxHashSet<TypeVar>,
    endpoint_seen: FxHashSet<(TypeVar, TypeVar)>,
    metrics: ReplayRoutingShadowMetrics,
    weighted: Option<ReplayWeightedRoutingShadow>,
}

impl ReplayRoutingShadow {
    fn from_env() -> Option<Self> {
        let unweighted = std::env::var("YULANG_REPLAY_ROUTING_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0");
        let weighted = ReplayWeightedRoutingShadow::from_env();
        (unweighted || weighted.is_some()).then(|| Self {
            unweighted_enabled: unweighted,
            weighted,
            ..Self::default()
        })
    }

    fn observe_var_var_edge(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
    ) {
        if source == target {
            return;
        }
        if let Some(weighted) = &mut self.weighted {
            weighted.observe_edge(source, target, weights);
        }
        if !self.unweighted_enabled {
            return;
        }
        self.metrics.accepted_edges += 1;
        if !self.endpoint_seen.insert((source, target)) {
            self.metrics.repeated_endpoint_edges += 1;
        }
        if self.reaches(source, target) {
            self.metrics.reachable_before_edges += 1;
        }
        self.nodes.insert(source);
        self.nodes.insert(target);
        if self.graph.entry(source).or_default().insert(target) {
            self.metrics.graph_edges += 1;
        }
        self.metrics.graph_nodes = self.nodes.len();
    }

    fn observe_var_var_consequence(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
        seen_before: bool,
    ) {
        if source == target {
            return;
        }
        if let Some(weighted) = &mut self.weighted {
            weighted.observe_consequence(source, target, weights, seen_before);
        }
    }

    fn has_weighted_frontier_path(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
    ) -> bool {
        self.weighted
            .as_mut()
            .is_some_and(|weighted| weighted.has_frontier_path(source, target, weights))
    }

    fn reaches(&self, source: TypeVar, target: TypeVar) -> bool {
        let mut stack = vec![source];
        let mut visited = FxHashSet::default();
        while let Some(var) = stack.pop() {
            if !visited.insert(var) {
                continue;
            }
            let Some(next) = self.graph.get(&var) else {
                continue;
            };
            if next.contains(&target) {
                return true;
            }
            stack.extend(next.iter().copied());
        }
        false
    }
}

#[derive(Debug)]
struct ReplayWeightedRoutingShadow {
    graph: FxHashMap<TypeVar, Vec<ReplayWeightedRouteEdge>>,
    frontier_graph: FxHashMap<TypeVar, Vec<ReplayWeightedRouteEdge>>,
    nodes: FxHashSet<TypeVar>,
    frontier_nodes: FxHashSet<TypeVar>,
    positive_paths: FxHashSet<ReplayWeightedPathKey>,
    frontier_positive_paths: FxHashSet<ReplayWeightedPathKey>,
    summary: Option<ReplayWeightedPathSummary>,
    weights: ReplayWeightInterner,
    metrics: ReplayWeightedRoutingShadowMetrics,
    search_limit: usize,
    all_edge_search_enabled: bool,
    frontier_search_enabled: bool,
}

impl ReplayWeightedRoutingShadow {
    fn from_env() -> Option<Self> {
        let weighted = std::env::var("YULANG_REPLAY_WEIGHTED_ROUTING_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0");
        let evidence_skip = evidence_only_replay_skip_enabled();
        let summary = ReplayWeightedPathSummary::from_env();
        let search_limit = if weighted {
            replay_weighted_routing_shadow_limit()
        } else {
            replay_evidence_only_skip_limit()
        };
        (weighted || evidence_skip || summary.is_some()).then(|| Self {
            graph: FxHashMap::default(),
            frontier_graph: FxHashMap::default(),
            nodes: FxHashSet::default(),
            frontier_nodes: FxHashSet::default(),
            positive_paths: FxHashSet::default(),
            frontier_positive_paths: FxHashSet::default(),
            summary,
            weights: ReplayWeightInterner::default(),
            metrics: ReplayWeightedRoutingShadowMetrics::default(),
            search_limit,
            all_edge_search_enabled: weighted,
            frontier_search_enabled: weighted || evidence_skip,
        })
    }

    fn observe_edge(&mut self, source: TypeVar, target: TypeVar, weights: &ConstraintWeights) {
        if source == target {
            return;
        }
        self.metrics.accepted_edges += 1;
        let weight = self.weights.intern(weights.clone());
        if let Some(summary) = &mut self.summary {
            summary.observe_edge(source, target, weight, &mut self.weights);
            self.metrics.summary_observed_edges = summary.metrics.observed_edges;
            self.metrics.summary_known_edges = summary.metrics.known_edges;
            self.metrics.summary_new_edges = summary.metrics.new_edges;
            self.metrics.summary_inserted_paths = summary.metrics.inserted_paths;
            self.metrics.summary_duplicate_paths = summary.metrics.duplicate_paths;
            self.metrics.summary_capped_insertions = summary.metrics.capped_insertions;
            self.metrics.summary_max_queue = summary.metrics.max_queue;
            self.metrics.summary_paths = summary.paths.len();
            self.metrics.summary_outgoing_nodes = summary.outgoing.len();
            self.metrics.summary_incoming_nodes = summary.incoming.len();
        }
        if !self.all_edge_search_enabled && !self.frontier_search_enabled {
            self.metrics.weight_count = self.weights.len();
            self.metrics.compose_cache_hits = self.weights.compose_hits;
            self.metrics.compose_cache_misses = self.weights.compose_misses;
            return;
        }

        if self.all_edge_search_enabled {
            let search = search_exact_weighted_route(
                &self.graph,
                &mut self.positive_paths,
                &mut self.weights,
                self.search_limit,
                source,
                target,
                weight,
            );
            if search.cache_hit {
                self.metrics.route_cache_hits += 1;
            }
            self.metrics.search_states += search.states;
            self.metrics.max_search_states = self.metrics.max_search_states.max(search.states);
            if search.capped {
                self.metrics.capped_searches += 1;
            }
            if search.found {
                self.metrics.reachable_before_edges += 1;
            }
        }

        if self.frontier_search_enabled {
            let frontier_search = search_exact_weighted_route(
                &self.frontier_graph,
                &mut self.frontier_positive_paths,
                &mut self.weights,
                self.search_limit,
                source,
                target,
                weight,
            );
            if frontier_search.cache_hit {
                self.metrics.frontier_route_cache_hits += 1;
            }
            self.metrics.frontier_search_states += frontier_search.states;
            self.metrics.frontier_max_search_states = self
                .metrics
                .frontier_max_search_states
                .max(frontier_search.states);
            if frontier_search.capped {
                self.metrics.frontier_capped_searches += 1;
            }
            if frontier_search.found {
                self.metrics.frontier_skipped_edges += 1;
            } else {
                self.frontier_nodes.insert(source);
                self.frontier_nodes.insert(target);
                self.frontier_graph
                    .entry(source)
                    .or_default()
                    .push(ReplayWeightedRouteEdge { target, weight });
                self.frontier_positive_paths
                    .insert(ReplayWeightedPathKey::new(source, target, weight));
                self.metrics.frontier_inserted_edges += 1;
                self.metrics.frontier_graph_nodes = self.frontier_nodes.len();
                self.metrics.frontier_graph_edges += 1;
            }
        }

        if self.all_edge_search_enabled {
            self.nodes.insert(source);
            self.nodes.insert(target);
            self.graph
                .entry(source)
                .or_default()
                .push(ReplayWeightedRouteEdge { target, weight });
            self.positive_paths
                .insert(ReplayWeightedPathKey::new(source, target, weight));
            self.metrics.graph_nodes = self.nodes.len();
            self.metrics.graph_edges += 1;
        }
        self.metrics.route_cache_entries = self.positive_paths.len();
        self.metrics.frontier_route_cache_entries = self.frontier_positive_paths.len();
        self.metrics.weight_count = self.weights.len();
        self.metrics.compose_cache_hits = self.weights.compose_hits;
        self.metrics.compose_cache_misses = self.weights.compose_misses;
    }

    fn has_frontier_path(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
    ) -> bool {
        if source == target {
            return false;
        }
        let weight = self.weights.intern(weights.clone());
        let search = search_exact_weighted_route(
            &self.frontier_graph,
            &mut self.frontier_positive_paths,
            &mut self.weights,
            self.search_limit,
            source,
            target,
            weight,
        );
        if search.cache_hit {
            self.metrics.frontier_route_cache_hits += 1;
        }
        if search.capped {
            self.metrics.frontier_capped_searches += 1;
        }
        self.metrics.frontier_search_states += search.states;
        self.metrics.frontier_max_search_states =
            self.metrics.frontier_max_search_states.max(search.states);
        self.metrics.weight_count = self.weights.len();
        self.metrics.compose_cache_hits = self.weights.compose_hits;
        self.metrics.compose_cache_misses = self.weights.compose_misses;
        search.found
    }

    fn observe_consequence(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
        seen_before: bool,
    ) {
        if !self.all_edge_search_enabled {
            return;
        }
        self.metrics.consequence_queries += 1;
        let weight = self.weights.intern(weights.clone());
        let search = search_exact_weighted_route(
            &self.graph,
            &mut self.positive_paths,
            &mut self.weights,
            self.search_limit,
            source,
            target,
            weight,
        );
        if search.cache_hit {
            self.metrics.route_cache_hits += 1;
        }
        self.metrics.consequence_search_states += search.states;
        self.metrics.consequence_max_search_states = self
            .metrics
            .consequence_max_search_states
            .max(search.states);
        if search.capped {
            self.metrics.consequence_capped_searches += 1;
        }
        if search.found {
            self.metrics.consequence_known += 1;
            if !seen_before {
                self.metrics.consequence_known_unseen += 1;
            }
        } else {
            self.metrics.consequence_unknown += 1;
            if seen_before {
                self.metrics.consequence_unknown_seen += 1;
            }
        }

        let frontier_search = search_exact_weighted_route(
            &self.frontier_graph,
            &mut self.frontier_positive_paths,
            &mut self.weights,
            self.search_limit,
            source,
            target,
            weight,
        );
        if frontier_search.cache_hit {
            self.metrics.frontier_route_cache_hits += 1;
        }
        self.metrics.consequence_frontier_search_states += frontier_search.states;
        self.metrics.consequence_frontier_max_search_states = self
            .metrics
            .consequence_frontier_max_search_states
            .max(frontier_search.states);
        if frontier_search.capped {
            self.metrics.consequence_frontier_capped_searches += 1;
        }
        if frontier_search.found {
            self.metrics.consequence_frontier_known += 1;
            if !seen_before {
                self.metrics.consequence_frontier_known_unseen += 1;
            }
        } else {
            self.metrics.consequence_frontier_unknown += 1;
            if seen_before {
                self.metrics.consequence_frontier_unknown_seen += 1;
            }
        }
        self.metrics.route_cache_entries = self.positive_paths.len();
        self.metrics.frontier_route_cache_entries = self.frontier_positive_paths.len();
        self.metrics.weight_count = self.weights.len();
        self.metrics.compose_cache_hits = self.weights.compose_hits;
        self.metrics.compose_cache_misses = self.weights.compose_misses;
    }
}

fn search_exact_weighted_route(
    graph: &FxHashMap<TypeVar, Vec<ReplayWeightedRouteEdge>>,
    positive_paths: &mut FxHashSet<ReplayWeightedPathKey>,
    weights: &mut ReplayWeightInterner,
    search_limit: usize,
    source: TypeVar,
    target: TypeVar,
    target_weight: ReplayWeightId,
) -> ReplayWeightedRouteSearch {
    let key = ReplayWeightedPathKey::new(source, target, target_weight);
    if positive_paths.contains(&key) {
        return ReplayWeightedRouteSearch {
            found: true,
            capped: false,
            cache_hit: true,
            states: 0,
        };
    }
    let empty = weights.empty();
    let mut stack = vec![ReplayWeightedRouteState {
        var: source,
        weight: empty,
    }];
    let mut visited = FxHashSet::default();
    let mut local_states = 0usize;
    while let Some(state) = stack.pop() {
        if !visited.insert(state) {
            continue;
        }
        let edges = graph.get(&state.var).cloned().unwrap_or_default();
        for edge in edges {
            local_states += 1;
            if local_states > search_limit {
                return ReplayWeightedRouteSearch {
                    found: false,
                    capped: true,
                    cache_hit: false,
                    states: local_states,
                };
            }
            let next_weight = weights.compose_for_replay(state.weight, edge.weight);
            if edge.target == target && next_weight == target_weight {
                positive_paths.insert(key);
                return ReplayWeightedRouteSearch {
                    found: true,
                    capped: false,
                    cache_hit: false,
                    states: local_states,
                };
            }
            stack.push(ReplayWeightedRouteState {
                var: edge.target,
                weight: next_weight,
            });
        }
    }
    ReplayWeightedRouteSearch {
        found: false,
        capped: false,
        cache_hit: false,
        states: local_states,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReplayWeightedRouteSearch {
    found: bool,
    capped: bool,
    cache_hit: bool,
    states: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReplayWeightedRouteEdge {
    target: TypeVar,
    weight: ReplayWeightId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayWeightedRouteState {
    var: TypeVar,
    weight: ReplayWeightId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayWeightedPathKey {
    source: TypeVar,
    target: TypeVar,
    weight: ReplayWeightId,
}

impl ReplayWeightedPathKey {
    fn new(source: TypeVar, target: TypeVar, weight: ReplayWeightId) -> Self {
        Self {
            source,
            target,
            weight,
        }
    }
}

#[derive(Debug)]
struct ReplayWeightedPathSummary {
    paths: FxHashSet<ReplayWeightedPathKey>,
    outgoing: FxHashMap<TypeVar, Vec<ReplayWeightedPathSummaryEdge>>,
    incoming: FxHashMap<TypeVar, Vec<ReplayWeightedPathSummaryEdge>>,
    queue: VecDeque<ReplayWeightedPathKey>,
    metrics: ReplayWeightedPathSummaryMetrics,
    limit: usize,
    capped: bool,
}

impl ReplayWeightedPathSummary {
    fn from_env() -> Option<Self> {
        std::env::var("YULANG_REPLAY_WEIGHTED_ROUTING_SUMMARY_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0")
            .then(|| Self {
                paths: FxHashSet::default(),
                outgoing: FxHashMap::default(),
                incoming: FxHashMap::default(),
                queue: VecDeque::new(),
                metrics: ReplayWeightedPathSummaryMetrics::default(),
                limit: replay_weighted_routing_summary_shadow_limit(),
                capped: false,
            })
    }

    fn observe_edge(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weight: ReplayWeightId,
        weights: &mut ReplayWeightInterner,
    ) {
        self.metrics.observed_edges += 1;
        if self.capped {
            self.metrics.capped_insertions += 1;
            return;
        }
        if self
            .paths
            .contains(&ReplayWeightedPathKey::new(source, target, weight))
        {
            self.metrics.known_edges += 1;
            return;
        }
        self.metrics.new_edges += 1;
        self.insert_path(source, target, weight);
        self.close_from_queue(weights);
    }

    fn close_from_queue(&mut self, weights: &mut ReplayWeightInterner) {
        if self.capped {
            return;
        }
        while let Some(path) = self.queue.pop_front() {
            let mut prefixes = self.incoming.get(&path.source).cloned().unwrap_or_default();
            prefixes.push(ReplayWeightedPathSummaryEdge {
                var: path.source,
                weight: weights.empty(),
            });

            let mut suffixes = self.outgoing.get(&path.target).cloned().unwrap_or_default();
            suffixes.push(ReplayWeightedPathSummaryEdge {
                var: path.target,
                weight: weights.empty(),
            });

            for prefix in &prefixes {
                let prefix_weight = weights.compose_for_replay(prefix.weight, path.weight);
                for suffix in &suffixes {
                    if self.capped {
                        self.metrics.capped_insertions += 1;
                        return;
                    }
                    let weight = weights.compose_for_replay(prefix_weight, suffix.weight);
                    self.insert_path(prefix.var, suffix.var, weight);
                }
            }
            self.metrics.max_queue = self.metrics.max_queue.max(self.queue.len());
        }
    }

    fn insert_path(&mut self, source: TypeVar, target: TypeVar, weight: ReplayWeightId) {
        let key = ReplayWeightedPathKey::new(source, target, weight);
        if !self.paths.insert(key) {
            self.metrics.duplicate_paths += 1;
            return;
        }
        if self.paths.len() > self.limit {
            self.capped = true;
            self.metrics.capped_insertions += 1;
            self.paths.remove(&key);
            self.queue.clear();
            return;
        }
        self.metrics.inserted_paths += 1;
        self.outgoing
            .entry(source)
            .or_default()
            .push(ReplayWeightedPathSummaryEdge {
                var: target,
                weight,
            });
        self.incoming
            .entry(target)
            .or_default()
            .push(ReplayWeightedPathSummaryEdge {
                var: source,
                weight,
            });
        self.queue.push_back(key);
        self.metrics.max_queue = self.metrics.max_queue.max(self.queue.len());
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct ReplayWeightedPathSummaryMetrics {
    observed_edges: usize,
    known_edges: usize,
    new_edges: usize,
    inserted_paths: usize,
    duplicate_paths: usize,
    capped_insertions: usize,
    max_queue: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReplayWeightedPathSummaryEdge {
    var: TypeVar,
    weight: ReplayWeightId,
}

#[derive(Debug, Default)]
struct ReplayWeightInterner {
    weights: Vec<ConstraintWeights>,
    ids: FxHashMap<ConstraintWeights, ReplayWeightId>,
    compose_cache: FxHashMap<(ReplayWeightId, ReplayWeightId), ReplayWeightId>,
    empty: Option<ReplayWeightId>,
    compose_hits: usize,
    compose_misses: usize,
}

impl ReplayWeightInterner {
    fn empty(&mut self) -> ReplayWeightId {
        if let Some(id) = self.empty {
            return id;
        }
        let id = self.intern(ConstraintWeights::empty());
        self.empty = Some(id);
        id
    }

    fn intern(&mut self, weights: ConstraintWeights) -> ReplayWeightId {
        if let Some(id) = self.ids.get(&weights) {
            return *id;
        }
        let id = ReplayWeightId(self.weights.len() as u32);
        self.weights.push(weights.clone());
        self.ids.insert(weights, id);
        id
    }

    fn compose_for_replay(
        &mut self,
        left: ReplayWeightId,
        right: ReplayWeightId,
    ) -> ReplayWeightId {
        let key = (left, right);
        if let Some(id) = self.compose_cache.get(&key) {
            self.compose_hits += 1;
            return *id;
        }
        self.compose_misses += 1;
        let left_weight = self.weights[left.0 as usize].clone();
        let right_weight = self.weights[right.0 as usize].clone();
        let composed = left_weight
            .compose_for_replay(&right_weight)
            .normalize_for_var_var_replay_key();
        let id = self.intern(composed);
        self.compose_cache.insert(key, id);
        id
    }

    fn len(&self) -> usize {
        self.weights.len()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayWeightId(u32);

fn replay_weighted_routing_shadow_limit() -> usize {
    std::env::var("YULANG_REPLAY_WEIGHTED_ROUTING_SHADOW_LIMIT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|limit| *limit > 0)
        .unwrap_or(4096)
}

fn replay_weighted_routing_summary_shadow_limit() -> usize {
    std::env::var("YULANG_REPLAY_WEIGHTED_ROUTING_SUMMARY_LIMIT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|limit| *limit > 0)
        .unwrap_or(200_000)
}

fn evidence_only_replay_skip_enabled() -> bool {
    std::env::var("YULANG_REPLAY_EVIDENCE_ONLY_SKIP")
        .is_ok_and(|value| !value.is_empty() && value != "0")
}

fn replay_evidence_only_skip_limit() -> usize {
    std::env::var("YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|limit| *limit > 0)
        .unwrap_or(16)
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
