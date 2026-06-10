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
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, SubtractId, Subtractability, TypeArena,
    TypeVar,
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
    levels: TypeLevels,
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
            levels: TypeLevels::new(),
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

    pub fn register_type_var(&mut self, var: TypeVar, level: TypeLevel) {
        self.levels.register(var, level);
    }

    pub fn level_of(&self, var: TypeVar) -> TypeLevel {
        self.levels.level_of(var)
    }

    pub fn birth_level_of(&self, var: TypeVar) -> TypeLevel {
        self.levels.birth_level_of(var)
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
                self.record_subtract_fact(fact.effect, fact.fact);
            }
        }
    }

    fn record_subtract_fact(&mut self, effect: TypeVar, fact: SubtractFact) {
        let id = fact.id;
        if self.subtracts.record(effect, fact) {
            self.events
                .push(ConstraintEvent::SubtractFactAdded { effect, id });
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
            (Pos::NonSubtract(pos, subtract), _) => {
                self.enqueue_subtype(
                    pos,
                    constraint.weights.with_left(subtract),
                    constraint.upper,
                );
            }
            (Pos::Union(left, right), _) => {
                self.enqueue_subtype(left, constraint.weights.clone(), constraint.upper);
                self.enqueue_subtype(right, constraint.weights, constraint.upper);
            }
            (_, Neg::Intersection(left, right)) => {
                self.enqueue_subtype(constraint.lower, constraint.weights.clone(), left);
                self.enqueue_subtype(constraint.lower, constraint.weights, right);
            }
            (Pos::Var(source), Neg::Var(target)) => {
                self.add_lower_bound(target, constraint.lower, constraint.weights.clone());
                self.add_upper_bound(source, constraint.upper, constraint.weights);
            }
            (Pos::Var(source), Neg::Row(items, tail)) => {
                self.add_effect_row_upper_bound(source, items, tail, constraint.weights);
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
                if matches!(self.types.neg(arg_eff), Neg::Bot) {
                    self.enqueue_subtype(
                        upper_arg_eff,
                        constraint.weights.both_from_right(),
                        upper_ret_eff,
                    );
                } else {
                    self.enqueue_subtype(upper_arg_eff, swapped, arg_eff);
                }
                self.enqueue_subtype(ret_eff, constraint.weights.clone(), upper_ret_eff);
                self.enqueue_subtype(ret, constraint.weights, upper_ret);
            }
            (Pos::Con(lower_path, lower_args), Neg::Con(upper_path, upper_args))
                if lower_path == upper_path && lower_args.len() == upper_args.len() =>
            {
                self.enqueue_invariant_neu_args(lower_args, upper_args, constraint.weights);
            }
            (Pos::Con(source, _), Neg::Con(target, _)) if source != target => {
                self.events.push(ConstraintEvent::NominalCastNeeded {
                    lower: constraint.lower,
                    upper: constraint.upper,
                    source,
                    target,
                    weights: constraint.weights,
                });
            }
            (Pos::Record(lower_fields), Neg::Record(upper_fields)) => {
                self.enqueue_record_fields(lower_fields, upper_fields, constraint.weights);
            }
            (Pos::RecordTailSpread { fields, tail }, Neg::Record(upper_fields)) => {
                self.enqueue_record_tail_spread(fields, tail, upper_fields, constraint.weights);
            }
            (Pos::RecordHeadSpread { tail, fields }, Neg::Record(upper_fields)) => {
                self.enqueue_record_head_spread(tail, fields, upper_fields, constraint.weights);
            }
            (Pos::PolyVariant(lower_items), Neg::PolyVariant(upper_items)) => {
                self.enqueue_variant_items(lower_items, upper_items, constraint.weights);
            }
            (Pos::Tuple(lowers), Neg::Tuple(uppers)) if lowers.len() == uppers.len() => {
                for (lower, upper) in lowers.into_iter().zip(uppers) {
                    self.enqueue_subtype(lower, constraint.weights.clone(), upper);
                }
            }
            (Pos::Row(items), Neg::Row(upper_items, upper_tail)) => {
                self.enqueue_row_items(items, upper_items, upper_tail, constraint.weights);
            }
            _ => {}
        }
    }

    fn enqueue_invariant_neu_args(
        &mut self,
        lower_args: Vec<NeuId>,
        upper_args: Vec<NeuId>,
        weights: ConstraintWeights,
    ) {
        for (lower, upper) in lower_args.into_iter().zip(upper_args) {
            self.enqueue_invariant_neu(lower, upper, weights.clone());
        }
    }

    fn enqueue_invariant_neu(&mut self, lower: NeuId, upper: NeuId, weights: ConstraintWeights) {
        let (lower_pos, lower_neg) = self.neu_bounds(lower);
        let (upper_pos, upper_neg) = self.neu_bounds(upper);
        self.enqueue_subtype(lower_pos, weights.clone(), upper_neg);
        self.enqueue_subtype(upper_pos, weights.swapped(), lower_neg);
    }

    fn neu_bounds(&mut self, id: NeuId) -> (PosId, NegId) {
        match self.types.neu(id).clone() {
            Neu::Bounds(lower, var, upper) => {
                let var_pos = self.alloc_pos(Pos::Var(var));
                let var_neg = self.alloc_neg(Neg::Var(var));
                (
                    self.alloc_pos(Pos::Union(lower, var_pos)),
                    self.alloc_neg(Neg::Intersection(var_neg, upper)),
                )
            }
            Neu::Con(path, args) => (
                self.alloc_pos(Pos::Con(path.clone(), args.clone())),
                self.alloc_neg(Neg::Con(path, args)),
            ),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let (arg_pos, arg_neg) = self.neu_bounds(arg);
                let (arg_eff_pos, arg_eff_neg) = self.neu_bounds(arg_eff);
                let (ret_eff_pos, ret_eff_neg) = self.neu_bounds(ret_eff);
                let (ret_pos, ret_neg) = self.neu_bounds(ret);
                (
                    self.alloc_pos(Pos::Fun {
                        arg: arg_neg,
                        arg_eff: arg_eff_neg,
                        ret_eff: ret_eff_pos,
                        ret: ret_pos,
                    }),
                    self.alloc_neg(Neg::Fun {
                        arg: arg_pos,
                        arg_eff: arg_eff_pos,
                        ret_eff: ret_eff_neg,
                        ret: ret_neg,
                    }),
                )
            }
            Neu::Record(fields) => {
                let (pos, neg) = self.neu_record_fields(fields);
                (
                    self.alloc_pos(Pos::Record(pos)),
                    self.alloc_neg(Neg::Record(neg)),
                )
            }
            Neu::PolyVariant(items) => {
                let (pos, neg) = self.neu_variant_items(items);
                (
                    self.alloc_pos(Pos::PolyVariant(pos)),
                    self.alloc_neg(Neg::PolyVariant(neg)),
                )
            }
            Neu::Tuple(items) => {
                let mut pos = Vec::with_capacity(items.len());
                let mut neg = Vec::with_capacity(items.len());
                for item in items {
                    let (lower, upper) = self.neu_bounds(item);
                    pos.push(lower);
                    neg.push(upper);
                }
                (
                    self.alloc_pos(Pos::Tuple(pos)),
                    self.alloc_neg(Neg::Tuple(neg)),
                )
            }
        }
    }

    fn neu_record_fields(
        &mut self,
        fields: Vec<RecordField<NeuId>>,
    ) -> (Vec<RecordField<PosId>>, Vec<RecordField<NegId>>) {
        let mut pos = Vec::with_capacity(fields.len());
        let mut neg = Vec::with_capacity(fields.len());
        for field in fields {
            let (lower, upper) = self.neu_bounds(field.value);
            pos.push(RecordField {
                name: field.name.clone(),
                value: lower,
                optional: field.optional,
            });
            neg.push(RecordField {
                name: field.name,
                value: upper,
                optional: field.optional,
            });
        }
        (pos, neg)
    }

    fn neu_variant_items(
        &mut self,
        items: Vec<(String, Vec<NeuId>)>,
    ) -> (Vec<(String, Vec<PosId>)>, Vec<(String, Vec<NegId>)>) {
        let mut pos = Vec::with_capacity(items.len());
        let mut neg = Vec::with_capacity(items.len());
        for (name, payloads) in items {
            let mut pos_payloads = Vec::with_capacity(payloads.len());
            let mut neg_payloads = Vec::with_capacity(payloads.len());
            for payload in payloads {
                let (lower, upper) = self.neu_bounds(payload);
                pos_payloads.push(lower);
                neg_payloads.push(upper);
            }
            pos.push((name.clone(), pos_payloads));
            neg.push((name, neg_payloads));
        }
        (pos, neg)
    }

    fn enqueue_record_fields(
        &mut self,
        lower_fields: Vec<RecordField<PosId>>,
        upper_fields: Vec<RecordField<NegId>>,
        weights: ConstraintWeights,
    ) {
        for upper in upper_fields {
            let Some(lower) = find_record_field(&lower_fields, &upper.name) else {
                continue;
            };
            if lower.optional && !upper.optional {
                continue;
            }
            self.enqueue_subtype(lower.value, weights.clone(), upper.value);
        }
    }

    fn enqueue_record_tail_spread(
        &mut self,
        fields: Vec<RecordField<PosId>>,
        tail: PosId,
        upper_fields: Vec<RecordField<NegId>>,
        weights: ConstraintWeights,
    ) {
        for upper in upper_fields {
            if let Some(lower) = find_record_field(&fields, &upper.name) {
                if !lower.optional || upper.optional {
                    self.enqueue_subtype(lower.value, weights.clone(), upper.value);
                }
                let tail_upper = self.singleton_neg_record(optionalized_neg_field(upper));
                self.enqueue_subtype(tail, weights.clone(), tail_upper);
            } else {
                let tail_upper = self.singleton_neg_record(upper);
                self.enqueue_subtype(tail, weights.clone(), tail_upper);
            }
        }
    }

    fn enqueue_record_head_spread(
        &mut self,
        tail: PosId,
        fields: Vec<RecordField<PosId>>,
        upper_fields: Vec<RecordField<NegId>>,
        weights: ConstraintWeights,
    ) {
        for upper in upper_fields {
            if let Some(lower) = find_record_field(&fields, &upper.name) {
                if !lower.optional || upper.optional {
                    self.enqueue_subtype(lower.value, weights.clone(), upper.value);
                }
            } else {
                let tail_upper = self.singleton_neg_record(upper);
                self.enqueue_subtype(tail, weights.clone(), tail_upper);
            }
        }
    }

    fn singleton_neg_record(&mut self, field: RecordField<NegId>) -> NegId {
        self.alloc_neg(Neg::Record(vec![field]))
    }

    fn enqueue_variant_items(
        &mut self,
        lower_items: Vec<(String, Vec<PosId>)>,
        upper_items: Vec<(String, Vec<NegId>)>,
        weights: ConstraintWeights,
    ) {
        for (name, lower_payloads) in lower_items {
            let Some((_, upper_payloads)) = upper_items
                .iter()
                .find(|(upper_name, _)| upper_name == &name)
            else {
                continue;
            };
            if lower_payloads.len() != upper_payloads.len() {
                continue;
            }
            for (lower, upper) in lower_payloads
                .into_iter()
                .zip(upper_payloads.iter().copied())
            {
                self.enqueue_subtype(lower, weights.clone(), upper);
            }
        }
    }

    fn enqueue_row_items(
        &mut self,
        items: Vec<PosId>,
        upper_items: Vec<NegId>,
        upper_tail: NegId,
        weights: ConstraintWeights,
    ) {
        let mut remaining_upper_items = upper_items;
        let mut variable_items = Vec::new();
        let mut lower_tail_items = Vec::new();
        for item in items {
            if matches!(self.types.pos(item), Pos::Var(_)) {
                variable_items.push(item);
                continue;
            }

            if let Some(index) = remaining_upper_items
                .iter()
                .position(|upper| self.row_items_can_match(item, *upper))
            {
                let upper = remaining_upper_items.remove(index);
                self.enqueue_row_item_match(item, upper, weights.clone());
            } else {
                lower_tail_items.push(item);
                self.enqueue_subtype(item, weights.clone(), upper_tail);
            }
        }

        for item in variable_items {
            if let Some(index) = remaining_upper_items
                .iter()
                .position(|upper| self.row_items_can_match(item, *upper))
            {
                let upper = remaining_upper_items.remove(index);
                self.enqueue_row_item_match(item, upper, weights.clone());
                continue;
            }

            lower_tail_items.push(item);
            let upper = if remaining_upper_items.is_empty() {
                upper_tail
            } else {
                self.alloc_neg(Neg::Row(remaining_upper_items.clone(), upper_tail))
            };
            self.enqueue_subtype(item, weights.clone(), upper);
        }

        self.enqueue_upper_tail_to_lower_row_tail(upper_tail, lower_tail_items, weights);
    }

    fn row_items_can_match(&self, lower: PosId, upper: NegId) -> bool {
        match (self.types.pos(lower), self.types.neg(upper)) {
            (Pos::Con(lower_path, _), Neg::Con(upper_path, _)) => lower_path == upper_path,
            (Pos::Var(lower), Neg::Var(upper)) => lower == upper,
            _ => false,
        }
    }

    fn enqueue_row_item_match(&mut self, lower: PosId, upper: NegId, weights: ConstraintWeights) {
        match (self.types.pos(lower).clone(), self.types.neg(upper).clone()) {
            (Pos::Con(lower_path, lower_args), Neg::Con(upper_path, upper_args))
                if lower_path == upper_path =>
            {
                self.enqueue_row_item_neu_args(lower_args, upper_args, weights);
            }
            (Pos::Var(lower), Neg::Var(upper)) if lower == upper => {}
            _ => self.enqueue_subtype(lower, weights, upper),
        }
    }

    fn enqueue_row_item_neu_args(
        &mut self,
        lower_args: Vec<NeuId>,
        upper_args: Vec<NeuId>,
        weights: ConstraintWeights,
    ) {
        for (lower, upper) in lower_args.into_iter().zip(upper_args) {
            let (lower_pos, lower_neg) = self.neu_bounds(lower);
            let (upper_pos, upper_neg) = self.neu_bounds(upper);
            self.enqueue_subtype(lower_pos, weights.clone(), upper_neg);
            self.enqueue_subtype(upper_pos, weights.swapped(), lower_neg);
        }
    }

    fn enqueue_upper_tail_to_lower_row_tail(
        &mut self,
        upper_tail: NegId,
        lower_tail_items: Vec<PosId>,
        weights: ConstraintWeights,
    ) {
        let Neg::Var(tail_var) = self.types.neg(upper_tail).clone() else {
            return;
        };
        let Some(lower_tail) = self.neg_row_from_pos_items(lower_tail_items) else {
            return;
        };
        let tail = self.alloc_pos(Pos::Var(tail_var));
        self.enqueue_subtype(tail, weights, lower_tail);
    }

    fn neg_row_from_pos_items(&mut self, items: Vec<PosId>) -> Option<NegId> {
        match items.as_slice() {
            [] => None,
            [item] => self.neg_row_item_from_pos(*item),
            _ => {
                let neg_items = items
                    .into_iter()
                    .map(|item| self.neg_row_item_from_pos(item))
                    .collect::<Option<Vec<_>>>()?;
                let tail = self.alloc_neg(Neg::Bot);
                Some(self.alloc_neg(Neg::Row(neg_items, tail)))
            }
        }
    }

    fn neg_row_item_from_pos(&mut self, item: PosId) -> Option<NegId> {
        match self.types.pos(item).clone() {
            Pos::Var(var) => Some(self.alloc_neg(Neg::Var(var))),
            Pos::Con(path, args) => Some(self.alloc_neg(Neg::Con(path, args))),
            Pos::Row(items) => self.neg_row_from_pos_items(items),
            _ => None,
        }
    }

    fn add_effect_row_upper_bound(
        &mut self,
        source: TypeVar,
        items: Vec<NegId>,
        tail: NegId,
        weights: ConstraintWeights,
    ) {
        let Neg::Var(tail_var) = self.types.neg(tail).clone() else {
            let row = self.alloc_neg(Neg::Row(items, tail));
            self.add_upper_bound(source, row, weights);
            return;
        };

        let handled_families = self.neg_effect_families(&items);
        let active_facts = self.active_subtract_facts(source, &weights.left);
        let mut retained_items = items;
        for fact in &active_facts {
            retained_items = self
                .intersect_row_items_with_subtractability(retained_items, &fact.subtractability);
        }

        for fact in active_facts {
            self.record_subtract_fact(
                tail_var,
                SubtractFact {
                    id: fact.id,
                    subtractability: subtractability_minus_families(
                        fact.subtractability,
                        &handled_families,
                    ),
                },
            );
        }

        if retained_items.is_empty() {
            let source = self.alloc_pos(Pos::Var(source));
            self.enqueue_subtype(source, weights, tail);
        } else {
            let row = self.alloc_neg(Neg::Row(retained_items, tail));
            self.add_upper_bound(source, row, weights);
        }
    }

    fn active_subtract_facts(
        &self,
        var: TypeVar,
        cancelled: &ConstraintWeight,
    ) -> Vec<SubtractFact> {
        self.subtracts
            .facts(var)
            .iter()
            .filter(|fact| !cancelled.contains(fact.id))
            .cloned()
            .collect()
    }

    fn intersect_row_items_with_subtractability(
        &self,
        items: Vec<NegId>,
        subtractability: &Subtractability,
    ) -> Vec<NegId> {
        match subtractability {
            Subtractability::All => items,
            Subtractability::Empty => Vec::new(),
            Subtractability::Set(path, _) => items
                .into_iter()
                .filter(|item| self.neg_effect_family_matches(*item, path))
                .collect(),
            Subtractability::AllExcept(path, _) => items
                .into_iter()
                .filter(|item| !self.neg_effect_family_matches(*item, path))
                .collect(),
            Subtractability::AllExceptMany(families) => items
                .into_iter()
                .filter(|item| {
                    !families
                        .iter()
                        .any(|(path, _)| self.neg_effect_family_matches(*item, path))
                })
                .collect(),
        }
    }

    fn neg_effect_family_matches(&self, item: NegId, path: &[String]) -> bool {
        matches!(self.types.neg(item), Neg::Con(item_path, _) if item_path == path)
    }

    fn neg_effect_families(&self, items: &[NegId]) -> Vec<EffectFamily> {
        let mut families = Vec::new();
        for item in items {
            let Neg::Con(path, _) = self.types.neg(*item) else {
                continue;
            };
            push_unique_effect_family(
                &mut families,
                EffectFamily {
                    path: path.clone(),
                    args: Vec::new(),
                },
            );
        }
        families
    }

    fn add_lower_bound(&mut self, target: TypeVar, pos: PosId, weights: ConstraintWeights) {
        let pos = self.extrude_pos(pos, self.level_of(target));
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
        let neg = self.extrude_neg(neg, self.level_of(source));
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

    fn extrude_pos(&mut self, pos: PosId, target: TypeLevel) -> PosId {
        let mut ctx = ExtrudeCtx::new(target);
        self.extrude_pos_id(pos, &mut ctx);
        pos
    }

    fn extrude_neg(&mut self, neg: NegId, target: TypeLevel) -> NegId {
        let mut ctx = ExtrudeCtx::new(target);
        self.extrude_neg_id(neg, &mut ctx);
        neg
    }

    fn extrude_pos_id(&mut self, id: PosId, ctx: &mut ExtrudeCtx) {
        match self.types.pos(id).clone() {
            Pos::Bot => {}
            Pos::Var(var) => self.extrude_type_var(var, ctx),
            Pos::Con(_, args) => self.extrude_neu_ids(args, ctx),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_neg_id(arg, ctx);
                self.extrude_neg_id(arg_eff, ctx);
                self.extrude_pos_id(ret_eff, ctx);
                self.extrude_pos_id(ret, ctx);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
            }
            Pos::RecordTailSpread { fields, tail } => {
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
                self.extrude_pos_id(tail, ctx);
            }
            Pos::RecordHeadSpread { tail, fields } => {
                self.extrude_pos_id(tail, ctx);
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
            }
            Pos::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_pos_id(payload, ctx);
                    }
                }
            }
            Pos::Tuple(items) | Pos::Row(items) => {
                for item in items {
                    self.extrude_pos_id(item, ctx);
                }
            }
            Pos::NonSubtract(pos, _) => self.extrude_pos_id(pos, ctx),
            Pos::Union(left, right) => {
                self.extrude_pos_id(left, ctx);
                self.extrude_pos_id(right, ctx);
            }
        }
    }

    fn extrude_neg_id(&mut self, id: NegId, ctx: &mut ExtrudeCtx) {
        match self.types.neg(id).clone() {
            Neg::Top | Neg::Bot => {}
            Neg::Var(var) => self.extrude_type_var(var, ctx),
            Neg::Con(_, args) => self.extrude_neu_ids(args, ctx),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_pos_id(arg, ctx);
                self.extrude_pos_id(arg_eff, ctx);
                self.extrude_neg_id(ret_eff, ctx);
                self.extrude_neg_id(ret, ctx);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.extrude_neg_id(field.value, ctx);
                }
            }
            Neg::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_neg_id(payload, ctx);
                    }
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.extrude_neg_id(item, ctx);
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.extrude_neg_id(item, ctx);
                }
                self.extrude_neg_id(tail, ctx);
            }
            Neg::Intersection(left, right) => {
                self.extrude_neg_id(left, ctx);
                self.extrude_neg_id(right, ctx);
            }
        }
    }

    fn extrude_neu_ids(&mut self, ids: Vec<NeuId>, ctx: &mut ExtrudeCtx) {
        for id in ids {
            self.extrude_neu_id(id, ctx);
        }
    }

    fn extrude_neu_id(&mut self, id: NeuId, ctx: &mut ExtrudeCtx) {
        match self.types.neu(id).clone() {
            Neu::Bounds(lower, var, upper) => {
                self.extrude_pos_id(lower, ctx);
                self.extrude_type_var(var, ctx);
                self.extrude_neg_id(upper, ctx);
            }
            Neu::Con(_, args) => self.extrude_neu_ids(args, ctx),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_neu_id(arg, ctx);
                self.extrude_neu_id(arg_eff, ctx);
                self.extrude_neu_id(ret_eff, ctx);
                self.extrude_neu_id(ret, ctx);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.extrude_neu_id(field.value, ctx);
                }
            }
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_neu_id(payload, ctx);
                    }
                }
            }
            Neu::Tuple(items) => self.extrude_neu_ids(items, ctx),
        }
    }

    fn extrude_type_var(&mut self, var: TypeVar, ctx: &mut ExtrudeCtx) {
        if self.level_of(var) <= ctx.target {
            return;
        }
        if !ctx.visited.insert(var) {
            return;
        }
        self.levels.lower_to(var, ctx.target);
        let bounds = self.bounds.of(var).cloned();
        if let Some(bounds) = bounds {
            for lower in bounds.lowers {
                self.extrude_pos_id(lower.pos, ctx);
            }
            for upper in bounds.uppers {
                self.extrude_neg_id(upper.neg, ctx);
            }
        }
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

    pub fn with_left(&self, id: SubtractId) -> Self {
        Self {
            left: self.left.union(&ConstraintWeight::from_ids([id])),
            right: self.right.clone(),
        }
    }

    pub fn both_from_right(&self) -> Self {
        Self {
            left: self.right.clone(),
            right: self.right.clone(),
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct EffectFamily {
    path: Vec<String>,
    args: Vec<NeuId>,
}

fn subtractability_minus_families(
    subtractability: Subtractability,
    handled: &[EffectFamily],
) -> Subtractability {
    if handled.is_empty() {
        return subtractability;
    }
    match subtractability {
        Subtractability::Empty => Subtractability::Empty,
        Subtractability::All => all_except_families(handled.iter().cloned()),
        Subtractability::Set(path, args) => {
            if handled.iter().any(|family| family.path == path) {
                Subtractability::Empty
            } else {
                Subtractability::Set(path, args)
            }
        }
        Subtractability::AllExcept(path, args) => all_except_families(
            std::iter::once(EffectFamily { path, args }).chain(handled.iter().cloned()),
        ),
        Subtractability::AllExceptMany(families) => all_except_families(
            families
                .into_iter()
                .map(|(path, args)| EffectFamily { path, args })
                .chain(handled.iter().cloned()),
        ),
    }
}

fn all_except_families(families: impl IntoIterator<Item = EffectFamily>) -> Subtractability {
    let mut out = Vec::new();
    for family in families {
        push_unique_effect_family(&mut out, family);
    }
    match out.as_slice() {
        [] => Subtractability::All,
        [family] => Subtractability::AllExcept(family.path.clone(), family.args.clone()),
        _ => Subtractability::AllExceptMany(
            out.into_iter()
                .map(|family| (family.path, family.args))
                .collect(),
        ),
    }
}

fn push_unique_effect_family(families: &mut Vec<EffectFamily>, family: EffectFamily) {
    if !families.iter().any(|existing| existing.path == family.path) {
        families.push(family);
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
    fn lower_bound_extrudes_deeper_positive_variables_to_target_level() {
        let mut machine = ConstraintMachine::new();
        let target = TypeVar(0);
        let inner = TypeVar(1);
        let root = TypeLevel::root();
        let child = root.child();
        machine.register_type_var(target, root);
        machine.register_type_var(inner, child);
        let lower = machine.alloc_pos(Pos::Var(inner));
        let upper = machine.alloc_neg(Neg::Var(target));

        machine.subtype(lower, upper);

        assert_eq!(machine.level_of(inner), root);
        let bounds = machine.bounds().of(target).expect("target bounds");
        assert_eq!(
            bounds.lowers(),
            &[WeightedLowerBound {
                pos: lower,
                weights: ConstraintWeights::empty()
            }]
        );
    }

    #[test]
    fn lower_bound_extrudes_secondary_level_variables_to_target_level() {
        let mut machine = ConstraintMachine::new();
        let target = TypeVar(0);
        let inner = TypeVar(1);
        let root = TypeLevel::root();
        machine.register_type_var(target, root);
        machine.register_type_var(inner, TypeLevel::secondary());
        let lower = machine.alloc_pos(Pos::Var(inner));
        let upper = machine.alloc_neg(Neg::Var(target));

        machine.subtype(lower, upper);

        assert_eq!(machine.level_of(inner), root);
    }

    #[test]
    fn upper_bound_extrudes_deeper_negative_variables_to_source_level() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let inner = TypeVar(1);
        let root = TypeLevel::root();
        let child = root.child();
        machine.register_type_var(source, root);
        machine.register_type_var(inner, child);
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Var(inner));

        machine.subtype(lower, upper);

        assert_eq!(machine.level_of(inner), root);
        let bounds = machine.bounds().of(source).expect("source bounds");
        assert_eq!(
            bounds.uppers(),
            &[WeightedUpperBound {
                neg: upper,
                weights: ConstraintWeights::empty()
            }]
        );
    }

    #[test]
    fn extrusion_recurses_through_neutral_constructor_args_and_existing_bounds() {
        let mut machine = ConstraintMachine::new();
        let target = TypeVar(0);
        let inner = TypeVar(1);
        let bound_var = TypeVar(2);
        let root = TypeLevel::root();
        let child = root.child();
        machine.register_type_var(target, root);
        machine.register_type_var(inner, child);
        machine.register_type_var(bound_var, child);
        let inner_as_lower = machine.alloc_pos(Pos::Var(inner));
        let bound_var_as_upper = machine.alloc_neg(Neg::Var(bound_var));
        machine.subtype(inner_as_lower, bound_var_as_upper);

        let arg_lower = machine.alloc_pos(Pos::Con(vec!["lower".into()], vec![]));
        let arg_upper = machine.alloc_neg(Neg::Con(vec!["upper".into()], vec![]));
        let arg = machine.alloc_neu(Neu::Bounds(arg_lower, inner, arg_upper));
        let lower = machine.alloc_pos(Pos::Con(vec!["box".into()], vec![arg]));
        let upper = machine.alloc_neg(Neg::Var(target));

        machine.subtype(lower, upper);

        assert_eq!(machine.level_of(inner), root);
        assert_eq!(machine.level_of(bound_var), root);
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

    #[test]
    fn constructor_args_propagate_invariant_neutral_bounds() {
        let mut machine = ConstraintMachine::new();
        let lower_arg_var = TypeVar(10);
        let upper_arg_var = TypeVar(11);
        let lower_arg_lower = machine.alloc_pos(Pos::Con(vec!["lower_arg_lower".into()], vec![]));
        let lower_arg_upper = machine.alloc_neg(Neg::Con(vec!["lower_arg_upper".into()], vec![]));
        let lower_arg =
            machine.alloc_neu(Neu::Bounds(lower_arg_lower, lower_arg_var, lower_arg_upper));
        let upper_arg_lower = machine.alloc_pos(Pos::Con(vec!["upper_arg_lower".into()], vec![]));
        let upper_arg_upper = machine.alloc_neg(Neg::Con(vec!["upper_arg_upper".into()], vec![]));
        let upper_arg =
            machine.alloc_neu(Neu::Bounds(upper_arg_lower, upper_arg_var, upper_arg_upper));
        let lower = machine.alloc_pos(Pos::Con(vec!["box".into()], vec![lower_arg]));
        let upper = machine.alloc_neg(Neg::Con(vec!["box".into()], vec![upper_arg]));
        let weights = ConstraintWeights {
            left: ConstraintWeight::from_ids([SubtractId(0)]),
            right: ConstraintWeight::from_ids([SubtractId(1)]),
        };

        machine.weighted_subtype(lower, weights.clone(), upper);

        let lower_arg_var_pos = machine.alloc_pos(Pos::Var(lower_arg_var));
        let upper_arg_var_neg = machine.alloc_neg(Neg::Var(upper_arg_var));
        let lower_arg_union = machine.alloc_pos(Pos::Union(lower_arg_lower, lower_arg_var_pos));
        let upper_arg_intersection =
            machine.alloc_neg(Neg::Intersection(upper_arg_var_neg, upper_arg_upper));
        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: lower_arg_union,
            upper: upper_arg_intersection,
            weights: weights.clone(),
        }));

        let upper_arg_var_pos = machine.alloc_pos(Pos::Var(upper_arg_var));
        let lower_arg_var_neg = machine.alloc_neg(Neg::Var(lower_arg_var));
        let upper_arg_union = machine.alloc_pos(Pos::Union(upper_arg_lower, upper_arg_var_pos));
        let lower_arg_intersection =
            machine.alloc_neg(Neg::Intersection(lower_arg_var_neg, lower_arg_upper));
        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: upper_arg_union,
            upper: lower_arg_intersection,
            weights: weights.swapped(),
        }));
    }

    #[test]
    fn mismatched_constructors_emit_nominal_cast_event() {
        let mut machine = ConstraintMachine::new();
        let lower = machine.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
        let upper = machine.alloc_neg(Neg::Con(vec!["user_id".into()], Vec::new()));

        machine.subtype(lower, upper);

        assert_eq!(
            machine.events(),
            &[ConstraintEvent::NominalCastNeeded {
                lower,
                upper,
                source: vec!["int".into()],
                target: vec!["user_id".into()],
                weights: ConstraintWeights::empty()
            }]
        );
    }

    #[test]
    fn neutral_structures_build_regular_upper_and_lower_bounds() {
        let mut machine = ConstraintMachine::new();
        let lower_item_var = TypeVar(10);
        let upper_item_var = TypeVar(11);
        let lower_item_lower = machine.alloc_pos(Pos::Con(vec!["lower_item_lower".into()], vec![]));
        let lower_item_upper = machine.alloc_neg(Neg::Con(vec!["lower_item_upper".into()], vec![]));
        let lower_item = machine.alloc_neu(Neu::Bounds(
            lower_item_lower,
            lower_item_var,
            lower_item_upper,
        ));
        let upper_item_lower = machine.alloc_pos(Pos::Con(vec!["upper_item_lower".into()], vec![]));
        let upper_item_upper = machine.alloc_neg(Neg::Con(vec!["upper_item_upper".into()], vec![]));
        let upper_item = machine.alloc_neu(Neu::Bounds(
            upper_item_lower,
            upper_item_var,
            upper_item_upper,
        ));
        let lower_arg = machine.alloc_neu(Neu::Tuple(vec![lower_item]));
        let upper_arg = machine.alloc_neu(Neu::Tuple(vec![upper_item]));
        let lower = machine.alloc_pos(Pos::Con(vec!["box".into()], vec![lower_arg]));
        let upper = machine.alloc_neg(Neg::Con(vec!["box".into()], vec![upper_arg]));

        machine.subtype(lower, upper);

        let lower_item_var_pos = machine.alloc_pos(Pos::Var(lower_item_var));
        let upper_item_var_neg = machine.alloc_neg(Neg::Var(upper_item_var));
        let lower_item_union = machine.alloc_pos(Pos::Union(lower_item_lower, lower_item_var_pos));
        let upper_item_intersection =
            machine.alloc_neg(Neg::Intersection(upper_item_var_neg, upper_item_upper));
        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: lower_item_union,
            upper: upper_item_intersection,
            weights: ConstraintWeights::empty(),
        }));

        let upper_item_var_pos = machine.alloc_pos(Pos::Var(upper_item_var));
        let lower_item_var_neg = machine.alloc_neg(Neg::Var(lower_item_var));
        let upper_item_union = machine.alloc_pos(Pos::Union(upper_item_lower, upper_item_var_pos));
        let lower_item_intersection =
            machine.alloc_neg(Neg::Intersection(lower_item_var_neg, lower_item_upper));
        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: upper_item_union,
            upper: lower_item_intersection,
            weights: ConstraintWeights::empty(),
        }));
    }

    #[test]
    fn record_fields_propagate_matching_field_constraints() {
        let mut machine = ConstraintMachine::new();
        let lower_x = machine.alloc_pos(Pos::Con(vec!["lower_x".into()], vec![]));
        let upper_x = machine.alloc_neg(Neg::Con(vec!["upper_x".into()], vec![]));
        let lower = machine.alloc_pos(Pos::Record(vec![RecordField {
            name: "x".into(),
            value: lower_x,
            optional: false,
        }]));
        let upper = machine.alloc_neg(Neg::Record(vec![RecordField {
            name: "x".into(),
            value: upper_x,
            optional: false,
        }]));

        machine.subtype(lower, upper);

        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: lower_x,
            upper: upper_x,
            weights: ConstraintWeights::empty(),
        }));
    }

    #[test]
    fn record_tail_spread_sends_missing_fields_to_tail() {
        let mut machine = ConstraintMachine::new();
        let tail = machine.alloc_pos(Pos::Var(TypeVar(0)));
        let upper_y = machine.alloc_neg(Neg::Con(vec!["upper_y".into()], vec![]));
        let upper = machine.alloc_neg(Neg::Record(vec![RecordField {
            name: "y".into(),
            value: upper_y,
            optional: false,
        }]));
        let lower = machine.alloc_pos(Pos::RecordTailSpread {
            fields: Vec::new(),
            tail,
        });
        let expected_tail_upper = machine.alloc_neg(Neg::Record(vec![RecordField {
            name: "y".into(),
            value: upper_y,
            optional: false,
        }]));

        machine.subtype(lower, upper);

        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: tail,
            upper: expected_tail_upper,
            weights: ConstraintWeights::empty(),
        }));
    }

    #[test]
    fn variant_payloads_propagate_matching_tag_constraints() {
        let mut machine = ConstraintMachine::new();
        let lower_payload = machine.alloc_pos(Pos::Con(vec!["lower_payload".into()], vec![]));
        let upper_payload = machine.alloc_neg(Neg::Con(vec!["upper_payload".into()], vec![]));
        let lower = machine.alloc_pos(Pos::PolyVariant(vec![("some".into(), vec![lower_payload])]));
        let upper = machine.alloc_neg(Neg::PolyVariant(vec![("some".into(), vec![upper_payload])]));

        machine.subtype(lower, upper);

        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: lower_payload,
            upper: upper_payload,
            weights: ConstraintWeights::empty(),
        }));
    }

    #[test]
    fn row_items_use_remaining_upper_rows_for_variables_and_tail_for_unmatched_atoms() {
        let mut machine = ConstraintMachine::new();
        let io_pos = machine.alloc_pos(Pos::Con(vec!["io".into()], vec![]));
        let io_neg = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
        let fs_pos = machine.alloc_pos(Pos::Con(vec!["fs".into()], vec![]));
        let row_var = machine.alloc_pos(Pos::Var(TypeVar(0)));
        let upper_tail = machine.alloc_neg(Neg::Var(TypeVar(1)));
        let lower = machine.alloc_pos(Pos::Row(vec![io_pos, fs_pos, row_var]));
        let upper = machine.alloc_neg(Neg::Row(vec![io_neg], upper_tail));

        machine.subtype(lower, upper);

        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: fs_pos,
            upper: upper_tail,
            weights: ConstraintWeights::empty(),
        }));
        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: row_var,
            upper: upper_tail,
            weights: ConstraintWeights::empty(),
        }));
        let old_row_var_upper = machine.alloc_neg(Neg::Row(vec![io_neg], upper_tail));
        assert!(!machine.seen.contains(&SubtypeConstraint {
            lower: row_var,
            upper: old_row_var_upper,
            weights: ConstraintWeights::empty(),
        }));
        assert!(!machine.seen.contains(&SubtypeConstraint {
            lower: io_pos,
            upper: upper_tail,
            weights: ConstraintWeights::empty(),
        }));
    }

    #[test]
    fn pos_row_variable_items_use_subtractable_row_upper_processing() {
        let mut machine = ConstraintMachine::new();
        let row_var = TypeVar(0);
        let tail_var = TypeVar(1);
        let subtract = SubtractId(0);
        machine.subtract_fact(
            row_var,
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        );
        machine.take_events();
        let row_var_pos = machine.alloc_pos(Pos::Var(row_var));
        let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
        let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
        let tail = machine.alloc_neg(Neg::Var(tail_var));
        let lower = machine.alloc_pos(Pos::Row(vec![row_var_pos]));
        let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));
        let expected_row_var_upper = machine.alloc_neg(Neg::Row(vec![io], tail));

        machine.subtype(lower, upper);

        let bounds = machine.bounds().of(row_var).expect("row var bounds");
        assert_eq!(
            bounds.uppers(),
            &[WeightedUpperBound {
                neg: expected_row_var_upper,
                weights: ConstraintWeights::empty()
            }]
        );
        assert_eq!(
            machine.subtracts().facts(tail_var),
            &[SubtractFact {
                id: subtract,
                subtractability: Subtractability::Empty
            }]
        );
    }

    #[test]
    fn pos_row_concrete_effect_items_compare_matching_payloads() {
        let mut machine = ConstraintMachine::new();
        let lower_payload_var = TypeVar(10);
        let upper_payload_var = TypeVar(11);
        let lower_payload_lower =
            machine.alloc_pos(Pos::Con(vec!["lower_payload_lower".into()], vec![]));
        let lower_payload_upper =
            machine.alloc_neg(Neg::Con(vec!["lower_payload_upper".into()], vec![]));
        let lower_payload = machine.alloc_neu(Neu::Bounds(
            lower_payload_lower,
            lower_payload_var,
            lower_payload_upper,
        ));
        let upper_payload_lower =
            machine.alloc_pos(Pos::Con(vec!["upper_payload_lower".into()], vec![]));
        let upper_payload_upper =
            machine.alloc_neg(Neg::Con(vec!["upper_payload_upper".into()], vec![]));
        let upper_payload = machine.alloc_neu(Neu::Bounds(
            upper_payload_lower,
            upper_payload_var,
            upper_payload_upper,
        ));
        let lower_item = machine.alloc_pos(Pos::Con(
            crate::std_paths::control_var_ref_update_effect(),
            vec![lower_payload],
        ));
        let upper_item = machine.alloc_neg(Neg::Con(
            crate::std_paths::control_var_ref_update_effect(),
            vec![upper_payload],
        ));
        let upper_tail = machine.alloc_neg(Neg::Var(TypeVar(12)));
        let lower = machine.alloc_pos(Pos::Row(vec![lower_item]));
        let upper = machine.alloc_neg(Neg::Row(vec![upper_item], upper_tail));

        machine.subtype(lower, upper);

        let lower_payload_var_pos = machine.alloc_pos(Pos::Var(lower_payload_var));
        let lower_payload_union =
            machine.alloc_pos(Pos::Union(lower_payload_lower, lower_payload_var_pos));
        let upper_payload_var_neg = machine.alloc_neg(Neg::Var(upper_payload_var));
        let upper_payload_intersection = machine.alloc_neg(Neg::Intersection(
            upper_payload_var_neg,
            upper_payload_upper,
        ));
        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: lower_payload_union,
            upper: upper_payload_intersection,
            weights: ConstraintWeights::empty(),
        }));
        let upper_payload_var_pos = machine.alloc_pos(Pos::Var(upper_payload_var));
        let upper_payload_union =
            machine.alloc_pos(Pos::Union(upper_payload_lower, upper_payload_var_pos));
        let lower_payload_var_neg = machine.alloc_neg(Neg::Var(lower_payload_var));
        let lower_payload_intersection = machine.alloc_neg(Neg::Intersection(
            lower_payload_var_neg,
            lower_payload_upper,
        ));
        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: upper_payload_union,
            upper: lower_payload_intersection,
            weights: ConstraintWeights::empty(),
        }));
        assert!(!machine.seen.contains(&SubtypeConstraint {
            lower: lower_item,
            upper: upper_tail,
            weights: ConstraintWeights::empty(),
        }));
    }

    #[test]
    fn pos_row_concrete_effect_items_match_by_path() {
        let mut machine = ConstraintMachine::new();
        let payload_lower = machine.alloc_pos(Pos::Bot);
        let payload_upper = machine.alloc_neg(Neg::Top);
        let payload = machine.alloc_neu(Neu::Bounds(payload_lower, TypeVar(10), payload_upper));
        let lower_item = machine.alloc_pos(Pos::Con(vec!["effect".into()], vec![payload]));
        let upper_item = machine.alloc_neg(Neg::Con(vec!["effect".into()], Vec::new()));
        let upper_tail = machine.alloc_neg(Neg::Var(TypeVar(11)));
        let lower = machine.alloc_pos(Pos::Row(vec![lower_item]));
        let upper = machine.alloc_neg(Neg::Row(vec![upper_item], upper_tail));

        machine.subtype(lower, upper);

        assert!(!machine.seen.contains(&SubtypeConstraint {
            lower: lower_item,
            upper: upper_tail,
            weights: ConstraintWeights::empty(),
        }));
    }

    #[test]
    fn var_to_effect_row_upper_filters_items_by_active_subtract_facts() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let tail_var = TypeVar(1);
        let subtract = SubtractId(0);
        machine.subtract_fact(
            source,
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        );
        machine.take_events();
        let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
        let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
        let tail = machine.alloc_neg(Neg::Var(tail_var));
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));
        let expected_upper = machine.alloc_neg(Neg::Row(vec![io], tail));

        machine.subtype(lower, upper);

        let bounds = machine.bounds().of(source).expect("source bounds");
        assert_eq!(
            bounds.uppers(),
            &[WeightedUpperBound {
                neg: expected_upper,
                weights: ConstraintWeights::empty()
            }]
        );
        assert_eq!(
            machine.subtracts().facts(tail_var),
            &[SubtractFact {
                id: subtract,
                subtractability: Subtractability::Empty
            }]
        );
    }

    #[test]
    fn var_to_effect_row_upper_ignores_subtract_facts_cancelled_by_left_weight() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let tail_var = TypeVar(1);
        let subtract = SubtractId(0);
        machine.subtract_fact(
            source,
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        );
        machine.take_events();
        let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
        let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
        let tail = machine.alloc_neg(Neg::Var(tail_var));
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));
        let weights = ConstraintWeights {
            left: ConstraintWeight::from_ids([subtract]),
            right: ConstraintWeight::empty(),
        };

        machine.weighted_subtype(lower, weights.clone(), upper);

        let bounds = machine.bounds().of(source).expect("source bounds");
        assert_eq!(
            bounds.uppers(),
            &[WeightedUpperBound {
                neg: upper,
                weights
            }]
        );
        assert!(machine.subtracts().facts(tail_var).is_empty());
    }

    #[test]
    fn var_to_effect_row_upper_stores_tail_when_subtract_intersection_is_empty() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let tail_var = TypeVar(1);
        let subtract = SubtractId(0);
        machine.subtract_fact(source, subtract, Subtractability::Empty);
        machine.take_events();
        let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
        let tail = machine.alloc_neg(Neg::Var(tail_var));
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Row(vec![io], tail));

        machine.subtype(lower, upper);

        let bounds = machine.bounds().of(source).expect("source bounds");
        assert_eq!(
            bounds.uppers(),
            &[WeightedUpperBound {
                neg: tail,
                weights: ConstraintWeights::empty()
            }]
        );
        assert_eq!(
            machine.subtracts().facts(tail_var),
            &[SubtractFact {
                id: subtract,
                subtractability: Subtractability::Empty
            }]
        );
    }

    #[test]
    fn var_to_effect_row_upper_removes_all_except_excluded_effect_family() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let tail_var = TypeVar(1);
        let subtract = SubtractId(0);
        machine.subtract_fact(
            source,
            subtract,
            Subtractability::AllExcept(vec!["io".into()], Vec::new()),
        );
        machine.take_events();
        let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
        let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
        let tail = machine.alloc_neg(Neg::Var(tail_var));
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));
        let expected_upper = machine.alloc_neg(Neg::Row(vec![nondet], tail));

        machine.subtype(lower, upper);

        let bounds = machine.bounds().of(source).expect("source bounds");
        assert_eq!(
            bounds.uppers(),
            &[WeightedUpperBound {
                neg: expected_upper,
                weights: ConstraintWeights::empty()
            }]
        );
        assert_eq!(
            machine.subtracts().facts(tail_var),
            &[SubtractFact {
                id: subtract,
                subtractability: Subtractability::AllExceptMany(vec![
                    (vec!["io".into()], Vec::new()),
                    (vec!["nondet".into()], Vec::new())
                ])
            }]
        );
    }

    #[test]
    fn var_to_effect_row_upper_moves_all_subtract_to_tail_minus_handled_families() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let tail_var = TypeVar(1);
        let subtract = SubtractId(0);
        machine.subtract_fact(source, subtract, Subtractability::All);
        machine.take_events();
        let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
        let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
        let tail = machine.alloc_neg(Neg::Var(tail_var));
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));

        machine.subtype(lower, upper);

        assert_eq!(
            machine.subtracts().facts(tail_var),
            &[SubtractFact {
                id: subtract,
                subtractability: Subtractability::AllExceptMany(vec![
                    (vec!["io".into()], Vec::new()),
                    (vec!["nondet".into()], Vec::new())
                ])
            }]
        );
    }

    #[test]
    fn pure_function_argument_effect_passes_through_with_right_side_weights() {
        let mut machine = ConstraintMachine::new();
        let lhs_arg = machine.alloc_neg(Neg::Con(vec!["lhs_arg".into()], vec![]));
        let lhs_arg_eff = machine.alloc_neg(Neg::Bot);
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
        let expected_passthrough_weights = ConstraintWeights {
            left: ConstraintWeight::from_ids([SubtractId(1)]),
            right: ConstraintWeight::from_ids([SubtractId(1)]),
        };

        machine.weighted_subtype(lower, weights.clone(), upper);

        assert!(machine.seen.contains(&SubtypeConstraint {
            lower: rhs_arg_eff,
            upper: rhs_ret_eff,
            weights: expected_passthrough_weights,
        }));
        assert!(!machine.seen.contains(&SubtypeConstraint {
            lower: rhs_arg_eff,
            upper: rhs_ret_eff,
            weights: ConstraintWeights::empty(),
        }));
        assert!(!machine.seen.contains(&SubtypeConstraint {
            lower: rhs_arg_eff,
            upper: rhs_ret_eff,
            weights,
        }));
    }

    #[test]
    fn non_subtract_adds_left_weight_before_continuing() {
        let mut machine = ConstraintMachine::new();
        let target = TypeVar(0);
        let inner = machine.alloc_pos(Pos::Con(vec!["io".into()], vec![]));
        let subtract = SubtractId(0);
        let lower = machine.alloc_pos(Pos::NonSubtract(inner, subtract));
        let upper = machine.alloc_neg(Neg::Var(target));

        machine.subtype(lower, upper);

        let bounds = machine.bounds().of(target).expect("target bounds");
        assert_eq!(
            bounds.lowers(),
            &[WeightedLowerBound {
                pos: inner,
                weights: ConstraintWeights {
                    left: ConstraintWeight::from_ids([subtract]),
                    right: ConstraintWeight::empty()
                }
            }]
        );
    }
}
