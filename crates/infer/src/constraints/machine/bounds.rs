use super::*;

impl ConstraintMachine {
    pub(in crate::constraints) fn add_lower_bound(
        &mut self,
        target: TypeVar,
        pos: PosId,
        weights: ConstraintWeights,
    ) {
        let pos = self.extrude_pos(pos, self.level_of(target));
        if !self.bounds.add_lower(target, pos, weights.clone()) {
            return;
        }
        self.events.push(ConstraintEvent::LowerBoundAdded {
            var: target,
            bound: pos,
            weights: weights.clone(),
        });
        trace_var_bounds("after lower", target, self.bounds.of(target), &self.types);

        let uppers = self
            .bounds
            .of(target)
            .map(|bounds| bounds.uppers.clone())
            .unwrap_or_default();
        trace_bound_replay_start("lower", target, uppers.len());
        for (index, upper) in uppers.into_iter().enumerate() {
            trace_bound_replay_progress("lower", target, index);
            let replay_weights = weights.compose_for_replay(&upper.weights);
            if self.is_var_var_replay(pos, upper.neg) && !replay_weights.is_empty() {
                self.add_var_var_bound_without_replay(pos, upper.neg, replay_weights);
                continue;
            }
            self.enqueue_subtype(pos, replay_weights, upper.neg);
        }
    }

    pub(in crate::constraints) fn add_upper_bound(
        &mut self,
        source: TypeVar,
        neg: NegId,
        weights: ConstraintWeights,
    ) {
        let neg = self.extrude_neg(neg, self.level_of(source));
        if !self.bounds.add_upper(source, neg, weights.clone()) {
            return;
        }
        self.events.push(ConstraintEvent::UpperBoundAdded {
            var: source,
            bound: neg,
            weights: weights.clone(),
        });
        trace_var_bounds("after upper", source, self.bounds.of(source), &self.types);

        let lowers = self
            .bounds
            .of(source)
            .map(|bounds| bounds.lowers.clone())
            .unwrap_or_default();
        trace_bound_replay_start("upper", source, lowers.len());
        for (index, lower) in lowers.into_iter().enumerate() {
            trace_bound_replay_progress("upper", source, index);
            let replay_weights = lower.weights.compose_for_replay(&weights);
            if self.is_var_var_replay(lower.pos, neg) && !replay_weights.is_empty() {
                self.add_var_var_bound_without_replay(lower.pos, neg, replay_weights);
                continue;
            }
            self.enqueue_subtype(lower.pos, replay_weights, neg);
        }
    }

    pub(in crate::constraints) fn add_var_var_bound_without_replay(
        &mut self,
        lower: PosId,
        upper: NegId,
        weights: ConstraintWeights,
    ) {
        let (Pos::Var(lower_var), Neg::Var(upper_var)) =
            (self.types.pos(lower).clone(), self.types.neg(upper).clone())
        else {
            return;
        };
        if lower_var == upper_var {
            return;
        }
        if !self.record_var_var_pair(lower_var, upper_var, &weights) {
            return;
        }
        let upper = self.extrude_neg(upper, self.level_of(lower_var));
        if self.bounds.add_upper(lower_var, upper, weights.clone()) {
            self.events.push(ConstraintEvent::UpperBoundAdded {
                var: lower_var,
                bound: upper,
                weights: weights.clone(),
            });
            trace_var_bounds(
                "after var-var upper",
                lower_var,
                self.bounds.of(lower_var),
                &self.types,
            );
            let lowers = self
                .bounds
                .of(lower_var)
                .map(|bounds| bounds.lowers.clone())
                .unwrap_or_default();
            for lower_bound in lowers {
                if matches!(self.types.pos(lower_bound.pos), Pos::Var(_)) {
                    continue;
                }
                let replay_weights = lower_bound.weights.compose_for_replay(&weights);
                self.enqueue_subtype(lower_bound.pos, replay_weights, upper);
            }
        }

        let lower = self.extrude_pos(lower, self.level_of(upper_var));
        if self.bounds.add_lower(upper_var, lower, weights.clone()) {
            self.events.push(ConstraintEvent::LowerBoundAdded {
                var: upper_var,
                bound: lower,
                weights: weights.clone(),
            });
            trace_var_bounds(
                "after var-var lower",
                upper_var,
                self.bounds.of(upper_var),
                &self.types,
            );
            let uppers = self
                .bounds
                .of(upper_var)
                .map(|bounds| bounds.uppers.clone())
                .unwrap_or_default();
            for upper_bound in uppers {
                if matches!(self.types.neg(upper_bound.neg), Neg::Var(_)) {
                    continue;
                }
                let replay_weights = weights.compose_for_replay(&upper_bound.weights);
                self.enqueue_subtype(lower, replay_weights, upper_bound.neg);
            }
        }
    }

    pub(in crate::constraints) fn is_var_var_replay(&self, lower: PosId, upper: NegId) -> bool {
        matches!(self.types.pos(lower), Pos::Var(_)) && matches!(self.types.neg(upper), Neg::Var(_))
    }

    pub(in crate::constraints) fn extrude_pos(&mut self, pos: PosId, target: TypeLevel) -> PosId {
        let mut ctx = ExtrudeCtx::new(target);
        self.extrude_pos_id(pos, &mut ctx);
        pos
    }

    pub(in crate::constraints) fn extrude_neg(&mut self, neg: NegId, target: TypeLevel) -> NegId {
        let mut ctx = ExtrudeCtx::new(target);
        self.extrude_neg_id(neg, &mut ctx);
        neg
    }

    pub(in crate::constraints) fn extrude_pos_id(&mut self, id: PosId, ctx: &mut ExtrudeCtx) {
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
            Pos::Stack { inner, .. } => self.extrude_pos_id(inner, ctx),
            Pos::NonSubtract(pos, _) => self.extrude_pos_id(pos, ctx),
            Pos::Union(left, right) => {
                self.extrude_pos_id(left, ctx);
                self.extrude_pos_id(right, ctx);
            }
        }
    }

    pub(in crate::constraints) fn extrude_neg_id(&mut self, id: NegId, ctx: &mut ExtrudeCtx) {
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
            Neg::Stack { inner, .. } => self.extrude_neg_id(inner, ctx),
            Neg::Intersection(left, right) => {
                self.extrude_neg_id(left, ctx);
                self.extrude_neg_id(right, ctx);
            }
        }
    }

    pub(in crate::constraints) fn extrude_neu_ids(
        &mut self,
        ids: Vec<NeuId>,
        ctx: &mut ExtrudeCtx,
    ) {
        for id in ids {
            self.extrude_neu_id(id, ctx);
        }
    }

    pub(in crate::constraints) fn extrude_neu_id(&mut self, id: NeuId, ctx: &mut ExtrudeCtx) {
        match self.types.neu(id).clone() {
            Neu::Bounds(lower, upper) => {
                self.extrude_pos_id(lower, ctx);
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

    pub(in crate::constraints) fn extrude_type_var(&mut self, var: TypeVar, ctx: &mut ExtrudeCtx) {
        if self.level_of(var) <= ctx.target {
            return;
        }
        if !ctx.visited.insert(var) {
            return;
        }
        self.levels.lower_to(var, ctx.target);
        let bounds = self
            .bounds
            .of(var)
            .map(|bounds| (bounds.lowers.clone(), bounds.uppers.clone()));
        if let Some((lowers, uppers)) = bounds {
            for lower in lowers {
                self.extrude_pos_id(lower.pos, ctx);
            }
            for upper in uppers {
                self.extrude_neg_id(upper.neg, ctx);
            }
        }
    }
}
