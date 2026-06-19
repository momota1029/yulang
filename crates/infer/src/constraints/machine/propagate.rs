use super::*;

impl ConstraintMachine {
    pub(in crate::constraints) fn step_subtype(&mut self, constraint: SubtypeConstraint) {
        if matches!(self.types.pos(constraint.lower), Pos::Bot)
            || matches!(self.types.neg(constraint.upper), Neg::Top)
        {
            return;
        }
        if let Pos::Stack { inner, weight } = self.types.pos(constraint.lower) {
            let inner = *inner;
            let weight = weight.clone();
            if let Neg::Var(target) = self.types.neg(constraint.upper) {
                self.record_pre_pop_effect_families(*target, &weight);
            }
            self.enqueue_subtype(
                inner,
                constraint.weights.with_left_prefix(weight),
                constraint.upper,
            );
            return;
        }
        if let Pos::NonSubtract(pos, weight) = self.types.pos(constraint.lower) {
            let pos = *pos;
            let weight = weight.clone();
            self.enqueue_subtype(
                pos,
                constraint.weights.with_left_prefix(weight),
                constraint.upper,
            );
            return;
        }
        if let Neg::Stack { inner, weight } = self.types.neg(constraint.upper) {
            let inner = *inner;
            let weight = weight.clone();
            self.constrain_pos_lower_by_filter(constraint.lower, weight.filter_set());
            let stack_filter = common_stack_subtractability(weight.stack_items());
            self.constrain_pos_lower_by_filter(constraint.lower, &stack_filter);
            self.enqueue_subtype(
                constraint.lower,
                constraint.weights.with_right_suffix(weight),
                inner,
            );
            return;
        }
        if let Pos::Union(left, right) = self.types.pos(constraint.lower) {
            let left = *left;
            let right = *right;
            self.enqueue_subtype(left, constraint.weights.clone(), constraint.upper);
            self.enqueue_subtype(right, constraint.weights, constraint.upper);
            return;
        }
        if let Neg::Intersection(left, right) = self.types.neg(constraint.upper) {
            let left = *left;
            let right = *right;
            self.enqueue_subtype(constraint.lower, constraint.weights.clone(), left);
            self.enqueue_subtype(constraint.lower, constraint.weights, right);
            return;
        }
        if let Pos::Var(source) = self.types.pos(constraint.lower) {
            let source = *source;
            match self.types.neg(constraint.upper).clone() {
                Neg::Var(target) => {
                    if source == target {
                        return;
                    }
                    self.add_lower_bound(target, constraint.lower, constraint.weights.clone());
                    self.add_upper_bound(source, constraint.upper, constraint.weights);
                }
                Neg::Row(items, tail) => {
                    self.add_effect_row_upper_bound(source, items, tail, constraint.weights);
                }
                _ => {
                    self.add_upper_bound(source, constraint.upper, constraint.weights);
                }
            }
            return;
        }
        if let Neg::Var(target) = self.types.neg(constraint.upper) {
            self.add_lower_bound(*target, constraint.lower, constraint.weights);
            return;
        }
        match (
            self.types.pos(constraint.lower).clone(),
            self.types.neg(constraint.upper).clone(),
        ) {
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
                    let passthrough_ret_eff =
                        self.pure_arg_effect_passthrough_target(upper_ret_eff);
                    self.enqueue_subtype(
                        upper_arg_eff,
                        constraint.weights.both_from_right(),
                        passthrough_ret_eff,
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
            (Pos::Con(path, args), Neg::Row(upper_items, upper_tail)) => {
                self.enqueue_row_item_to_upper_row(
                    path,
                    args,
                    upper_items,
                    upper_tail,
                    constraint.weights,
                );
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

    pub(in crate::constraints) fn pure_arg_effect_passthrough_target(
        &self,
        ret_eff: NegId,
    ) -> NegId {
        let mut target = ret_eff;
        while let Neg::Stack { inner, .. } = self.types.neg(target) {
            target = *inner;
        }
        target
    }

    pub(in crate::constraints) fn enqueue_invariant_neu_args(
        &mut self,
        lower_args: Vec<NeuId>,
        upper_args: Vec<NeuId>,
        weights: ConstraintWeights,
    ) {
        for (lower, upper) in lower_args.into_iter().zip(upper_args) {
            self.enqueue_invariant_neu(lower, upper, weights.clone());
        }
    }

    pub(in crate::constraints) fn enqueue_invariant_neu(
        &mut self,
        lower: NeuId,
        upper: NeuId,
        weights: ConstraintWeights,
    ) {
        let (lower_pos, lower_neg) = self.neu_bounds(lower);
        let (upper_pos, upper_neg) = self.neu_bounds(upper);
        self.enqueue_subtype(lower_pos, weights.clone(), upper_neg);
        self.enqueue_subtype(upper_pos, weights.swapped(), lower_neg);
    }

    pub(in crate::constraints) fn neu_bounds(&mut self, id: NeuId) -> (PosId, NegId) {
        match self.types.neu(id).clone() {
            Neu::Bounds(lower, upper) => (lower, upper),
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

    pub(in crate::constraints) fn neu_record_fields(
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

    pub(in crate::constraints) fn neu_variant_items(
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

    pub(in crate::constraints) fn enqueue_record_fields(
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

    pub(in crate::constraints) fn enqueue_record_tail_spread(
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

    pub(in crate::constraints) fn enqueue_record_head_spread(
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

    pub(in crate::constraints) fn singleton_neg_record(
        &mut self,
        field: RecordField<NegId>,
    ) -> NegId {
        self.alloc_neg(Neg::Record(vec![field]))
    }

    pub(in crate::constraints) fn enqueue_variant_items(
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

    pub(in crate::constraints) fn enqueue_row_items(
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

            // A variable row item is handled by `α <: remaining row` itself. Treating it again as
            // a lower-tail item would add `upper_tail <: α` and create fresh residual cycles.
            let upper = if remaining_upper_items.is_empty() {
                upper_tail
            } else {
                self.alloc_neg(Neg::Row(remaining_upper_items.clone(), upper_tail))
            };
            self.enqueue_subtype(item, weights.clone(), upper);
        }

        self.enqueue_upper_tail_to_lower_row_tail(upper_tail, lower_tail_items, weights);
    }

    pub(in crate::constraints) fn row_items_can_match(&self, lower: PosId, upper: NegId) -> bool {
        match (self.types.pos(lower), self.types.neg(upper)) {
            (Pos::Con(lower_path, _), Neg::Con(upper_path, _)) => lower_path == upper_path,
            (Pos::Var(lower), Neg::Var(upper)) => lower == upper,
            _ => false,
        }
    }

    pub(in crate::constraints) fn enqueue_row_item_match(
        &mut self,
        lower: PosId,
        upper: NegId,
        weights: ConstraintWeights,
    ) {
        match (self.types.pos(lower).clone(), self.types.neg(upper).clone()) {
            (Pos::Con(lower_path, lower_args), Neg::Con(upper_path, upper_args))
                if lower_path == upper_path =>
            {
                self.enqueue_row_item_neu_args(lower_args, upper_args, weights);
            }
            (Pos::Var(lower), Neg::Var(upper)) if lower == upper => {}
            _ => {
                self.enqueue_subtype(lower, weights, upper);
            }
        }
    }

    pub(in crate::constraints) fn enqueue_row_item_neu_args(
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

    pub(in crate::constraints) fn enqueue_row_item_to_upper_row(
        &mut self,
        lower_path: Vec<String>,
        lower_args: Vec<NeuId>,
        upper_items: Vec<NegId>,
        upper_tail: NegId,
        weights: ConstraintWeights,
    ) {
        let Some(upper) = upper_items.into_iter().find(
            |upper| matches!(self.types.neg(*upper), Neg::Con(path, _) if path == &lower_path),
        ) else {
            let lower = self.alloc_pos(Pos::Con(lower_path, lower_args));
            self.enqueue_subtype(lower, weights, upper_tail);
            return;
        };
        let Neg::Con(_, upper_args) = self.types.neg(upper).clone() else {
            return;
        };
        self.enqueue_row_item_neu_args(lower_args, upper_args, weights);
    }

    pub(in crate::constraints) fn enqueue_upper_tail_to_lower_row_tail(
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

    pub(in crate::constraints) fn neg_row_from_pos_items(
        &mut self,
        items: Vec<PosId>,
    ) -> Option<NegId> {
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

    pub(in crate::constraints) fn neg_row_item_from_pos(&mut self, item: PosId) -> Option<NegId> {
        match self.types.pos(item).clone() {
            Pos::Var(var) => Some(self.alloc_neg(Neg::Var(var))),
            Pos::Con(path, args) => Some(self.alloc_neg(Neg::Con(path, args))),
            Pos::Row(items) => self.neg_row_from_pos_items(items),
            _ => None,
        }
    }
}
