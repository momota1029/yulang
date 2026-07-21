use super::*;

impl ConstraintMachine {
    pub(in crate::constraints) fn step_subtype(&mut self, parent: ConstraintRecordId) {
        let constraint = self.constraint_records[parent.0 as usize].key.clone();
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
            self.enqueue_derived_subtype(
                inner,
                constraint.weights.with_left_prefix(weight),
                constraint.upper,
                parent,
                StructuralDerivationRule::LowerStackNormalization,
            );
            return;
        }
        if let Pos::NonSubtract(pos, weight) = self.types.pos(constraint.lower) {
            let pos = *pos;
            let weight = weight.clone();
            self.enqueue_derived_subtype(
                pos,
                constraint.weights.with_left_prefix(weight),
                constraint.upper,
                parent,
                StructuralDerivationRule::LowerNonSubtractNormalization,
            );
            return;
        }
        if let Neg::Stack { inner, weight } = self.types.neg(constraint.upper) {
            let inner = *inner;
            let weight = weight.clone();
            self.constrain_pos_lower_by_filter(constraint.lower, weight.filter_set());
            let weight = weight.with_filter(Subtractability::All);
            let stack_filter = self.common_stack_subtractability(weight.active_stack_items());
            if !matches!(stack_filter, Subtractability::Empty) {
                self.constrain_pos_lower_by_filter(constraint.lower, &stack_filter);
            }
            self.enqueue_derived_subtype(
                constraint.lower,
                constraint.weights.with_right_suffix(weight),
                inner,
                parent,
                StructuralDerivationRule::UpperStackNormalization,
            );
            return;
        }
        if let Pos::Union(left, right) = self.types.pos(constraint.lower) {
            let left = *left;
            let right = *right;
            self.enqueue_derived_subtype(
                left,
                constraint.weights.clone(),
                constraint.upper,
                parent,
                StructuralDerivationRule::UnionBranch {
                    branch: StructuralIndex::from_usize(0),
                },
            );
            self.enqueue_derived_subtype(
                right,
                constraint.weights,
                constraint.upper,
                parent,
                StructuralDerivationRule::UnionBranch {
                    branch: StructuralIndex::from_usize(1),
                },
            );
            return;
        }
        if let Neg::Intersection(left, right) = self.types.neg(constraint.upper) {
            let left = *left;
            let right = *right;
            self.enqueue_derived_subtype(
                constraint.lower,
                constraint.weights.clone(),
                left,
                parent,
                StructuralDerivationRule::IntersectionBranch {
                    branch: StructuralIndex::from_usize(0),
                },
            );
            self.enqueue_derived_subtype(
                constraint.lower,
                constraint.weights,
                right,
                parent,
                StructuralDerivationRule::IntersectionBranch {
                    branch: StructuralIndex::from_usize(1),
                },
            );
            return;
        }
        if let Pos::Var(source) = self.types.pos(constraint.lower) {
            let source = *source;
            match self.types.neg(constraint.upper).clone() {
                Neg::Var(target) => {
                    if source == target {
                        return;
                    }
                    self.add_lower_bound(
                        target,
                        constraint.lower,
                        constraint.weights.clone(),
                        BoundDerivation::Constraint(parent),
                    );
                    self.add_upper_bound(
                        source,
                        constraint.upper,
                        constraint.weights,
                        BoundDerivation::Constraint(parent),
                    );
                }
                Neg::Row(items, tail) => {
                    self.add_effect_row_upper_bound(
                        source,
                        items,
                        tail,
                        constraint.weights,
                        Some(parent),
                    );
                }
                _ => {
                    self.add_upper_bound(
                        source,
                        constraint.upper,
                        constraint.weights,
                        BoundDerivation::Constraint(parent),
                    );
                }
            }
            return;
        }
        if let Neg::Var(target) = self.types.neg(constraint.upper) {
            self.add_lower_bound(
                *target,
                constraint.lower,
                constraint.weights,
                BoundDerivation::Constraint(parent),
            );
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
                self.enqueue_derived_subtype(
                    upper_arg,
                    swapped.clone(),
                    arg,
                    parent,
                    StructuralDerivationRule::FunctionArgument,
                );
                if matches!(self.types.neg(arg_eff), Neg::Bot) {
                    let passthrough_ret_eff =
                        self.pure_arg_effect_passthrough_target(upper_ret_eff);
                    self.enqueue_derived_subtype(
                        upper_arg_eff,
                        constraint.weights.both_from_right(),
                        passthrough_ret_eff,
                        parent,
                        StructuralDerivationRule::FunctionArgumentEffect {
                            pure_passthrough: true,
                        },
                    );
                } else {
                    self.enqueue_derived_subtype(
                        upper_arg_eff,
                        swapped,
                        arg_eff,
                        parent,
                        StructuralDerivationRule::FunctionArgumentEffect {
                            pure_passthrough: false,
                        },
                    );
                }
                self.enqueue_derived_subtype(
                    ret_eff,
                    constraint.weights.clone(),
                    upper_ret_eff,
                    parent,
                    StructuralDerivationRule::FunctionReturnEffect,
                );
                self.enqueue_derived_subtype(
                    ret,
                    constraint.weights,
                    upper_ret,
                    parent,
                    StructuralDerivationRule::FunctionReturn,
                );
            }
            (Pos::Con(lower_path, lower_args), Neg::Con(upper_path, upper_args))
                if lower_path == upper_path && lower_args.len() == upper_args.len() =>
            {
                self.enqueue_derived_invariant_neu_args(
                    lower_args,
                    upper_args,
                    constraint.weights,
                    parent,
                );
            }
            (Pos::Con(source, _), Neg::Con(target, _)) if source != target => {
                self.timing.record_nominal_cast_event(&source, &target);
                self.events.push(ConstraintEvent::NominalCastNeeded {
                    lower: constraint.lower,
                    upper: constraint.upper,
                    source,
                    target,
                    weights: constraint.weights,
                    producer: parent,
                });
            }
            (Pos::Con(path, args), Neg::Row(upper_items, upper_tail)) => {
                self.enqueue_row_item_to_upper_row(
                    path,
                    args,
                    upper_items,
                    upper_tail,
                    constraint.weights,
                    parent,
                );
            }
            (Pos::Record(lower_fields), Neg::Record(upper_fields)) => {
                self.enqueue_record_fields(lower_fields, upper_fields, constraint.weights, parent);
            }
            (Pos::RecordTailSpread { fields, tail }, Neg::Record(upper_fields)) => {
                self.enqueue_record_tail_spread(
                    fields,
                    tail,
                    upper_fields,
                    constraint.weights,
                    parent,
                );
            }
            (Pos::RecordHeadSpread { tail, fields }, Neg::Record(upper_fields)) => {
                self.enqueue_record_head_spread(
                    tail,
                    fields,
                    upper_fields,
                    constraint.weights,
                    parent,
                );
            }
            (Pos::PolyVariant(lower_items), Neg::PolyVariant(upper_items)) => {
                self.enqueue_variant_items(lower_items, upper_items, constraint.weights, parent);
            }
            (Pos::Tuple(lowers), Neg::Tuple(uppers)) if lowers.len() == uppers.len() => {
                for (index, (lower, upper)) in lowers.into_iter().zip(uppers).enumerate() {
                    self.enqueue_derived_subtype(
                        lower,
                        constraint.weights.clone(),
                        upper,
                        parent,
                        StructuralDerivationRule::TupleElement {
                            index: StructuralIndex::from_usize(index),
                        },
                    );
                }
            }
            (Pos::Row(items), Neg::Row(upper_items, upper_tail)) => {
                self.enqueue_row_items(items, upper_items, upper_tail, constraint.weights, parent);
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

    fn enqueue_derived_invariant_neu_args(
        &mut self,
        lower_args: Vec<NeuId>,
        upper_args: Vec<NeuId>,
        weights: ConstraintWeights,
        parent: ConstraintRecordId,
    ) {
        for (index, (lower, upper)) in lower_args.into_iter().zip(upper_args).enumerate() {
            let (lower_pos, lower_neg) = self.neu_bounds(lower);
            let (upper_pos, upper_neg) = self.neu_bounds(upper);
            let index = StructuralIndex::from_usize(index);
            self.enqueue_derived_subtype(
                lower_pos,
                weights.clone(),
                upper_neg,
                parent,
                StructuralDerivationRule::ConstructorArgument {
                    index,
                    direction: InvariantDirection::LowerToUpper,
                },
            );
            self.enqueue_derived_subtype(
                upper_pos,
                weights.swapped(),
                lower_neg,
                parent,
                StructuralDerivationRule::ConstructorArgument {
                    index,
                    direction: InvariantDirection::UpperToLower,
                },
            );
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
        parent: ConstraintRecordId,
    ) {
        for (index, upper) in upper_fields.into_iter().enumerate() {
            let Some(lower) = find_record_field(&lower_fields, &upper.name) else {
                continue;
            };
            if lower.optional && !upper.optional {
                continue;
            }
            self.enqueue_derived_subtype(
                lower.value,
                weights.clone(),
                upper.value,
                parent,
                StructuralDerivationRule::RecordField {
                    index: StructuralIndex::from_usize(index),
                },
            );
        }
    }

    pub(in crate::constraints) fn enqueue_record_tail_spread(
        &mut self,
        fields: Vec<RecordField<PosId>>,
        tail: PosId,
        upper_fields: Vec<RecordField<NegId>>,
        weights: ConstraintWeights,
        parent: ConstraintRecordId,
    ) {
        for (index, upper) in upper_fields.into_iter().enumerate() {
            let index = StructuralIndex::from_usize(index);
            if let Some(lower) = find_record_field(&fields, &upper.name) {
                if !lower.optional || upper.optional {
                    self.enqueue_derived_subtype(
                        lower.value,
                        weights.clone(),
                        upper.value,
                        parent,
                        StructuralDerivationRule::RecordSpreadField {
                            spread: RecordSpreadKind::Tail,
                            index,
                        },
                    );
                }
                let tail_upper = self.singleton_neg_record(optionalized_neg_field(upper));
                self.enqueue_derived_subtype(
                    tail,
                    weights.clone(),
                    tail_upper,
                    parent,
                    StructuralDerivationRule::RecordSpreadTail {
                        spread: RecordSpreadKind::Tail,
                        index,
                    },
                );
            } else {
                let tail_upper = self.singleton_neg_record(upper);
                self.enqueue_derived_subtype(
                    tail,
                    weights.clone(),
                    tail_upper,
                    parent,
                    StructuralDerivationRule::RecordSpreadTail {
                        spread: RecordSpreadKind::Tail,
                        index,
                    },
                );
            }
        }
    }

    pub(in crate::constraints) fn enqueue_record_head_spread(
        &mut self,
        tail: PosId,
        fields: Vec<RecordField<PosId>>,
        upper_fields: Vec<RecordField<NegId>>,
        weights: ConstraintWeights,
        parent: ConstraintRecordId,
    ) {
        for (index, upper) in upper_fields.into_iter().enumerate() {
            let index = StructuralIndex::from_usize(index);
            if let Some(lower) = find_record_field(&fields, &upper.name) {
                if !lower.optional || upper.optional {
                    self.enqueue_derived_subtype(
                        lower.value,
                        weights.clone(),
                        upper.value,
                        parent,
                        StructuralDerivationRule::RecordSpreadField {
                            spread: RecordSpreadKind::Head,
                            index,
                        },
                    );
                }
            } else {
                let tail_upper = self.singleton_neg_record(upper);
                self.enqueue_derived_subtype(
                    tail,
                    weights.clone(),
                    tail_upper,
                    parent,
                    StructuralDerivationRule::RecordSpreadTail {
                        spread: RecordSpreadKind::Head,
                        index,
                    },
                );
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
        parent: ConstraintRecordId,
    ) {
        for (variant_index, (name, lower_payloads)) in lower_items.into_iter().enumerate() {
            let Some((_, upper_payloads)) = upper_items
                .iter()
                .find(|(upper_name, _)| upper_name == &name)
            else {
                continue;
            };
            if lower_payloads.len() != upper_payloads.len() {
                continue;
            }
            for (payload_index, (lower, upper)) in lower_payloads
                .into_iter()
                .zip(upper_payloads.iter().copied())
                .enumerate()
            {
                self.enqueue_derived_subtype(
                    lower,
                    weights.clone(),
                    upper,
                    parent,
                    StructuralDerivationRule::VariantPayload {
                        variant_index: StructuralIndex::from_usize(variant_index),
                        payload_index: StructuralIndex::from_usize(payload_index),
                    },
                );
            }
        }
    }

    pub(in crate::constraints) fn enqueue_row_items(
        &mut self,
        items: Vec<PosId>,
        upper_items: Vec<NegId>,
        upper_tail: NegId,
        weights: ConstraintWeights,
        parent: ConstraintRecordId,
    ) {
        let mut remaining_upper_items = upper_items;
        let mut variable_items = Vec::new();
        let mut row_tail_items = Vec::new();
        let mut direct_tail_items = Vec::new();
        for (lower_index, item) in items.into_iter().enumerate() {
            if matches!(self.types.pos(item), Pos::Var(_)) {
                variable_items.push((lower_index, item));
                continue;
            }

            if let Some(upper_index) = remaining_upper_items
                .iter()
                .position(|upper| self.row_items_can_match(item, *upper))
            {
                let upper = remaining_upper_items.remove(upper_index);
                self.enqueue_derived_row_item_match(
                    item,
                    upper,
                    weights.clone(),
                    parent,
                    StructuralIndex::from_usize(lower_index),
                );
            } else if self.pos_is_effect_marker_row_item(item) {
                row_tail_items.push((lower_index, item));
            } else {
                direct_tail_items.push((lower_index, item));
                self.enqueue_derived_subtype(
                    item,
                    weights.clone(),
                    upper_tail,
                    parent,
                    StructuralDerivationRule::RowItem {
                        index: StructuralIndex::from_usize(lower_index),
                        route: RowItemRoute::DirectToUpperTail,
                    },
                );
            }
        }

        if let Some(lower_tail) =
            self.pos_row_from_pos_items(row_tail_items.iter().map(|(_, item)| *item).collect())
        {
            for (derivation_index, (index, _)) in row_tail_items.iter().enumerate() {
                let rule = StructuralDerivationRule::RowItem {
                    index: StructuralIndex::from_usize(*index),
                    route: RowItemRoute::MarkerAggregateToUpperTail,
                };
                if derivation_index == 0 {
                    self.enqueue_derived_subtype(
                        lower_tail,
                        weights.clone(),
                        upper_tail,
                        parent,
                        rule,
                    );
                } else {
                    self.merge_structural_derivation(
                        lower_tail,
                        weights.clone(),
                        upper_tail,
                        parent,
                        rule,
                    );
                }
            }
        }

        for (lower_index, item) in variable_items {
            if let Some(upper_index) = remaining_upper_items
                .iter()
                .position(|upper| self.row_items_can_match(item, *upper))
            {
                let upper = remaining_upper_items.remove(upper_index);
                self.enqueue_derived_row_item_match(
                    item,
                    upper,
                    weights.clone(),
                    parent,
                    StructuralIndex::from_usize(lower_index),
                );
                continue;
            }

            // A variable row item is handled by `α <: remaining row` itself. Treating it again as
            // a lower-tail item would add `upper_tail <: α` and create fresh residual cycles.
            let upper = if remaining_upper_items.is_empty() {
                upper_tail
            } else {
                self.alloc_neg(Neg::Row(remaining_upper_items.clone(), upper_tail))
            };
            self.enqueue_derived_subtype(
                item,
                weights.clone(),
                upper,
                parent,
                StructuralDerivationRule::RowItem {
                    index: StructuralIndex::from_usize(lower_index),
                    route: RowItemRoute::VariableToRemainingRow,
                },
            );
        }

        self.enqueue_derived_upper_tail_to_lower_row_tail(
            upper_tail,
            row_tail_items,
            weights.clone(),
            parent,
        );
        self.enqueue_derived_upper_tail_to_direct_tail(
            upper_tail,
            direct_tail_items,
            weights,
            parent,
        );
    }

    fn pos_row_from_pos_items(&mut self, items: Vec<PosId>) -> Option<PosId> {
        (!items.is_empty()).then(|| self.alloc_pos(Pos::Row(items)))
    }

    fn pos_is_effect_marker_row_item(&self, item: PosId) -> bool {
        match self.types.pos(item) {
            Pos::Con(path, args) => args.is_empty() && self.effect_family_paths.contains(path),
            Pos::Row(items) => items
                .iter()
                .all(|item| self.pos_is_effect_marker_row_item(*item)),
            Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => {
                self.pos_is_effect_marker_row_item(*inner)
            }
            Pos::Union(left, right) => {
                self.pos_is_effect_marker_row_item(*left)
                    && self.pos_is_effect_marker_row_item(*right)
            }
            Pos::Var(_)
            | Pos::Bot
            | Pos::Fun { .. }
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_) => false,
        }
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

    fn enqueue_derived_row_item_match(
        &mut self,
        lower: PosId,
        upper: NegId,
        weights: ConstraintWeights,
        parent: ConstraintRecordId,
        item_index: StructuralIndex,
    ) {
        match (self.types.pos(lower).clone(), self.types.neg(upper).clone()) {
            (Pos::Con(lower_path, lower_args), Neg::Con(upper_path, upper_args))
                if lower_path == upper_path =>
            {
                self.enqueue_derived_row_item_neu_args(
                    lower_args, upper_args, weights, parent, item_index,
                );
            }
            (Pos::Var(lower), Neg::Var(upper)) if lower == upper => {}
            _ => {
                self.enqueue_derived_subtype(
                    lower,
                    weights,
                    upper,
                    parent,
                    StructuralDerivationRule::RowItem {
                        index: item_index,
                        route: RowItemRoute::Matched,
                    },
                );
            }
        }
    }

    fn enqueue_derived_row_item_neu_args(
        &mut self,
        lower_args: Vec<NeuId>,
        upper_args: Vec<NeuId>,
        weights: ConstraintWeights,
        parent: ConstraintRecordId,
        item_index: StructuralIndex,
    ) {
        for (argument_index, (lower, upper)) in lower_args.into_iter().zip(upper_args).enumerate() {
            let (lower_pos, lower_neg) = self.neu_bounds(lower);
            let (upper_pos, upper_neg) = self.neu_bounds(upper);
            let argument_index = StructuralIndex::from_usize(argument_index);
            self.enqueue_derived_subtype(
                lower_pos,
                weights.clone(),
                upper_neg,
                parent,
                StructuralDerivationRule::RowItemArgument {
                    item_index,
                    argument_index,
                    direction: InvariantDirection::LowerToUpper,
                },
            );
            self.enqueue_derived_subtype(
                upper_pos,
                weights.swapped(),
                lower_neg,
                parent,
                StructuralDerivationRule::RowItemArgument {
                    item_index,
                    argument_index,
                    direction: InvariantDirection::UpperToLower,
                },
            );
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
        parent: ConstraintRecordId,
    ) {
        let Some(upper) = upper_items.into_iter().find(
            |upper| matches!(self.types.neg(*upper), Neg::Con(path, _) if path == &lower_path),
        ) else {
            let lower = self.alloc_pos(Pos::Con(lower_path, lower_args));
            self.enqueue_derived_subtype(
                lower,
                weights,
                upper_tail,
                parent,
                StructuralDerivationRule::RowItem {
                    index: StructuralIndex::from_usize(0),
                    route: RowItemRoute::DirectToUpperTail,
                },
            );
            return;
        };
        let Neg::Con(_, upper_args) = self.types.neg(upper).clone() else {
            return;
        };
        self.enqueue_derived_row_item_neu_args(
            lower_args,
            upper_args,
            weights,
            parent,
            StructuralIndex::from_usize(0),
        );
    }

    fn enqueue_derived_upper_tail_to_lower_row_tail(
        &mut self,
        upper_tail: NegId,
        lower_tail_items: Vec<(usize, PosId)>,
        weights: ConstraintWeights,
        parent: ConstraintRecordId,
    ) {
        let Neg::Var(tail_var) = self.types.neg(upper_tail).clone() else {
            return;
        };
        let Some(lower_tail) =
            self.neg_row_from_pos_items(lower_tail_items.iter().map(|(_, item)| *item).collect())
        else {
            return;
        };
        let tail = self.alloc_pos(Pos::Var(tail_var));
        for (derivation_index, (index, _)) in lower_tail_items.into_iter().enumerate() {
            let rule = StructuralDerivationRule::RowItem {
                index: StructuralIndex::from_usize(index),
                route: RowItemRoute::UpperTailToMarkerItems,
            };
            if derivation_index == 0 {
                self.enqueue_derived_subtype(tail, weights.clone(), lower_tail, parent, rule);
            } else {
                self.merge_structural_derivation(tail, weights.clone(), lower_tail, parent, rule);
            }
        }
    }

    fn enqueue_derived_upper_tail_to_direct_tail(
        &mut self,
        upper_tail: NegId,
        direct_tail_items: Vec<(usize, PosId)>,
        weights: ConstraintWeights,
        parent: ConstraintRecordId,
    ) {
        let Neg::Var(tail_var) = self.types.neg(upper_tail).clone() else {
            return;
        };
        let Some(lower_tail) = self.neg_direct_tail_from_pos_items(
            direct_tail_items.iter().map(|(_, item)| *item).collect(),
        ) else {
            return;
        };
        let tail = self.alloc_pos(Pos::Var(tail_var));
        for (derivation_index, (index, _)) in direct_tail_items.into_iter().enumerate() {
            let rule = StructuralDerivationRule::RowItem {
                index: StructuralIndex::from_usize(index),
                route: RowItemRoute::UpperTailToDirectItems,
            };
            if derivation_index == 0 {
                self.enqueue_derived_subtype(tail, weights.clone(), lower_tail, parent, rule);
            } else {
                self.merge_structural_derivation(tail, weights.clone(), lower_tail, parent, rule);
            }
        }
    }

    pub(in crate::constraints) fn neg_direct_tail_from_pos_items(
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

    pub(in crate::constraints) fn neg_row_from_pos_items(
        &mut self,
        items: Vec<PosId>,
    ) -> Option<NegId> {
        if items.is_empty() {
            return None;
        }
        let neg_items = items
            .into_iter()
            .map(|item| self.neg_row_item_from_pos(item))
            .collect::<Option<Vec<_>>>()?;
        let tail = self.alloc_neg(Neg::Bot);
        Some(self.alloc_neg(Neg::Row(neg_items, tail)))
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
