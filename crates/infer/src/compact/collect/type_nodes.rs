use super::*;

impl<'a> CompactCollector<'a> {
    pub(super) fn compact_pos_id(&mut self, id: PosId, weight: ConstraintWeight) -> CompactType {
        match self.machine.types().pos(id).clone() {
            Pos::Bot => CompactType::default(),
            Pos::Var(var) => self.compact_var_side(var, Polarity::Positive, weight),
            Pos::Con(path, args) => self.compact_con(path, args, weight),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactType::from_fun(CompactFun {
                arg: self.compact_neg_id(arg, ConstraintWeight::empty()),
                arg_eff: self.compact_neg_effect_id(arg_eff, ConstraintWeight::empty()),
                ret_eff: self.compact_pos_effect_id(ret_eff, weight.clone()),
                ret: self.compact_pos_id(ret, weight),
            }),
            Pos::Record(fields) => CompactType::from_record(CompactRecord {
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.compact_pos_id(field.value, weight.clone()),
                        optional: field.optional,
                    })
                    .collect(),
            }),
            Pos::RecordTailSpread { fields, tail } => {
                CompactType::from_record_spread(CompactRecordSpread {
                    fields: fields
                        .into_iter()
                        .map(|field| RecordField {
                            name: field.name,
                            value: self.compact_pos_id(field.value, weight.clone()),
                            optional: field.optional,
                        })
                        .collect(),
                    tail: Box::new(self.compact_pos_id(tail, weight)),
                    tail_wins: true,
                })
            }
            Pos::RecordHeadSpread { tail, fields } => {
                CompactType::from_record_spread(CompactRecordSpread {
                    fields: fields
                        .into_iter()
                        .map(|field| RecordField {
                            name: field.name,
                            value: self.compact_pos_id(field.value, weight.clone()),
                            optional: field.optional,
                        })
                        .collect(),
                    tail: Box::new(self.compact_pos_id(tail, weight)),
                    tail_wins: false,
                })
            }
            Pos::PolyVariant(items) => CompactType::from_poly_variant(CompactPolyVariant {
                items: items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.compact_pos_id(payload, weight.clone()))
                                .collect(),
                        )
                    })
                    .collect(),
            }),
            Pos::Tuple(items) => CompactType::from_tuple(CompactTuple {
                items: items
                    .into_iter()
                    .map(|item| self.compact_pos_id(item, weight.clone()))
                    .collect(),
            }),
            Pos::Row(items) => self.compact_pos_row(items, weight),
            Pos::NonSubtract(pos, subtract) => {
                let weight = weight.union(&ConstraintWeight::from_ids([subtract]));
                self.compact_pos_id(pos, weight)
            }
            Pos::Stack {
                inner,
                weight: stack_weight,
            } => {
                let families = self.compact_weight_stack_families(&stack_weight);
                let compact = self.compact_pos_id(inner, stack_weight.union(&weight));
                self.record_stack_families_row_coexistence(&families, &compact);
                compact
            }
            Pos::Union(lhs, rhs) => {
                let lhs = self.compact_pos_id(lhs, weight.clone());
                let rhs = self.compact_pos_id(rhs, weight);
                self.merge_types(true, lhs, rhs)
            }
        }
    }

    pub(super) fn compact_neg_id(&mut self, id: NegId, weight: ConstraintWeight) -> CompactType {
        match self.machine.types().neg(id).clone() {
            Neg::Top => CompactType::default(),
            Neg::Bot => CompactType::never(),
            Neg::Var(var) => {
                self.compact_var_side(var, Polarity::Negative, ConstraintWeight::empty())
            }
            Neg::Con(path, args) => self.compact_con(path, args, ConstraintWeight::empty()),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactType::from_fun(CompactFun {
                arg: self.compact_pos_id(arg, weight.clone()),
                arg_eff: self.compact_pos_effect_id(arg_eff, weight.clone()),
                ret_eff: self.compact_neg_effect_id(ret_eff, ConstraintWeight::empty()),
                ret: self.compact_neg_id(ret, ConstraintWeight::empty()),
            }),
            Neg::Record(fields) => CompactType::from_record(CompactRecord {
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.compact_neg_id(field.value, ConstraintWeight::empty()),
                        optional: field.optional,
                    })
                    .collect(),
            }),
            Neg::PolyVariant(items) => CompactType::from_poly_variant(CompactPolyVariant {
                items: items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| {
                                    self.compact_neg_id(payload, ConstraintWeight::empty())
                                })
                                .collect(),
                        )
                    })
                    .collect(),
            }),
            Neg::Tuple(items) => CompactType::from_tuple(CompactTuple {
                items: items
                    .into_iter()
                    .map(|item| self.compact_neg_id(item, ConstraintWeight::empty()))
                    .collect(),
            }),
            Neg::Row(items, tail) => self.compact_neg_row(items, tail, weight),
            Neg::Stack {
                inner,
                weight: stack_weight,
            } => {
                let families = self.compact_weight_stack_families(&stack_weight);
                let compact = self.compact_neg_id(inner, stack_weight.union(&weight));
                self.record_stack_families_row_coexistence(&families, &compact);
                compact
            }
            Neg::Intersection(lhs, rhs) => {
                let lhs = self.compact_neg_id(lhs, weight.clone());
                let rhs = self.compact_neg_id(rhs, weight);
                self.merge_types(false, lhs, rhs)
            }
        }
    }

    pub(super) fn compact_con(
        &mut self,
        path: Vec<String>,
        args: Vec<NeuId>,
        weight: ConstraintWeight,
    ) -> CompactType {
        if args.is_empty()
            && path.len() == 1
            && let Some(builtin) = BuiltinType::from_surface_name(&path[0])
        {
            return CompactType::from_builtin(builtin);
        }
        CompactType::from_con(CompactCon {
            path,
            args: args
                .into_iter()
                .map(|arg| self.compact_neu_id(arg, weight.clone()))
                .collect(),
        })
    }

    pub(super) fn compact_pos_effect_id(
        &mut self,
        id: PosId,
        weight: ConstraintWeight,
    ) -> CompactType {
        match self.machine.types().pos(id).clone() {
            Pos::Bot => CompactType::default(),
            Pos::Var(var) => self.compact_var_side(var, Polarity::Positive, weight),
            Pos::Con(_, _) | Pos::NonSubtract(_, _) | Pos::Stack { .. } | Pos::Union(_, _) => {
                match self.machine.types().pos(id).clone() {
                    Pos::Union(lhs, rhs) => {
                        let lhs = self.compact_pos_effect_id(lhs, weight.clone());
                        let rhs = self.compact_pos_effect_id(rhs, weight);
                        self.merge_types(true, lhs, rhs)
                    }
                    _ => {
                        if let Some((path, args)) = self.compact_pos_row_item(id, weight.clone()) {
                            CompactType::from_row(CompactRow {
                                items: singleton_row_item_map(path, args),
                                tail: Box::new(CompactType::default()),
                            })
                        } else {
                            self.compact_pos_id(id, weight)
                        }
                    }
                }
            }
            Pos::Row(items) => self.compact_pos_row(items, weight),
            _ => self.compact_pos_id(id, weight),
        }
    }

    pub(super) fn compact_neg_effect_id(
        &mut self,
        id: NegId,
        weight: ConstraintWeight,
    ) -> CompactType {
        match self.machine.types().neg(id).clone() {
            Neg::Top => CompactType::default(),
            Neg::Bot => CompactType::never(),
            Neg::Var(var) => {
                self.compact_var_side(var, Polarity::Negative, ConstraintWeight::empty())
            }
            Neg::Con(_, _) | Neg::Stack { .. } => {
                if let Some((path, args)) = self.compact_neg_row_item(id) {
                    CompactType::from_row(CompactRow {
                        items: singleton_row_item_map(path, args),
                        tail: Box::new(CompactType::default()),
                    })
                } else {
                    self.compact_neg_id(id, weight)
                }
            }
            Neg::Row(items, tail) => self.compact_neg_row(items, tail, weight),
            Neg::Intersection(lhs, rhs) => {
                let lhs = self.compact_neg_effect_id(lhs, weight.clone());
                let rhs = self.compact_neg_effect_id(rhs, weight);
                self.merge_types(false, lhs, rhs)
            }
            _ => self.compact_neg_id(id, weight),
        }
    }

    pub(super) fn compact_pos_row_item(
        &mut self,
        id: PosId,
        weight: ConstraintWeight,
    ) -> Option<(Vec<String>, Vec<CompactBounds>)> {
        match self.machine.types().pos(id).clone() {
            Pos::Con(path, args) => Some((
                path,
                args.into_iter()
                    .map(|arg| self.compact_neu_id(arg, weight.clone()))
                    .collect(),
            )),
            Pos::NonSubtract(pos, subtract) => {
                let weight = weight.union(&ConstraintWeight::from_ids([subtract]));
                self.compact_pos_row_item(pos, weight)
            }
            Pos::Stack {
                inner,
                weight: stack_weight,
            } => {
                let families = self.compact_weight_stack_families(&stack_weight);
                let item = self.compact_pos_row_item(inner, stack_weight.union(&weight));
                if let Some((path, args)) = &item {
                    self.record_stack_families_row_item_coexistence(&families, path, args);
                }
                item
            }
            _ => None,
        }
    }

    pub(super) fn compact_neg_row_item(
        &mut self,
        id: NegId,
    ) -> Option<(Vec<String>, Vec<CompactBounds>)> {
        match self.machine.types().neg(id).clone() {
            Neg::Con(path, args) => Some((
                path,
                args.into_iter()
                    .map(|arg| self.compact_neu_id(arg, ConstraintWeight::empty()))
                    .collect(),
            )),
            Neg::Stack {
                inner,
                weight: stack_weight,
            } => {
                let families = self.compact_weight_stack_families(&stack_weight);
                let item = self.compact_neg_row_item(inner);
                if let Some((path, args)) = &item {
                    self.record_stack_families_row_item_coexistence(&families, path, args);
                }
                item
            }
            _ => None,
        }
    }

    pub(super) fn compact_neu_id(&mut self, id: NeuId, weight: ConstraintWeight) -> CompactBounds {
        match self.machine.types().neu(id).clone() {
            Neu::Bounds(lower, upper) => CompactBounds::Interval {
                lower: self.compact_pos_id(lower, weight),
                upper: self.compact_neg_id(upper, ConstraintWeight::empty()),
            },
            Neu::Con(path, args) => CompactBounds::Con {
                path,
                args: args
                    .into_iter()
                    .map(|arg| self.compact_neu_id(arg, weight.clone()))
                    .collect(),
            },
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactBounds::Fun {
                arg: Box::new(self.compact_neu_id(arg, ConstraintWeight::empty())),
                arg_eff: Box::new(self.compact_effect_neu_id(arg_eff, ConstraintWeight::empty())),
                ret_eff: Box::new(self.compact_effect_neu_id(ret_eff, weight.clone())),
                ret: Box::new(self.compact_neu_id(ret, weight)),
            },
            Neu::Record(fields) => CompactBounds::Record {
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.compact_neu_id(field.value, weight.clone()),
                        optional: field.optional,
                    })
                    .collect(),
            },
            Neu::PolyVariant(items) => CompactBounds::PolyVariant {
                items: items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.compact_neu_id(payload, weight.clone()))
                                .collect(),
                        )
                    })
                    .collect(),
            },
            Neu::Tuple(items) => CompactBounds::Tuple {
                items: items
                    .into_iter()
                    .map(|item| self.compact_neu_id(item, weight.clone()))
                    .collect(),
            },
        }
    }

    pub(super) fn compact_effect_neu_id(
        &mut self,
        id: NeuId,
        weight: ConstraintWeight,
    ) -> CompactBounds {
        match self.machine.types().neu(id).clone() {
            Neu::Bounds(lower, upper) => CompactBounds::Interval {
                lower: self.compact_pos_effect_id(lower, weight),
                upper: self.compact_neg_effect_id(upper, ConstraintWeight::empty()),
            },
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactBounds::Fun {
                arg: Box::new(self.compact_neu_id(arg, ConstraintWeight::empty())),
                arg_eff: Box::new(self.compact_effect_neu_id(arg_eff, ConstraintWeight::empty())),
                ret_eff: Box::new(self.compact_effect_neu_id(ret_eff, weight.clone())),
                ret: Box::new(self.compact_neu_id(ret, weight)),
            },
            _ => self.compact_neu_id(id, weight),
        }
    }

    pub(super) fn compact_pos_row(
        &mut self,
        items: Vec<PosId>,
        weight: ConstraintWeight,
    ) -> CompactType {
        let mut vars_and_nested = CompactType::default();
        let mut concrete_items = CompactRowItemMap::default();
        for item in items {
            match self.machine.types().pos(item).clone() {
                Pos::Var(var) => {
                    let compact = self.compact_var_side(var, Polarity::Positive, weight.clone());
                    vars_and_nested = self.merge_types(true, vars_and_nested, compact);
                }
                Pos::Row(nested) => {
                    let compact = self.compact_pos_row(nested, weight.clone());
                    vars_and_nested = self.merge_types(true, vars_and_nested, compact);
                }
                _ => {
                    if let Some((path, args)) = self.compact_pos_row_item(item, weight.clone()) {
                        concrete_items = self.merge_row_items(
                            true,
                            concrete_items,
                            singleton_row_item_map(path, args),
                        );
                    } else {
                        let compact = self.compact_pos_id(item, weight.clone());
                        vars_and_nested = self.merge_types(true, vars_and_nested, compact);
                    }
                }
            }
        }
        if concrete_items.is_empty() {
            vars_and_nested
        } else {
            self.merge_types(
                true,
                vars_and_nested,
                CompactType::from_row(CompactRow {
                    items: concrete_items,
                    tail: Box::new(CompactType::default()),
                }),
            )
        }
    }

    pub(super) fn compact_neg_row(
        &mut self,
        items: Vec<NegId>,
        tail: NegId,
        weight: ConstraintWeight,
    ) -> CompactType {
        let mut concrete_items = CompactRowItemMap::default();
        let mut item_tail = CompactType::default();
        for item in items {
            if let Some((path, args)) = self.compact_neg_row_item(item) {
                concrete_items =
                    self.merge_row_items(true, concrete_items, singleton_row_item_map(path, args));
            } else {
                let compact = self.compact_neg_id(item, ConstraintWeight::empty());
                item_tail = self.merge_types(false, item_tail, compact);
            }
        }
        let compact_tail = self.compact_neg_row_tail_id(tail, weight);
        let tail = self.merge_types(false, item_tail, compact_tail);
        CompactType::from_row(CompactRow {
            items: concrete_items,
            tail: Box::new(tail),
        })
    }

    pub(super) fn compact_neg_row_tail_id(
        &mut self,
        id: NegId,
        weight: ConstraintWeight,
    ) -> CompactType {
        match self.machine.types().neg(id).clone() {
            Neg::Top => CompactType::default(),
            Neg::Bot => CompactType::never(),
            Neg::Var(var) => self.compact_neg_row_tail_var(var, weight),
            Neg::Row(items, tail) => self.compact_neg_row(items, tail, weight),
            Neg::Stack {
                inner,
                weight: stack_weight,
            } => self.compact_neg_row_tail_id(inner, stack_weight.union(&weight)),
            Neg::Intersection(lhs, rhs) => {
                let lhs = self.compact_neg_row_tail_id(lhs, weight.clone());
                let rhs = self.compact_neg_row_tail_id(rhs, weight);
                self.merge_types(false, lhs, rhs)
            }
            Neg::Con(_, _)
            | Neg::Fun { .. }
            | Neg::Record(_)
            | Neg::PolyVariant(_)
            | Neg::Tuple(_) => CompactType::default(),
        }
    }

    pub(super) fn compact_neg_row_tail_var(
        &mut self,
        var: TypeVar,
        weight: ConstraintWeight,
    ) -> CompactType {
        let mut out = CompactType::from_var(self.compact_var_occurrence(
            var,
            Polarity::Negative,
            ConstraintWeight::empty(),
        ));
        if !self.row_tail_in_progress.insert(var) {
            return out;
        }
        let Some(bounds) = self.machine.bounds().of(var).cloned() else {
            self.row_tail_in_progress.remove(&var);
            return out;
        };
        for bound in bounds.uppers() {
            let bound_weight = weight.union(&bound.weights.right);
            let compact = match self.machine.types().neg(bound.neg).clone() {
                Neg::Row(items, tail) => self.compact_neg_row_upper_bound(
                    var,
                    items,
                    tail,
                    bound_weight,
                    &bound.weights.left,
                ),
                Neg::Var(other) if Self::is_unweighted_neg_var_alias(&bound.weights, &weight) => {
                    CompactType::from_var(self.compact_secondary_var_occurrence(
                        other,
                        Polarity::Negative,
                        ConstraintWeight::empty(),
                    ))
                }
                Neg::Var(_) => CompactType::default(),
                Neg::Stack {
                    inner,
                    weight: stack_weight,
                } => self.compact_neg_row_tail_id(inner, stack_weight.union(&bound_weight)),
                Neg::Intersection(lhs, rhs) => {
                    let lhs = self.compact_neg_row_tail_id(lhs, bound_weight.clone());
                    let rhs = self.compact_neg_row_tail_id(rhs, bound_weight);
                    self.merge_types(false, lhs, rhs)
                }
                Neg::Top => CompactType::default(),
                Neg::Bot => CompactType::never(),
                Neg::Con(_, _)
                | Neg::Fun { .. }
                | Neg::Record(_)
                | Neg::PolyVariant(_)
                | Neg::Tuple(_) => CompactType::default(),
            };
            out = self.merge_types(false, out, compact);
        }
        self.row_tail_in_progress.remove(&var);
        out
    }

    pub(super) fn record_recursive_side(
        &mut self,
        var: TypeVar,
        polarity: Polarity,
        side: CompactType,
    ) {
        let entry = self
            .rec_vars
            .entry(var)
            .or_insert_with(|| CompactBounds::Interval {
                lower: CompactType::default(),
                upper: CompactType::default(),
            });
        let CompactBounds::Interval { lower, upper, .. } = entry else {
            return;
        };
        match polarity {
            Polarity::Positive => *lower = side,
            Polarity::Negative => *upper = side,
        }
    }
}
