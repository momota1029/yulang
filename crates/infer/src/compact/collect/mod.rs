use super::merge::*;
use super::*;

mod type_nodes;

pub(super) struct CompactCollector<'a> {
    machine: &'a ConstraintMachine,
    record_merge_constraints: bool,
    merge_constraints: Vec<CompactMergeConstraint>,
    in_progress: FxHashSet<(TypeVar, Polarity)>,
    row_tail_in_progress: FxHashSet<TypeVar>,
    recursive: FxHashSet<(TypeVar, Polarity)>,
    rec_vars: FxHashMap<TypeVar, CompactBounds>,
    cache: FxHashMap<CompactVarSideKey, CompactType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct CompactVarSideKey {
    var: TypeVar,
    polarity: Polarity,
    weight: ConstraintWeight,
}

impl<'a> CompactCollector<'a> {
    pub(super) fn new(machine: &'a ConstraintMachine) -> Self {
        Self {
            machine,
            record_merge_constraints: false,
            merge_constraints: Vec::new(),
            in_progress: FxHashSet::default(),
            row_tail_in_progress: FxHashSet::default(),
            recursive: FxHashSet::default(),
            rec_vars: FxHashMap::default(),
            cache: FxHashMap::default(),
        }
    }

    pub(super) fn new_recording(machine: &'a ConstraintMachine) -> Self {
        Self {
            record_merge_constraints: true,
            ..Self::new(machine)
        }
    }

    pub(super) fn compact_root(self, root: TypeVar) -> CompactRoot {
        self.compact_root_with_merge_constraints(root).0
    }

    pub(super) fn compact_root_with_merge_constraints(
        mut self,
        root: TypeVar,
    ) -> (CompactRoot, Vec<CompactMergeConstraint>) {
        let root_ty = self.compact_var_side(root, Polarity::Positive, ConstraintWeight::empty());
        let mut rec_vars = self
            .rec_vars
            .into_iter()
            .map(|(var, bounds)| CompactRecursiveVar { var, bounds })
            .collect::<Vec<_>>();
        rec_vars.sort_by_key(|rec| rec.var.0);
        (
            CompactRoot {
                root: root_ty,
                rec_vars,
            },
            self.merge_constraints,
        )
    }

    pub(super) fn merge_types(
        &mut self,
        positive: bool,
        lhs: CompactType,
        rhs: CompactType,
    ) -> CompactType {
        if !self.record_merge_constraints {
            return merge_compact_types(positive, lhs, rhs);
        }
        let out = merge_compact_types_with_sink(positive, lhs, rhs, &mut self.merge_constraints);
        self.record_stack_row_coexistence(&out);
        out
    }

    pub(super) fn merge_row_items(
        &mut self,
        positive: bool,
        lhs: CompactRowItemMap,
        rhs: CompactRowItemMap,
    ) -> CompactRowItemMap {
        if !self.record_merge_constraints {
            return merge_row_items(positive, lhs, rhs);
        }
        merge_row_items_with_sink(positive, lhs, rhs, &mut self.merge_constraints)
    }

    pub(super) fn record_stack_row_coexistence(&mut self, ty: &CompactType) {
        if ty.vars.is_empty() || ty.rows.is_empty() {
            return;
        }

        let mut families = Vec::new();
        for var in &ty.vars {
            if var.weight.is_empty() {
                continue;
            }
            families.extend(self.compact_weight_stack_families(&var.weight));
        }
        self.record_stack_families_row_coexistence(&families, ty);
    }

    pub(super) fn compact_weight_stack_families(
        &mut self,
        weight: &ConstraintWeight,
    ) -> Vec<CompactStackFamily> {
        compact_weight_effect_families(weight)
            .into_iter()
            .map(|(path, args)| CompactStackFamily {
                path,
                args: args
                    .into_iter()
                    .map(|arg| self.compact_neu_id(arg, ConstraintWeight::empty()))
                    .collect(),
            })
            .collect()
    }

    pub(super) fn record_stack_families_row_coexistence(
        &mut self,
        families: &[CompactStackFamily],
        ty: &CompactType,
    ) {
        if families.is_empty() || ty.rows.is_empty() {
            return;
        }

        let mut row_items = Vec::new();
        for row in &ty.rows {
            for (path, args) in &row.items {
                row_items.push((path, args));
            }
        }
        for (row_path, row_args) in row_items {
            for family in families
                .iter()
                .filter(|family| &family.path == row_path && family.args.len() == row_args.len())
            {
                self.record_merge_bound_args(&family.args, row_args);
            }
        }
    }

    pub(super) fn record_stack_families_row_item_coexistence(
        &mut self,
        families: &[CompactStackFamily],
        path: &[String],
        args: &[CompactBounds],
    ) {
        for family in families
            .iter()
            .filter(|family| family.path == path && family.args.len() == args.len())
        {
            self.record_merge_bound_args(&family.args, args);
        }
    }

    pub(super) fn compact_pos_stack_families(&mut self, id: PosId) -> Vec<CompactStackFamily> {
        match self.machine.types().pos(id).clone() {
            Pos::Bot | Pos::Var(_) => Vec::new(),
            Pos::Con(_, args) => self.compact_neu_stack_families(args),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let mut out = self.compact_neg_stack_families(arg);
                out.extend(self.compact_neg_stack_families(arg_eff));
                out.extend(self.compact_pos_stack_families(ret_eff));
                out.extend(self.compact_pos_stack_families(ret));
                out
            }
            Pos::Record(fields) => fields
                .into_iter()
                .flat_map(|field| self.compact_pos_stack_families(field.value))
                .collect(),
            Pos::RecordTailSpread { fields, tail } => {
                let mut out = fields
                    .into_iter()
                    .flat_map(|field| self.compact_pos_stack_families(field.value))
                    .collect::<Vec<_>>();
                out.extend(self.compact_pos_stack_families(tail));
                out
            }
            Pos::RecordHeadSpread { tail, fields } => {
                let mut out = self.compact_pos_stack_families(tail);
                out.extend(
                    fields
                        .into_iter()
                        .flat_map(|field| self.compact_pos_stack_families(field.value)),
                );
                out
            }
            Pos::PolyVariant(items) => items
                .into_iter()
                .flat_map(|(_, payloads)| payloads)
                .flat_map(|payload| self.compact_pos_stack_families(payload))
                .collect(),
            Pos::Tuple(items) | Pos::Row(items) => items
                .into_iter()
                .flat_map(|item| self.compact_pos_stack_families(item))
                .collect(),
            Pos::NonSubtract(inner, _) => self.compact_pos_stack_families(inner),
            Pos::Stack {
                inner,
                weight: stack_weight,
            } => {
                let mut out = self.compact_weight_stack_families(&stack_weight);
                out.extend(self.compact_pos_stack_families(inner));
                out
            }
            Pos::Union(lhs, rhs) => {
                let mut out = self.compact_pos_stack_families(lhs);
                out.extend(self.compact_pos_stack_families(rhs));
                out
            }
        }
    }

    pub(super) fn compact_neg_stack_families(&mut self, id: NegId) -> Vec<CompactStackFamily> {
        match self.machine.types().neg(id).clone() {
            Neg::Top | Neg::Bot | Neg::Var(_) => Vec::new(),
            Neg::Con(_, args) => self.compact_neu_stack_families(args),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let mut out = self.compact_pos_stack_families(arg);
                out.extend(self.compact_pos_stack_families(arg_eff));
                out.extend(self.compact_neg_stack_families(ret_eff));
                out.extend(self.compact_neg_stack_families(ret));
                out
            }
            Neg::Record(fields) => fields
                .into_iter()
                .flat_map(|field| self.compact_neg_stack_families(field.value))
                .collect(),
            Neg::PolyVariant(items) => items
                .into_iter()
                .flat_map(|(_, payloads)| payloads)
                .flat_map(|payload| self.compact_neg_stack_families(payload))
                .collect(),
            Neg::Tuple(items) => items
                .into_iter()
                .flat_map(|item| self.compact_neg_stack_families(item))
                .collect(),
            Neg::Row(items, tail) => {
                let mut out = items
                    .into_iter()
                    .flat_map(|item| self.compact_neg_stack_families(item))
                    .collect::<Vec<_>>();
                out.extend(self.compact_neg_stack_families(tail));
                out
            }
            Neg::Stack {
                inner,
                weight: stack_weight,
            } => {
                let mut out = self.compact_weight_stack_families(&stack_weight);
                out.extend(self.compact_neg_stack_families(inner));
                out
            }
            Neg::Intersection(lhs, rhs) => {
                let mut out = self.compact_neg_stack_families(lhs);
                out.extend(self.compact_neg_stack_families(rhs));
                out
            }
        }
    }

    pub(super) fn compact_neu_stack_families(
        &mut self,
        ids: Vec<NeuId>,
    ) -> Vec<CompactStackFamily> {
        ids.into_iter()
            .flat_map(|id| self.compact_neu_id_stack_families(id))
            .collect()
    }

    pub(super) fn compact_neu_id_stack_families(&mut self, id: NeuId) -> Vec<CompactStackFamily> {
        match self.machine.types().neu(id).clone() {
            Neu::Bounds(lower, upper) => {
                let mut out = self.compact_pos_stack_families(lower);
                out.extend(self.compact_neg_stack_families(upper));
                out
            }
            Neu::Con(_, args) | Neu::Tuple(args) => self.compact_neu_stack_families(args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let mut out = self.compact_neu_id_stack_families(arg);
                out.extend(self.compact_neu_id_stack_families(arg_eff));
                out.extend(self.compact_neu_id_stack_families(ret_eff));
                out.extend(self.compact_neu_id_stack_families(ret));
                out
            }
            Neu::Record(fields) => fields
                .into_iter()
                .flat_map(|field| self.compact_neu_id_stack_families(field.value))
                .collect(),
            Neu::PolyVariant(items) => items
                .into_iter()
                .flat_map(|(_, payloads)| payloads)
                .flat_map(|payload| self.compact_neu_id_stack_families(payload))
                .collect(),
        }
    }

    pub(super) fn record_merge_bound_args(&mut self, lhs: &[CompactBounds], rhs: &[CompactBounds]) {
        if lhs.len() != rhs.len() {
            return;
        }
        record_merge_bound_args_with_sink(&mut self.merge_constraints, lhs, rhs);
    }

    pub(super) fn compact_reachable_role_constraints(
        self,
        seed: &CompactRoot,
        constraints: &[RoleConstraint],
    ) -> Vec<CompactRoleConstraint> {
        self.compact_reachable_role_constraints_with_merge_constraints(seed, constraints)
            .0
    }

    pub(super) fn compact_reachable_role_constraints_with_merge_constraints(
        mut self,
        seed: &CompactRoot,
        constraints: &[RoleConstraint],
    ) -> (Vec<CompactRoleConstraint>, Vec<CompactMergeConstraint>) {
        let mut reachable = free_vars_in_root(seed);
        let mut selected = vec![false; constraints.len()];
        let mut out = Vec::new();

        loop {
            let mut changed = false;
            for (index, constraint) in constraints.iter().enumerate() {
                if selected[index] {
                    continue;
                }
                let raw_vars = constraint.raw_vars(self.machine.types());
                if !raw_vars.is_empty() && raw_vars.is_disjoint(&reachable) {
                    continue;
                }

                selected[index] = true;
                let compact = self.compact_role_constraint(constraint);
                for var in free_vars_in_role_constraint(&compact) {
                    reachable.insert(var);
                }
                out.push(compact);
                changed = true;
            }
            if !changed {
                return (out, self.merge_constraints);
            }
        }
    }

    pub(super) fn compact_role_constraint(
        &mut self,
        constraint: &RoleConstraint,
    ) -> CompactRoleConstraint {
        CompactRoleConstraint {
            role: constraint.role.clone(),
            inputs: constraint
                .inputs
                .iter()
                .map(|arg| self.compact_role_arg(arg))
                .collect(),
            associated: constraint
                .associated
                .iter()
                .map(|associated| self.compact_role_associated(associated))
                .collect(),
        }
    }

    pub(super) fn compact_role_constraint_with_merge_constraints(
        mut self,
        constraint: &RoleConstraint,
    ) -> (CompactRoleConstraint, Vec<CompactMergeConstraint>) {
        let constraint = self.compact_role_constraint(constraint);
        (constraint, self.merge_constraints)
    }

    pub(super) fn compact_role_associated(
        &mut self,
        associated: &RoleAssociatedConstraint,
    ) -> CompactRoleAssociatedType {
        CompactRoleAssociatedType {
            name: associated.name.clone(),
            value: self.compact_role_arg(&associated.value),
        }
    }

    pub(super) fn compact_role_arg(&mut self, arg: &RoleConstraintArg) -> CompactRoleArg {
        let lower = self.compact_pos_id(arg.lower, ConstraintWeight::empty());
        let upper = self.compact_neg_id(arg.upper, ConstraintWeight::empty());
        let bounds = if self.record_merge_constraints {
            role_arg_bounds_from_types_with_sink(lower, upper, &mut self.merge_constraints)
        } else {
            role_arg_bounds_from_types_with_sink(lower, upper, &mut NoopCompactMergeConstraintSink)
        };
        CompactRoleArg::invariant(bounds)
    }

    pub(super) fn compact_var_side(
        &mut self,
        var: TypeVar,
        polarity: Polarity,
        weight: ConstraintWeight,
    ) -> CompactType {
        let cache_key = CompactVarSideKey {
            var,
            polarity,
            weight: weight.clone(),
        };
        if let Some(cached) = self.cache.get(&cache_key) {
            return cached.clone();
        }

        let key = (var, polarity);
        if self.in_progress.contains(&key) {
            self.recursive.insert(key);
            return CompactType::from_var(self.compact_var_occurrence(var, polarity, weight));
        }

        self.in_progress.insert(key);
        let bounds = self.compact_var_bounds(var, polarity, &weight);
        let with_self = self.merge_types(
            polarity.is_positive(),
            CompactType::from_var(self.compact_var_occurrence(var, polarity, weight)),
            bounds,
        );
        self.in_progress.remove(&key);

        if self.recursive.remove(&key) {
            self.record_recursive_side(var, polarity, with_self.clone());
            let ty = CompactType::from_var(self.compact_var_occurrence(
                var,
                polarity,
                ConstraintWeight::empty(),
            ));
            self.cache.insert(cache_key, ty.clone());
            return ty;
        }

        self.cache.insert(cache_key, with_self.clone());
        with_self
    }

    pub(super) fn compact_var_occurrence(
        &self,
        var: TypeVar,
        polarity: Polarity,
        weight: ConstraintWeight,
    ) -> CompactVar {
        if polarity.is_positive() {
            CompactVar::covariant(var, weight)
        } else {
            CompactVar::contravariant(var)
        }
    }

    pub(super) fn compact_secondary_var_occurrence(
        &self,
        var: TypeVar,
        polarity: Polarity,
        weight: ConstraintWeight,
    ) -> CompactVar {
        self.compact_var_occurrence(var, polarity, weight)
            .with_origin(CompactVarOrigin::Secondary)
    }

    pub(super) fn compact_var_bounds(
        &mut self,
        var: TypeVar,
        polarity: Polarity,
        weight: &ConstraintWeight,
    ) -> CompactType {
        let Some(bounds) = self.machine.bounds().of(var).cloned() else {
            return CompactType::default();
        };
        match polarity {
            Polarity::Positive => self.compact_lower_bounds(var, &bounds, weight),
            Polarity::Negative => self.compact_upper_bounds(var, &bounds, weight),
        }
    }

    pub(super) fn compact_lower_bounds(
        &mut self,
        var: TypeVar,
        bounds: &VarBounds,
        outer_weight: &ConstraintWeight,
    ) -> CompactType {
        let mut acc = CompactType::default();
        let mut pending_stack_families = self.compact_pre_pop_stack_families(var);
        for bound in bounds.lowers() {
            let mut bound_stack_families = self.compact_weight_stack_families(&bound.weights.left);
            bound_stack_families.extend(self.compact_pos_stack_families(bound.pos));
            let compact =
                self.compact_pos_bound_id(bound.pos, bound.weights.left.union(outer_weight));
            self.record_stack_families_row_coexistence(&pending_stack_families, &compact);
            self.record_stack_families_row_coexistence(&bound_stack_families, &acc);
            self.record_stack_families_row_coexistence(&bound_stack_families, &compact);
            acc = self.merge_types(true, acc, compact);
            pending_stack_families.extend(bound_stack_families);
        }
        acc
    }

    pub(super) fn compact_pre_pop_stack_families(
        &mut self,
        var: TypeVar,
    ) -> Vec<CompactStackFamily> {
        self.machine
            .pre_pop_effect_families(var)
            .iter()
            .cloned()
            .map(|family| CompactStackFamily {
                path: family.path,
                args: family
                    .args
                    .into_iter()
                    .map(|arg| self.compact_neu_id(arg, ConstraintWeight::empty()))
                    .collect(),
            })
            .collect()
    }

    pub(super) fn compact_upper_bounds(
        &mut self,
        var: TypeVar,
        bounds: &VarBounds,
        outer_weight: &ConstraintWeight,
    ) -> CompactType {
        let mut acc = CompactType::default();
        for bound in bounds.uppers() {
            let compact = self.compact_upper_bound(var, bound, outer_weight);
            acc = self.merge_types(false, acc, compact);
        }
        acc
    }

    pub(super) fn compact_upper_bound(
        &mut self,
        source: TypeVar,
        bound: &crate::constraints::WeightedUpperBound,
        outer_weight: &ConstraintWeight,
    ) -> CompactType {
        let weight = outer_weight.union(&bound.weights.right);
        match self.machine.types().neg(bound.neg).clone() {
            Neg::Row(items, tail) => {
                self.compact_neg_row_upper_bound(source, items, tail, weight, &bound.weights.left)
            }
            Neg::Var(var) if Self::is_unweighted_neg_var_alias(&bound.weights, outer_weight) => {
                CompactType::from_var(self.compact_secondary_var_occurrence(
                    var,
                    Polarity::Negative,
                    ConstraintWeight::empty(),
                ))
            }
            Neg::Var(_) => CompactType::default(),
            _ => self.compact_neg_bound_id(bound.neg, weight),
        }
    }

    pub(super) fn is_unweighted_neg_var_alias(
        bound_weights: &ConstraintWeights,
        outer_weight: &ConstraintWeight,
    ) -> bool {
        // Compact only stores subtract weight on covariant variable occurrences. A weighted
        // negative var-var edge is not a plain alias; replayed concrete bounds carry the
        // representable consequences.
        outer_weight.is_empty() && bound_weights.is_empty()
    }

    pub(super) fn compact_neg_row_upper_bound(
        &mut self,
        source: TypeVar,
        items: Vec<NegId>,
        tail: NegId,
        weight: ConstraintWeight,
        cancelled: &ConstraintWeight,
    ) -> CompactType {
        let mut retained_items = items;
        for fact in self.machine.subtracts().facts(source) {
            if cancelled.contains(fact.id) {
                continue;
            }
            retained_items =
                self.retain_neg_row_items_by_subtractability(retained_items, &fact.subtractability);
        }

        if retained_items.is_empty() {
            self.compact_neg_row_tail_id(tail, weight)
        } else {
            self.compact_neg_row(retained_items, tail, weight)
        }
    }

    pub(super) fn retain_neg_row_items_by_subtractability(
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
            Subtractability::SetMany(families) => items
                .into_iter()
                .filter(|item| {
                    families
                        .iter()
                        .any(|(path, _)| self.neg_effect_family_matches(*item, path))
                })
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

    pub(super) fn neg_effect_family_matches(&self, item: NegId, path: &[String]) -> bool {
        matches!(self.machine.types().neg(item), Neg::Con(item_path, _) if item_path == path)
    }

    pub(super) fn compact_pos_bound_id(
        &mut self,
        id: PosId,
        weight: ConstraintWeight,
    ) -> CompactType {
        match self.machine.types().pos(id).clone() {
            Pos::Var(var) => CompactType::from_var(self.compact_secondary_var_occurrence(
                var,
                Polarity::Positive,
                weight,
            )),
            Pos::NonSubtract(pos, subtract) => {
                let weight = weight.union(&ConstraintWeight::from_ids([subtract]));
                self.compact_pos_bound_id(pos, weight)
            }
            Pos::Stack {
                inner,
                weight: stack_weight,
            } => {
                let families = self.compact_weight_stack_families(&stack_weight);
                let compact = self.compact_pos_bound_id(inner, stack_weight.union(&weight));
                self.record_stack_families_row_coexistence(&families, &compact);
                compact
            }
            Pos::Union(lhs, rhs) => {
                let lhs = self.compact_pos_bound_id(lhs, weight.clone());
                let rhs = self.compact_pos_bound_id(rhs, weight);
                self.merge_types(true, lhs, rhs)
            }
            _ => self.compact_pos_id(id, weight),
        }
    }

    pub(super) fn compact_neg_bound_id(
        &mut self,
        id: NegId,
        weight: ConstraintWeight,
    ) -> CompactType {
        match self.machine.types().neg(id).clone() {
            Neg::Var(var) if weight.is_empty() => {
                CompactType::from_var(self.compact_secondary_var_occurrence(
                    var,
                    Polarity::Negative,
                    ConstraintWeight::empty(),
                ))
            }
            Neg::Var(_) => CompactType::default(),
            Neg::Stack {
                inner,
                weight: stack_weight,
            } => {
                let families = self.compact_weight_stack_families(&stack_weight);
                let compact = self.compact_neg_bound_id(inner, stack_weight.union(&weight));
                self.record_stack_families_row_coexistence(&families, &compact);
                compact
            }
            Neg::Intersection(lhs, rhs) => {
                let lhs = self.compact_neg_bound_id(lhs, weight.clone());
                let rhs = self.compact_neg_bound_id(rhs, weight);
                self.merge_types(false, lhs, rhs)
            }
            _ => self.compact_neg_id(id, weight),
        }
    }
}
