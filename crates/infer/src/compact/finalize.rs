use super::merge::*;
use super::*;

pub(crate) fn finalize_compact_root(
    types: &mut TypeArena,
    root: &CompactRoot,
) -> FinalizedCompactRoot {
    CompactFinalizer::new(types).finalize_root(root)
}

#[cfg(test)]
pub(crate) fn finalize_compact_type(types: &mut TypeArena, ty: &CompactType) -> PosId {
    CompactFinalizer::new(types).finalize_pos_type(ty)
}

pub(crate) fn finalize_compact_type_to_neg(types: &mut TypeArena, ty: &CompactType) -> NegId {
    CompactFinalizer::new(types).finalize_neg_type(ty)
}

pub(crate) fn finalize_compact_type_to_pos_constraint(
    machine: &mut ConstraintMachine,
    ty: &CompactType,
) -> PosId {
    CompactFinalizer::new(machine).finalize_pos_type(ty)
}

pub(crate) fn finalize_compact_type_to_neg_constraint(
    machine: &mut ConstraintMachine,
    ty: &CompactType,
) -> NegId {
    CompactFinalizer::new(machine).finalize_neg_type(ty)
}

pub(crate) fn finalize_compact_bounds_to_constraint(
    machine: &mut ConstraintMachine,
    bounds: &CompactBounds,
) -> NeuId {
    CompactFinalizer::new(machine).finalize_bounds(bounds)
}

pub(crate) fn finalize_compact_bounds(types: &mut TypeArena, bounds: &CompactBounds) -> NeuId {
    CompactFinalizer::new(types).finalize_bounds(bounds)
}

pub(crate) fn finalize_compact_bounds_lower(
    types: &mut TypeArena,
    bounds: &CompactBounds,
) -> PosId {
    CompactFinalizer::new(types).finalize_bounds_lower(bounds)
}

pub(crate) fn finalize_compact_bounds_upper(
    types: &mut TypeArena,
    bounds: &CompactBounds,
) -> NegId {
    CompactFinalizer::new(types).finalize_bounds_upper(bounds)
}

pub(super) trait CompactTypeStore {
    fn pos(&self, id: PosId) -> &Pos;
    fn neg(&self, id: NegId) -> &Neg;
    fn alloc_pos(&mut self, pos: Pos) -> PosId;
    fn alloc_neg(&mut self, neg: Neg) -> NegId;
    fn alloc_neu(&mut self, neu: Neu) -> NeuId;
}

impl CompactTypeStore for TypeArena {
    fn pos(&self, id: PosId) -> &Pos {
        TypeArena::pos(self, id)
    }

    fn neg(&self, id: NegId) -> &Neg {
        TypeArena::neg(self, id)
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        TypeArena::alloc_pos(self, pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        TypeArena::alloc_neg(self, neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        TypeArena::alloc_neu(self, neu)
    }
}

impl CompactTypeStore for ConstraintMachine {
    fn pos(&self, id: PosId) -> &Pos {
        self.types().pos(id)
    }

    fn neg(&self, id: NegId) -> &Neg {
        self.types().neg(id)
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        ConstraintMachine::alloc_pos(self, pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        ConstraintMachine::alloc_neg(self, neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        ConstraintMachine::alloc_neu(self, neu)
    }
}

pub(super) struct CompactFinalizer<'a, T> {
    types: &'a mut T,
}

impl<'a, T: CompactTypeStore> CompactFinalizer<'a, T> {
    pub(super) fn new(types: &'a mut T) -> Self {
        Self { types }
    }

    pub(super) fn finalize_root(&mut self, root: &CompactRoot) -> FinalizedCompactRoot {
        let predicate = self.finalize_pos_type(&root.root);
        let rec_vars = root
            .rec_vars
            .iter()
            .map(|rec| SchemeRecursiveBound {
                var: rec.var,
                bounds: self.finalize_bounds(&rec.bounds),
            })
            .collect();
        FinalizedCompactRoot {
            root: predicate,
            rec_vars,
        }
    }

    pub(super) fn finalize_pos_type(&mut self, ty: &CompactType) -> PosId {
        if self.is_positive_rowish(ty) {
            return self.finalize_pos_rowish_type(ty);
        }

        let mut parts = Vec::new();
        for var in &ty.vars {
            parts.push(self.finalize_pos_var(var));
        }
        for builtin in &ty.builtins {
            parts.push(self.alloc_pos(Pos::Con(builtin_path(*builtin), Vec::new())));
        }
        for con in compact_con_entries(&ty.cons) {
            parts.push(self.finalize_pos_con(&con));
        }
        for fun in &ty.funs {
            parts.push(self.finalize_pos_fun(fun));
        }
        for record in &ty.records {
            parts.push(self.finalize_pos_record(record));
        }
        for spread in &ty.record_spreads {
            parts.push(self.finalize_pos_record_spread(spread));
        }
        for variant in &ty.poly_variants {
            parts.push(self.finalize_pos_poly_variant(variant));
        }
        for tuple in &ty.tuples {
            parts.push(self.finalize_pos_tuple(tuple));
        }
        for row in &ty.rows {
            parts.push(self.finalize_pos_row(row));
        }
        self.union_pos(parts)
    }

    pub(super) fn finalize_neg_type(&mut self, ty: &CompactType) -> NegId {
        if ty.never {
            return self.alloc_neg(Neg::Bot);
        }
        if self.is_negative_rowish(ty) {
            return self.finalize_neg_rowish_type(ty);
        }

        let mut parts = Vec::new();
        for var in &ty.vars {
            parts.push(self.finalize_neg_var(var));
        }
        for builtin in &ty.builtins {
            parts.push(self.alloc_neg(Neg::Con(builtin_path(*builtin), Vec::new())));
        }
        for con in compact_con_entries(&ty.cons) {
            parts.push(self.finalize_neg_con(&con));
        }
        for fun in &ty.funs {
            parts.push(self.finalize_neg_fun(fun));
        }
        for record in &ty.records {
            parts.push(self.finalize_neg_record(record));
        }
        for variant in &ty.poly_variants {
            parts.push(self.finalize_neg_poly_variant(variant));
        }
        for tuple in &ty.tuples {
            parts.push(self.finalize_neg_tuple(tuple));
        }
        for row in &ty.rows {
            parts.push(self.finalize_neg_row(row));
        }
        self.intersection_neg(parts)
    }

    pub(super) fn finalize_bounds(&mut self, bounds: &CompactBounds) -> NeuId {
        match bounds {
            CompactBounds::Interval { lower, upper } => {
                if let Some(lifted) =
                    merge_exact_interval_without_center(lower.clone(), upper.clone())
                {
                    return self.finalize_bounds(&lifted);
                }
                let lower = self.finalize_pos_type(lower);
                let upper = self.finalize_neg_type(upper);
                self.alloc_neu(Neu::Bounds(lower, upper))
            }
            CompactBounds::Con { path, args } => {
                let args = args.iter().map(|arg| self.finalize_bounds(arg)).collect();
                self.alloc_neu(Neu::Con(path.clone(), args))
            }
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.finalize_bounds(arg);
                let arg_eff = self.finalize_bounds(arg_eff);
                let ret_eff = self.finalize_bounds(ret_eff);
                let ret = self.finalize_bounds(ret);
                self.alloc_neu(Neu::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                })
            }
            CompactBounds::Record { fields } => {
                let fields = fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.finalize_bounds(&field.value),
                        optional: field.optional,
                    })
                    .collect();
                self.alloc_neu(Neu::Record(fields))
            }
            CompactBounds::PolyVariant { items } => {
                let items = items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.finalize_bounds(payload))
                                .collect(),
                        )
                    })
                    .collect();
                self.alloc_neu(Neu::PolyVariant(items))
            }
            CompactBounds::Tuple { items } => {
                let items = items
                    .iter()
                    .map(|item| self.finalize_bounds(item))
                    .collect();
                self.alloc_neu(Neu::Tuple(items))
            }
        }
    }

    pub(super) fn finalize_bounds_lower(&mut self, bounds: &CompactBounds) -> PosId {
        match bounds {
            CompactBounds::Interval { lower, .. } => self.finalize_pos_type(lower),
            CompactBounds::Con { path, args } => {
                let args = args.iter().map(|arg| self.finalize_bounds(arg)).collect();
                self.alloc_pos(Pos::Con(path.clone(), args))
            }
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.finalize_bounds_upper(arg);
                let arg_eff = self.finalize_bounds_upper(arg_eff);
                let ret_eff = self.finalize_bounds_lower(ret_eff);
                let ret = self.finalize_bounds_lower(ret);
                self.alloc_pos(Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                })
            }
            CompactBounds::Record { fields } => {
                let fields = fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.finalize_bounds_lower(&field.value),
                        optional: field.optional,
                    })
                    .collect();
                self.alloc_pos(Pos::Record(fields))
            }
            CompactBounds::PolyVariant { items } => {
                let items = items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.finalize_bounds_lower(payload))
                                .collect(),
                        )
                    })
                    .collect();
                self.alloc_pos(Pos::PolyVariant(items))
            }
            CompactBounds::Tuple { items } => {
                let items = items
                    .iter()
                    .map(|item| self.finalize_bounds_lower(item))
                    .collect();
                self.alloc_pos(Pos::Tuple(items))
            }
        }
    }

    pub(super) fn finalize_bounds_upper(&mut self, bounds: &CompactBounds) -> NegId {
        match bounds {
            CompactBounds::Interval { upper, .. } => self.finalize_neg_type(upper),
            CompactBounds::Con { path, args } => {
                let args = args.iter().map(|arg| self.finalize_bounds(arg)).collect();
                self.alloc_neg(Neg::Con(path.clone(), args))
            }
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.finalize_bounds_lower(arg);
                let arg_eff = self.finalize_bounds_lower(arg_eff);
                let ret_eff = self.finalize_bounds_upper(ret_eff);
                let ret = self.finalize_bounds_upper(ret);
                self.alloc_neg(Neg::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                })
            }
            CompactBounds::Record { fields } => {
                let fields = fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.finalize_bounds_upper(&field.value),
                        optional: field.optional,
                    })
                    .collect();
                self.alloc_neg(Neg::Record(fields))
            }
            CompactBounds::PolyVariant { items } => {
                let items = items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.finalize_bounds_upper(payload))
                                .collect(),
                        )
                    })
                    .collect();
                self.alloc_neg(Neg::PolyVariant(items))
            }
            CompactBounds::Tuple { items } => {
                let items = items
                    .iter()
                    .map(|item| self.finalize_bounds_upper(item))
                    .collect();
                self.alloc_neg(Neg::Tuple(items))
            }
        }
    }

    pub(super) fn finalize_pos_con(&mut self, con: &CompactCon) -> PosId {
        let args = con
            .args
            .iter()
            .map(|arg| self.finalize_bounds(arg))
            .collect();
        self.alloc_pos(Pos::Con(con.path.clone(), args))
    }

    pub(super) fn finalize_neg_con(&mut self, con: &CompactCon) -> NegId {
        let args = con
            .args
            .iter()
            .map(|arg| self.finalize_bounds(arg))
            .collect();
        self.alloc_neg(Neg::Con(con.path.clone(), args))
    }

    pub(super) fn finalize_pos_fun(&mut self, fun: &CompactFun) -> PosId {
        let arg = self.finalize_neg_type(&fun.arg);
        let arg_eff = self.finalize_neg_effect_type(&fun.arg_eff);
        let ret_eff = self.finalize_pos_effect_type(&fun.ret_eff);
        let ret = self.finalize_pos_type(&fun.ret);
        self.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    pub(super) fn finalize_neg_fun(&mut self, fun: &CompactFun) -> NegId {
        let arg = self.finalize_pos_type(&fun.arg);
        let arg_eff = self.finalize_pos_effect_type(&fun.arg_eff);
        let ret_eff = self.finalize_neg_effect_type(&fun.ret_eff);
        let ret = self.finalize_neg_type(&fun.ret);
        self.alloc_neg(Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    pub(super) fn finalize_pos_record(&mut self, record: &CompactRecord) -> PosId {
        let fields = record
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: self.finalize_pos_type(&field.value),
                optional: field.optional,
            })
            .collect();
        self.alloc_pos(Pos::Record(fields))
    }

    pub(super) fn finalize_neg_record(&mut self, record: &CompactRecord) -> NegId {
        let fields = record
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: self.finalize_neg_type(&field.value),
                optional: field.optional,
            })
            .collect();
        self.alloc_neg(Neg::Record(fields))
    }

    pub(super) fn finalize_pos_record_spread(&mut self, spread: &CompactRecordSpread) -> PosId {
        let fields = spread
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: self.finalize_pos_type(&field.value),
                optional: field.optional,
            })
            .collect();
        let tail = self.finalize_pos_type(&spread.tail);
        if spread.tail_wins {
            self.alloc_pos(Pos::RecordTailSpread { fields, tail })
        } else {
            self.alloc_pos(Pos::RecordHeadSpread { tail, fields })
        }
    }

    pub(super) fn finalize_pos_poly_variant(&mut self, variant: &CompactPolyVariant) -> PosId {
        let items = variant
            .items
            .iter()
            .map(|(name, payloads)| {
                (
                    name.clone(),
                    payloads
                        .iter()
                        .map(|payload| self.finalize_pos_type(payload))
                        .collect(),
                )
            })
            .collect();
        self.alloc_pos(Pos::PolyVariant(items))
    }

    pub(super) fn finalize_neg_poly_variant(&mut self, variant: &CompactPolyVariant) -> NegId {
        let items = variant
            .items
            .iter()
            .map(|(name, payloads)| {
                (
                    name.clone(),
                    payloads
                        .iter()
                        .map(|payload| self.finalize_neg_type(payload))
                        .collect(),
                )
            })
            .collect();
        self.alloc_neg(Neg::PolyVariant(items))
    }

    pub(super) fn finalize_pos_tuple(&mut self, tuple: &CompactTuple) -> PosId {
        let items = tuple
            .items
            .iter()
            .map(|item| self.finalize_pos_type(item))
            .collect();
        self.alloc_pos(Pos::Tuple(items))
    }

    pub(super) fn finalize_neg_tuple(&mut self, tuple: &CompactTuple) -> NegId {
        let items = tuple
            .items
            .iter()
            .map(|item| self.finalize_neg_type(item))
            .collect();
        self.alloc_neg(Neg::Tuple(items))
    }

    pub(super) fn finalize_pos_rowish_type(&mut self, ty: &CompactType) -> PosId {
        let items = self.finalize_pos_effect_row_items(ty);
        self.alloc_pos(Pos::Row(items))
    }

    pub(super) fn finalize_pos_effect_type(&mut self, ty: &CompactType) -> PosId {
        if !self.is_positive_effect_rowish(ty) {
            return self.finalize_pos_type(ty);
        }

        let items = self.finalize_pos_effect_row_items(ty);
        self.alloc_pos(Pos::Row(items))
    }

    pub(super) fn finalize_neg_rowish_type(&mut self, ty: &CompactType) -> NegId {
        let rows = ty
            .rows
            .iter()
            .map(|row| self.finalize_neg_row(row))
            .collect();
        self.intersection_neg(rows)
    }

    pub(super) fn finalize_neg_effect_type(&mut self, ty: &CompactType) -> NegId {
        if self.is_negative_effect_closed_prefix_with_residual(ty) {
            return self.finalize_neg_effect_closed_prefix_with_residual(ty);
        }
        if !self.is_negative_effect_rowish(ty) {
            return self.finalize_neg_type(ty);
        }

        let mut rows = Vec::new();
        if !ty.cons.is_empty() {
            let items = compact_con_entries(&ty.cons)
                .iter()
                .map(|con| self.finalize_neg_con(con))
                .collect();
            let tail = self.alloc_neg(Neg::Top);
            rows.push(self.alloc_neg(Neg::Row(items, tail)));
        }
        rows.extend(ty.rows.iter().map(|row| self.finalize_neg_row(row)));
        self.intersection_neg(rows)
    }

    pub(super) fn finalize_pos_row(&mut self, row: &CompactRow) -> PosId {
        let items = self.finalize_pos_row_items(row);
        self.alloc_pos(Pos::Row(items))
    }

    pub(super) fn finalize_pos_var(&mut self, var: &CompactVar) -> PosId {
        let mut pos = self.alloc_pos(Pos::Var(var.var));
        let weight = principal_stack_weight(&var.weight);
        if !weight.is_empty() {
            pos = self.alloc_pos(Pos::Stack { inner: pos, weight });
        }
        pos
    }

    pub(super) fn finalize_neg_var(&mut self, var: &CompactVar) -> NegId {
        let mut neg = self.alloc_neg(Neg::Var(var.var));
        let weight = principal_stack_weight(&var.weight);
        if !weight.is_empty() {
            neg = self.alloc_neg(Neg::Stack { inner: neg, weight });
        }
        neg
    }

    pub(super) fn finalize_neg_row(&mut self, row: &CompactRow) -> NegId {
        let items = compact_row_item_entries(&row.items)
            .iter()
            .map(|item| self.finalize_neg_con(item))
            .collect();
        let tail = self.finalize_neg_row_tail(&row.tail);
        self.alloc_neg(Neg::Row(items, tail))
    }

    pub(super) fn finalize_neg_row_with_extra_tail(
        &mut self,
        row: &CompactRow,
        extra_tail: &CompactType,
    ) -> NegId {
        let items = compact_row_item_entries(&row.items)
            .iter()
            .map(|item| self.finalize_neg_con(item))
            .collect();
        let tail = merge_compact_types(false, (*row.tail).clone(), extra_tail.clone());
        let tail = self.finalize_neg_row_tail(&tail);
        self.alloc_neg(Neg::Row(items, tail))
    }

    pub(super) fn finalize_pos_effect_row_items(&mut self, ty: &CompactType) -> Vec<PosId> {
        let mut concrete = CompactRowItemMap::default();
        let mut opaque = Vec::new();
        self.collect_pos_effect_type_parts(ty, &mut concrete, &mut opaque);
        self.finalize_collected_pos_row_items(concrete, opaque)
    }

    pub(super) fn finalize_pos_row_items(&mut self, row: &CompactRow) -> Vec<PosId> {
        let mut concrete = CompactRowItemMap::default();
        let mut opaque = Vec::new();
        self.collect_pos_row_parts(row, &mut concrete, &mut opaque);
        self.finalize_collected_pos_row_items(concrete, opaque)
    }

    pub(super) fn finalize_collected_pos_row_items(
        &mut self,
        concrete: CompactRowItemMap,
        mut opaque: Vec<PosId>,
    ) -> Vec<PosId> {
        let mut items = Vec::new();
        for item in compact_row_item_entries(&concrete) {
            let item = self.finalize_pos_con(&item);
            push_unique_pos(&mut items, item);
        }
        for item in opaque.drain(..) {
            push_unique_pos(&mut items, item);
        }
        items
    }

    pub(super) fn collect_pos_effect_type_parts(
        &mut self,
        ty: &CompactType,
        concrete: &mut CompactRowItemMap,
        opaque: &mut Vec<PosId>,
    ) {
        for con in compact_con_entries(&ty.cons) {
            merge_pos_row_item(concrete, con);
        }
        for row in &ty.rows {
            self.collect_pos_row_parts(row, concrete, opaque);
        }
        for var in &ty.vars {
            let item = self.finalize_pos_var(var);
            push_unique_pos(opaque, item);
        }
    }

    pub(super) fn collect_pos_row_parts(
        &mut self,
        row: &CompactRow,
        concrete: &mut CompactRowItemMap,
        opaque: &mut Vec<PosId>,
    ) {
        *concrete = merge_row_items(true, mem::take(concrete), row.items.clone());
        if !is_empty_compact_type(&row.tail) {
            if self.is_positive_effect_rowish(&row.tail) {
                self.collect_pos_effect_type_parts(&row.tail, concrete, opaque);
            } else {
                let tail = self.finalize_pos_type(&row.tail);
                push_unique_pos(opaque, tail);
            }
        }
    }

    pub(super) fn finalize_neg_row_tail(&mut self, ty: &CompactType) -> NegId {
        if is_empty_compact_type(ty) {
            return self.alloc_neg(Neg::Top);
        }
        self.finalize_neg_type(ty)
    }

    pub(super) fn is_positive_rowish(&self, ty: &CompactType) -> bool {
        !ty.rows.is_empty()
            && !ty.never
            && ty.builtins.is_empty()
            && ty.cons.is_empty()
            && ty.funs.is_empty()
            && ty.records.is_empty()
            && ty.record_spreads.is_empty()
            && ty.poly_variants.is_empty()
            && ty.tuples.is_empty()
    }

    pub(super) fn is_positive_effect_rowish(&self, ty: &CompactType) -> bool {
        !ty.never
            && (!ty.cons.is_empty() || !ty.rows.is_empty())
            && ty.builtins.is_empty()
            && ty.funs.is_empty()
            && ty.records.is_empty()
            && ty.record_spreads.is_empty()
            && ty.poly_variants.is_empty()
            && ty.tuples.is_empty()
    }

    pub(super) fn is_negative_rowish(&self, ty: &CompactType) -> bool {
        !ty.rows.is_empty()
            && ty.vars.is_empty()
            && ty.builtins.is_empty()
            && ty.cons.is_empty()
            && ty.funs.is_empty()
            && ty.records.is_empty()
            && ty.record_spreads.is_empty()
            && ty.poly_variants.is_empty()
            && ty.tuples.is_empty()
    }

    pub(super) fn is_negative_effect_rowish(&self, ty: &CompactType) -> bool {
        !ty.never
            && ty.vars.is_empty()
            && (!ty.cons.is_empty() || !ty.rows.is_empty())
            && ty.builtins.is_empty()
            && ty.funs.is_empty()
            && ty.records.is_empty()
            && ty.record_spreads.is_empty()
            && ty.poly_variants.is_empty()
            && ty.tuples.is_empty()
    }

    pub(super) fn is_negative_effect_closed_prefix_with_residual(&self, ty: &CompactType) -> bool {
        !ty.never
            && !ty.vars.is_empty()
            && (!ty.cons.is_empty() || !ty.rows.is_empty())
            && ty.builtins.is_empty()
            && ty.funs.is_empty()
            && ty.records.is_empty()
            && ty.record_spreads.is_empty()
            && ty.poly_variants.is_empty()
            && ty.tuples.is_empty()
            && ty.rows.iter().all(|row| is_empty_compact_type(&row.tail))
    }

    pub(super) fn finalize_neg_effect_closed_prefix_with_residual(
        &mut self,
        ty: &CompactType,
    ) -> NegId {
        let residual_tail = CompactType {
            cons: CompactConMap::default(),
            rows: Vec::new(),
            ..ty.clone()
        };
        let mut rows = Vec::new();
        if !ty.cons.is_empty() {
            let items = compact_con_entries(&ty.cons)
                .iter()
                .map(|con| self.finalize_neg_con(con))
                .collect();
            let tail = self.finalize_neg_row_tail(&residual_tail);
            rows.push(self.alloc_neg(Neg::Row(items, tail)));
        }
        rows.extend(
            ty.rows
                .iter()
                .map(|row| self.finalize_neg_row_with_extra_tail(row, &residual_tail)),
        );
        self.intersection_neg(rows)
    }

    pub(super) fn union_pos(&mut self, input: Vec<PosId>) -> PosId {
        let mut parts = Vec::new();
        for part in input {
            if matches!(self.types.pos(part), Pos::Bot) || parts.contains(&part) {
                continue;
            }
            parts.push(part);
        }
        let Some(first) = parts.first().copied() else {
            return self.alloc_pos(Pos::Bot);
        };
        parts
            .into_iter()
            .skip(1)
            .fold(first, |acc, part| self.alloc_pos(Pos::Union(acc, part)))
    }

    pub(super) fn intersection_neg(&mut self, input: Vec<NegId>) -> NegId {
        if input
            .iter()
            .any(|part| matches!(self.types.neg(*part), Neg::Bot))
        {
            return self.alloc_neg(Neg::Bot);
        }
        let mut parts = Vec::new();
        for part in input {
            if matches!(self.types.neg(part), Neg::Top) || parts.contains(&part) {
                continue;
            }
            parts.push(part);
        }
        let Some(first) = parts.first().copied() else {
            return self.alloc_neg(Neg::Top);
        };
        parts.into_iter().skip(1).fold(first, |acc, part| {
            self.alloc_neg(Neg::Intersection(acc, part))
        })
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.types.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.types.alloc_neg(neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.types.alloc_neu(neu)
    }
}

fn principal_stack_weight(weight: &StackWeight) -> StackWeight {
    weight.with_filter(Subtractability::All)
}

pub(super) fn builtin_path(builtin: BuiltinType) -> Vec<String> {
    vec![builtin.surface_name().into()]
}

pub(super) fn push_unique_pos(items: &mut Vec<PosId>, item: PosId) {
    if !items.contains(&item) {
        items.push(item);
    }
}
