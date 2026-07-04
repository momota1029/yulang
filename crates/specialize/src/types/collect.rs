use super::*;

impl<'a> SchemeMaterializer<'a> {
    pub(super) fn collect_pos_kind(&mut self, id: PosId, context: TypeContext) {
        match self.arena.pos(id) {
            Pos::Var(var) => self.record_kind(*var, context),
            Pos::Con(path, args) => self.collect_con_arg_kinds(path, args),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_neg_kind(*arg, TypeContext::Value);
                self.collect_neg_kind(*arg_eff, TypeContext::Effect);
                self.collect_pos_kind(*ret_eff, TypeContext::Effect);
                self.collect_pos_kind(*ret, TypeContext::Value);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.collect_pos_kind(field.value, TypeContext::Value);
                }
            }
            Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { tail, fields } => {
                for field in fields {
                    self.collect_pos_kind(field.value, TypeContext::Value);
                }
                self.collect_pos_kind(*tail, TypeContext::Value);
            }
            Pos::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    self.collect_pos_kinds(payloads, TypeContext::Value);
                }
            }
            Pos::Tuple(items) => self.collect_pos_kinds(items, TypeContext::Value),
            Pos::Row(items) => self.collect_pos_kinds(items, TypeContext::Effect),
            Pos::Stack { inner, weight } => {
                self.collect_pos_kind(*inner, context);
                self.collect_stack_weight_kinds(weight);
            }
            Pos::NonSubtract(inner, _) => self.collect_pos_kind(*inner, context),
            Pos::Union(left, right) => {
                self.collect_pos_kind(*left, context);
                self.collect_pos_kind(*right, context);
            }
            Pos::Bot => {
                if self.track_empty_bounds && context == TypeContext::Value {
                    self.empty_bound_kinds.push(context);
                }
            }
        }
    }

    pub(super) fn collect_neg_kind(&mut self, id: NegId, context: TypeContext) {
        match self.arena.neg(id) {
            Neg::Var(var) => self.record_kind(*var, context),
            Neg::Con(path, args) => self.collect_con_arg_kinds(path, args),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_pos_kind(*arg, TypeContext::Value);
                self.collect_pos_kind(*arg_eff, TypeContext::Effect);
                self.collect_neg_kind(*ret_eff, TypeContext::Effect);
                self.collect_neg_kind(*ret, TypeContext::Value);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.collect_neg_kind(field.value, TypeContext::Value);
                }
            }
            Neg::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    self.collect_neg_kinds(payloads, TypeContext::Value);
                }
            }
            Neg::Tuple(items) => self.collect_neg_kinds(items, TypeContext::Value),
            Neg::Row(items, tail) => {
                self.collect_neg_kinds(items, TypeContext::Effect);
                self.collect_neg_kind(*tail, TypeContext::Effect);
            }
            Neg::Stack { inner, weight } => {
                self.collect_neg_kind(*inner, context);
                self.collect_stack_weight_kinds(weight);
            }
            Neg::Intersection(left, right) => {
                self.collect_neg_kind(*left, context);
                self.collect_neg_kind(*right, context);
            }
            Neg::Top => {
                if self.track_empty_bounds && context == TypeContext::Value {
                    self.empty_bound_kinds.push(context);
                }
            }
            Neg::Bot => {}
        }
    }

    pub(super) fn collect_neu_kind(&mut self, id: NeuId, context: TypeContext) {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                let has_lower = !matches!(self.arena.pos(*lower), Pos::Bot);
                let has_upper = !matches!(self.arena.neg(*upper), Neg::Top);
                if self.bound_materialization == BoundMaterialization::Fresh
                    && (has_lower || has_upper)
                {
                    self.record_inline_bound_kind(id, context);
                    if has_lower {
                        self.collect_pos_kind(*lower, context);
                    }
                    if has_upper {
                        self.collect_neg_kind(*upper, context);
                    }
                    return;
                }
                let empty = !has_lower && !has_upper;
                if self.track_empty_bounds && empty && context == TypeContext::Value {
                    self.empty_bound_kinds.push(context);
                    return;
                }
                self.collect_pos_kind(*lower, context);
                self.collect_neg_kind(*upper, context);
            }
            Neu::Con(path, args) => self.collect_con_arg_kinds(path, args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_neu_kind(*arg, TypeContext::Value);
                self.collect_neu_kind(*arg_eff, TypeContext::Effect);
                self.collect_neu_kind(*ret_eff, TypeContext::Effect);
                self.collect_neu_kind(*ret, TypeContext::Value);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.collect_neu_kind(field.value, TypeContext::Value);
                }
            }
            Neu::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    self.collect_neu_kinds(payloads, TypeContext::Value);
                }
            }
            Neu::Tuple(items) => self.collect_neu_kinds(items, TypeContext::Value),
        }
    }

    pub(super) fn collect_pos_kinds(&mut self, ids: &[PosId], context: TypeContext) {
        for id in ids {
            self.collect_pos_kind(*id, context);
        }
    }

    pub(super) fn collect_neg_kinds(&mut self, ids: &[NegId], context: TypeContext) {
        for id in ids {
            self.collect_neg_kind(*id, context);
        }
    }

    pub(super) fn collect_neu_kinds(&mut self, ids: &[NeuId], context: TypeContext) {
        for id in ids {
            self.collect_neu_kind(*id, context);
        }
    }

    pub(super) fn collect_con_arg_kinds(&mut self, path: &[String], args: &[NeuId]) {
        for (index, arg) in args.iter().enumerate() {
            let context = con_arg_context(path, index);
            if context == TypeContext::Effect {
                self.collect_neu_kind(*arg, context);
            } else {
                self.collect_nominal_arg_kind(*arg, context);
            }
        }
    }

    pub(super) fn collect_nominal_arg_kind(&mut self, id: NeuId, context: TypeContext) {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                self.collect_pos_default_kind(*lower, context);
                self.collect_neg_default_kind(*upper, context);
            }
            Neu::Con(path, args) => self.collect_con_arg_kinds(path, args),
            _ => self.collect_neu_kind(id, context),
        }
    }

    pub(super) fn collect_pos_default_kind(&mut self, id: PosId, context: TypeContext) {
        match self.arena.pos(id) {
            Pos::Var(var) => self.record_default_kind(*var, context),
            Pos::Con(path, args) => self.collect_con_arg_kinds(path, args),
            Pos::Stack { inner, weight } => {
                self.collect_pos_default_kind(*inner, context);
                self.collect_stack_weight_kinds(weight);
            }
            Pos::NonSubtract(inner, weight) => {
                self.collect_pos_default_kind(*inner, context);
                self.collect_stack_weight_kinds(weight);
            }
            Pos::Union(left, right) => {
                self.collect_pos_default_kind(*left, context);
                self.collect_pos_default_kind(*right, context);
            }
            _ => self.collect_pos_kind(id, context),
        }
    }

    pub(super) fn collect_neg_default_kind(&mut self, id: NegId, context: TypeContext) {
        match self.arena.neg(id) {
            Neg::Var(var) => self.record_default_kind(*var, context),
            Neg::Con(path, args) => self.collect_con_arg_kinds(path, args),
            Neg::Stack { inner, weight } => {
                self.collect_neg_default_kind(*inner, context);
                self.collect_stack_weight_kinds(weight);
            }
            Neg::Intersection(left, right) => {
                self.collect_neg_default_kind(*left, context);
                self.collect_neg_default_kind(*right, context);
            }
            _ => self.collect_neg_kind(id, context),
        }
    }

    pub(super) fn collect_stack_weight_kinds(&mut self, weight: &StackWeight) {
        for entry in weight.entries() {
            for item in entry.floor.iter().chain(&entry.stack) {
                self.collect_subtractability_kinds(item);
            }
        }
    }

    pub(super) fn collect_subtractability_kinds(&mut self, item: &Subtractability) {
        match item {
            Subtractability::Empty | Subtractability::All => {}
            Subtractability::AllExcept(_, args) | Subtractability::Set(_, args) => {
                self.collect_neu_kinds(args, TypeContext::Value);
            }
            Subtractability::AllExceptMany(families) | Subtractability::SetMany(families) => {
                for (_, args) in families {
                    self.collect_neu_kinds(args, TypeContext::Value);
                }
            }
        }
    }
}
