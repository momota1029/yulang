//! Signature effect row annotations lowered into row bounds and stack weights.
//!
//! This module is the boundary where surface rows such as `[io; 'e]` become
//! inference constraints. Keeping it separate makes it easier to audit that
//! stack weights remain lifetime/subtraction metadata and do not become
//! ordinary row requirements accidentally.

use super::*;

impl<'a> SignatureLowerer<'a> {
    pub(super) fn lower_arg_effect_pos(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<PosId, SignatureConstraintError> {
        row.map(|row| self.lower_effect_row_pos(row))
            .unwrap_or_else(|| Ok(self.alloc_pos(Pos::Bot)))
    }

    pub(super) fn lower_arg_effect_neg(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<NegId, SignatureConstraintError> {
        let Some(row) = row else {
            let top = self.alloc_neg(Neg::Top);
            return Ok(self.alloc_neg(Neg::Row(Vec::new(), top)));
        };
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            return self.lower_subtractable_effect_row_neg(row);
        }

        let effect = self.fresh_type_var();
        self.connect_effect_row_lower(effect, row)?;
        Ok(self.alloc_neg(Neg::Var(effect)))
    }

    pub(super) fn lower_ret_effect_pos(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<PosId, SignatureConstraintError> {
        row.map(|row| self.lower_effect_row_pos(row))
            .unwrap_or_else(|| Ok(self.alloc_pos(Pos::Bot)))
    }

    pub(super) fn lower_data_ret_effect_pos(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<PosId, SignatureConstraintError> {
        row.map(|row| self.lower_data_effect_row_pos(row))
            .unwrap_or_else(|| Ok(self.alloc_pos(Pos::Bot)))
    }

    pub(super) fn lower_ret_effect_neg(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<NegId, SignatureConstraintError> {
        let Some(row) = row else {
            let top = self.alloc_neg(Neg::Top);
            return Ok(self.alloc_neg(Neg::Row(Vec::new(), top)));
        };
        self.lower_ret_subtractable_effect_row_neg(row)
    }

    pub(super) fn lower_data_ret_effect_neg(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<NegId, SignatureConstraintError> {
        row.map(|row| self.lower_data_effect_row_neg(row))
            .unwrap_or_else(|| {
                let top = self.alloc_neg(Neg::Top);
                Ok(self.alloc_neg(Neg::Row(Vec::new(), top)))
            })
    }

    pub(super) fn lower_effect_row_pos(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<PosId, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            let effect = self.fresh_type_var();
            self.connect_effect_tail_exact(effect, row);
            let stack = self.effect_row_stack(row)?;
            self.register_stack_facts(effect, &stack.weight);
            let effect = self.alloc_pos(Pos::Var(effect));
            return Ok(self.wrap_pos_with_stack(effect, &stack.weight));
        }

        let mut items = Vec::with_capacity(row.items.len() + usize::from(row.tail.is_some()));
        for atom in &row.items {
            let SignatureEffectAtom::Type(ty) = atom else {
                unreachable!("wildcard checked above");
            };
            items.push(self.lower_pos(ty)?);
        }
        if let Some(tail) = &row.tail {
            let tail = self.signature_var(tail);
            items.push(self.alloc_pos(Pos::Var(tail)));
        }
        Ok(self.alloc_pos(Pos::Row(items)))
    }

    pub(super) fn lower_data_effect_row_pos(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<PosId, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            return Err(SignatureConstraintError::WildcardEffectRowInTypePosition);
        }
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let tail = self.signature_var(tail);
            return Ok(self.alloc_pos(Pos::Var(tail)));
        }

        let mut items = Vec::with_capacity(row.items.len() + usize::from(row.tail.is_some()));
        for atom in &row.items {
            let SignatureEffectAtom::Type(ty) = atom else {
                unreachable!("wildcard checked above");
            };
            items.push(self.lower_data_pos(ty)?);
        }
        if let Some(tail) = &row.tail {
            let public_tail = self.signature_var(tail);
            let (tail, weight) = self.data_effect_tail_stack(public_tail, row)?;
            let tail = self.alloc_pos(Pos::Var(tail));
            items.push(self.wrap_pos_with_stack(tail, &weight));
        }
        Ok(self.alloc_pos(Pos::Row(items)))
    }

    pub(super) fn lower_subtractable_effect_row_neg(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<NegId, SignatureConstraintError> {
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let tail = self.signature_var(tail);
            return Ok(self.alloc_neg(Neg::Var(tail)));
        }

        let effect = self.fresh_type_var();
        self.connect_effect_tail_exact(effect, row);
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(effect, &stack.weight);
        let effect = self.alloc_neg(Neg::Var(effect));
        Ok(self.wrap_neg_with_stack(effect, &stack.weight))
    }

    fn lower_ret_subtractable_effect_row_neg(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<NegId, SignatureConstraintError> {
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let tail = self.signature_var(tail);
            return Ok(self.alloc_neg(Neg::Var(tail)));
        }

        let effect = self.function_boundary_effect_stack_inner(row);
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(effect, &stack.weight);
        let filter = signature_effect_stack_filter_from_weight(&stack.weight);
        let effect = self.alloc_neg(Neg::Var(effect));
        Ok(self.wrap_neg_with_stack(effect, &StackWeight::filter(filter)))
    }

    pub(super) fn lower_data_effect_row_neg(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<NegId, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            return Err(SignatureConstraintError::WildcardEffectRowInTypePosition);
        }
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let tail = self.signature_var(tail);
            return Ok(self.alloc_neg(Neg::Var(tail)));
        }

        let items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_neg(atom))
            .collect::<Result<Vec<_>, _>>()?;
        let tail = if let Some(tail) = &row.tail {
            let public_tail = self.signature_var(tail);
            let (tail, weight) = self.data_effect_tail_stack(public_tail, row)?;
            let tail = self.alloc_neg(Neg::Var(tail));
            self.wrap_neg_with_stack(tail, &weight)
        } else {
            self.alloc_neg(Neg::Top)
        };
        Ok(self.alloc_neg(Neg::Row(items, tail)))
    }

    pub(super) fn lower_effect_row_neg(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<NegId, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            return Err(SignatureConstraintError::WildcardEffectRowInTypePosition);
        }

        let items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_neg(atom))
            .collect::<Result<Vec<_>, _>>()?;
        let tail = if let Some(tail) = &row.tail {
            let tail = self.signature_var(tail);
            self.alloc_neg(Neg::Var(tail))
        } else {
            self.alloc_neg(Neg::Top)
        };
        Ok(self.alloc_neg(Neg::Row(items, tail)))
    }

    fn lower_effect_atom_neg(
        &mut self,
        atom: &SignatureEffectAtom,
    ) -> Result<NegId, SignatureConstraintError> {
        match atom {
            SignatureEffectAtom::Type(ty) => self.lower_data_neg(ty),
            SignatureEffectAtom::Wildcard => {
                Err(SignatureConstraintError::WildcardEffectRowInTypePosition)
            }
        }
    }

    fn data_effect_tail_stack(
        &mut self,
        public_tail: TypeVar,
        row: &SignatureEffectRow,
    ) -> Result<(TypeVar, StackWeight), SignatureConstraintError> {
        let atoms = row
            .items
            .iter()
            .map(|atom| self.effect_atom_con(atom))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if atoms.is_empty() {
            return Ok((public_tail, StackWeight::empty()));
        }

        let private = self.data_effect_private_tail(public_tail, row);
        let subtractability = match atoms.as_slice() {
            [(path, _)] => Subtractability::AllExcept(path.clone(), Vec::new()),
            _ => Subtractability::AllExceptMany(
                atoms
                    .into_iter()
                    .map(|(path, _)| (path, Vec::new()))
                    .collect(),
            ),
        };
        // The data-function tail carries private stack evidence internally. The public type
        // parameter denotes the residual row itself, so the erased private tail flows to it as a
        // row rather than as a naked effect item.
        self.infer
            .declared_subtract_fact(private.tail, private.subtract, subtractability.clone());
        let private_tail = self.alloc_pos(Pos::Var(private.tail));
        let private_lower = self.alloc_pos(Pos::Row(vec![private_tail]));
        let public_upper = self.alloc_neg(Neg::Var(public_tail));
        self.infer.subtype(private_lower, public_upper);
        Ok((
            private.tail,
            StackWeight::push(private.subtract, subtractability),
        ))
    }

    fn data_effect_private_tail(
        &mut self,
        public_tail: TypeVar,
        row: &SignatureEffectRow,
    ) -> DataEffectPrivateTail {
        let key = DataEffectTailKey {
            row: row as *const SignatureEffectRow as usize,
            public_tail,
        };
        if let Some(private) = self.state.data_effect_private_tails.get(&key) {
            return *private;
        }
        let private = DataEffectPrivateTail {
            tail: self.fresh_type_var(),
            subtract: self.infer.fresh_subtract_id(),
        };
        self.state.data_effect_private_tails.insert(key, private);
        private
    }

    fn function_boundary_effect_stack_inner(&mut self, row: &SignatureEffectRow) -> TypeVar {
        if let Some(tail) = &row.tail {
            return self.signature_var(tail);
        }
        if !row.items.is_empty()
            && let Some(key) = closed_signature_effect_row_key(row)
        {
            if let Some(found) = self.state.closed_effect_rows.get(&key) {
                return *found;
            }
            let effect = self.fresh_type_var();
            self.state.closed_effect_rows.insert(key, effect);
            return effect;
        }
        self.fresh_type_var()
    }

    fn connect_effect_tail_exact(&mut self, effect: TypeVar, row: &SignatureEffectRow) {
        let Some(tail) = &row.tail else {
            return;
        };
        let tail = self.signature_var(tail);
        if tail == effect {
            return;
        }
        let tail_lower = self.alloc_pos(Pos::Var(tail));
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        self.infer.subtype(tail_lower, effect_upper);
        let effect_lower = self.alloc_pos(Pos::Var(effect));
        let tail_upper = self.alloc_neg(Neg::Var(tail));
        self.infer.subtype(effect_lower, tail_upper);
    }

    fn connect_effect_row_lower(
        &mut self,
        effect: TypeVar,
        row: &SignatureEffectRow,
    ) -> Result<(), SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            return Ok(());
        }
        let lower = self.lower_effect_row_pos(row)?;
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        self.infer.subtype(lower, effect_upper);
        Ok(())
    }

    fn effect_row_stack(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<SignatureEffectStack, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            let id = self.infer.fresh_subtract_id();
            return Ok(SignatureEffectStack {
                weight: StackWeight::push(id, Subtractability::All),
                ids: vec![id],
            });
        }

        let atoms = row
            .items
            .iter()
            .map(|atom| self.effect_atom_con(atom))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if atoms.is_empty() {
            if row.tail.is_none() {
                let id = self.infer.fresh_subtract_id();
                return Ok(SignatureEffectStack {
                    weight: StackWeight::push(id, Subtractability::Empty),
                    ids: vec![id],
                });
            }
            return Ok(SignatureEffectStack::empty());
        }

        let id = self.infer.fresh_subtract_id();
        Ok(SignatureEffectStack {
            weight: StackWeight::push(id, signature_subtractability_from_atoms(atoms)),
            ids: vec![id],
        })
    }

    fn wrap_neg_with_stack(&mut self, neg: NegId, weight: &StackWeight) -> NegId {
        if weight.is_empty() {
            return neg;
        }
        self.alloc_neg(Neg::Stack {
            inner: neg,
            weight: weight.clone(),
        })
    }

    fn register_stack_facts(&mut self, var: TypeVar, weight: &StackWeight) {
        for entry in weight.entries() {
            for subtractability in &entry.stack {
                self.infer
                    .declared_subtract_fact(var, entry.id, subtractability.clone());
            }
        }
    }

    fn wrap_pos_with_stack(&mut self, pos: PosId, weight: &StackWeight) -> PosId {
        if weight.is_empty() {
            return pos;
        }
        self.alloc_pos(Pos::Stack {
            inner: pos,
            weight: weight.clone(),
        })
    }

    fn effect_atom_con(
        &mut self,
        atom: &SignatureEffectAtom,
    ) -> Result<Option<(Vec<String>, Vec<NeuId>)>, SignatureConstraintError> {
        match atom {
            SignatureEffectAtom::Type(SignatureType::Var(_)) => Ok(None),
            SignatureEffectAtom::Type(ty) => self.constructor_path(ty).map(Some),
            SignatureEffectAtom::Wildcard => Ok(None),
        }
    }
}

fn signature_effect_stack_filter_from_weight(weight: &StackWeight) -> Subtractability {
    weight
        .active_stack_items()
        .cloned()
        .reduce(Subtractability::intersect)
        .unwrap_or(Subtractability::All)
}

fn closed_signature_effect_row_key(
    row: &SignatureEffectRow,
) -> Option<SignatureClosedEffectRowKey> {
    if row.tail.is_some()
        || row.items.is_empty()
        || row
            .items
            .iter()
            .any(|item| matches!(item, SignatureEffectAtom::Wildcard))
    {
        return None;
    }
    let items = row
        .items
        .iter()
        .map(|item| match item {
            SignatureEffectAtom::Type(ty) => closed_signature_effect_type_key(ty),
            SignatureEffectAtom::Wildcard => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some(SignatureClosedEffectRowKey(items))
}

fn closed_signature_effect_type_key(ty: &SignatureType) -> Option<SignatureClosedEffectAtomKey> {
    Some(match ty {
        SignatureType::Builtin(builtin) => SignatureClosedEffectAtomKey::Builtin(*builtin),
        SignatureType::Named(id) => SignatureClosedEffectAtomKey::Named(*id),
        SignatureType::Var(var) => SignatureClosedEffectAtomKey::Var(var.name.clone()),
        SignatureType::EffectRow(row) => {
            SignatureClosedEffectAtomKey::EffectRow(closed_signature_effect_row_key(row)?)
        }
        SignatureType::Effectful { eff, ret } => SignatureClosedEffectAtomKey::Effectful {
            eff: closed_signature_effect_row_key(eff)?,
            ret: Box::new(closed_signature_effect_type_key(ret)?),
        },
        SignatureType::Tuple(items) => SignatureClosedEffectAtomKey::Tuple(
            items
                .iter()
                .map(closed_signature_effect_type_key)
                .collect::<Option<Vec<_>>>()?,
        ),
        SignatureType::Apply { callee, args } => SignatureClosedEffectAtomKey::Apply {
            callee: Box::new(closed_signature_effect_type_key(callee)?),
            args: args
                .iter()
                .map(closed_signature_effect_type_key)
                .collect::<Option<Vec<_>>>()?,
        },
        SignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => SignatureClosedEffectAtomKey::Function {
            param: Box::new(closed_signature_effect_type_key(param)?),
            arg_eff: match arg_eff {
                Some(row) => Some(closed_signature_effect_row_key(row)?),
                None => None,
            },
            ret_eff: match ret_eff {
                Some(row) => Some(closed_signature_effect_row_key(row)?),
                None => None,
            },
            ret: Box::new(closed_signature_effect_type_key(ret)?),
        },
    })
}
