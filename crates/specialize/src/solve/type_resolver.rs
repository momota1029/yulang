use super::*;

impl<'graph, 'arena, 'solution> TypeResolver<'graph, 'arena, 'solution> {
    pub(super) fn new(graph: &'graph ConstraintGraph<'arena>) -> Self {
        Self {
            graph,
            solution: None,
            lazy_solutions: HashMap::new(),
            resolving: HashSet::new(),
        }
    }

    pub(super) fn with_solution(
        graph: &'graph ConstraintGraph<'arena>,
        solution: &'solution GraphSolution,
    ) -> Self {
        Self {
            graph,
            solution: Some(solution),
            lazy_solutions: HashMap::new(),
            resolving: HashSet::new(),
        }
    }

    pub(super) fn resolve(&mut self, ty: &Type) -> Result<Type, SpecializeError> {
        match ty {
            Type::Any => Ok(Type::Any),
            Type::Never => Ok(Type::Never),
            Type::Con { path, args } => Ok(Type::Con {
                path: path.clone(),
                args: self.resolve_all(args)?,
            }),
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => Ok(Type::Fun {
                arg: Box::new(self.resolve(arg)?),
                arg_effect: Box::new(self.resolve(arg_effect)?),
                ret_effect: Box::new(self.resolve(ret_effect)?),
                ret: Box::new(self.resolve(ret)?),
            }),
            Type::Thunk { effect, value } => {
                let effect = self.resolve(effect)?;
                let value = self.resolve(value)?;
                if effect.is_pure_effect() {
                    return Ok(value);
                }
                Ok(Type::Thunk {
                    effect: Box::new(effect),
                    value: Box::new(value),
                })
            }
            Type::Record(fields) => fields
                .iter()
                .map(|field| {
                    Ok(mono::TypeField {
                        name: field.name.clone(),
                        value: self.resolve(&field.value)?,
                        optional: field.optional,
                    })
                })
                .collect::<Result<Vec<_>, _>>()
                .map(Type::Record),
            Type::PolyVariant(variants) => variants
                .iter()
                .map(|variant| {
                    Ok(mono::TypeVariant {
                        name: variant.name.clone(),
                        payloads: self.resolve_all(&variant.payloads)?,
                    })
                })
                .collect::<Result<Vec<_>, _>>()
                .map(Type::PolyVariant),
            Type::Tuple(items) => self.resolve_all(items).map(Type::Tuple),
            Type::EffectRow(items) => self.resolve_effect_row(items),
            Type::Stack { inner, weight } => Ok(types::simplify_stack_type(
                self.resolve(inner)?,
                weight.clone(),
            )),
            Type::Union(left, right) => self.resolve_union(left, right),
            Type::Intersection(left, right) => self.resolve_intersection(left, right),
            Type::OpenVar(slot) => self.slot_solution(*slot),
        }
    }

    pub(super) fn resolve_all(&mut self, tys: &[Type]) -> Result<Vec<Type>, SpecializeError> {
        tys.iter().map(|ty| self.resolve(ty)).collect()
    }

    pub(super) fn resolve_effect_row(&mut self, items: &[Type]) -> Result<Type, SpecializeError> {
        Ok(types::simplify_type(Type::EffectRow(
            items
                .iter()
                .map(|item| self.resolve_effect_item(item))
                .collect::<Result<Vec<_>, _>>()?,
        )))
    }

    pub(super) fn resolve_effect_item(&mut self, item: &Type) -> Result<Type, SpecializeError> {
        let Type::Con { path, args } = item else {
            return self.resolve(item);
        };
        Ok(Type::Con {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| match self.resolve(arg) {
                    Ok(arg) => Ok(arg),
                    Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(Type::unit()),
                    Err(error) => Err(error),
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    pub(super) fn resolve_erased_effectful_actual(
        &mut self,
        actual: &Type,
        expected: Option<&Type>,
    ) -> Option<Type> {
        if let (
            Type::OpenVar(_),
            Some(Type::Thunk {
                effect,
                value: expected_value,
            }),
        ) = (actual, expected)
            && actual == expected_value.as_ref()
            && type_contains_open_var(expected_value)
        {
            let effect = self.resolve(effect).ok()?;
            return Some(Type::Thunk {
                effect: Box::new(effect),
                value: Box::new(Type::unit()),
            });
        }
        let Type::Thunk {
            effect,
            value: actual_value,
        } = actual
        else {
            return None;
        };
        let expected_matches_value = match expected {
            Some(Type::Thunk {
                value: expected_value,
                ..
            }) => actual_value == expected_value,
            Some(expected) => expected == actual_value.as_ref(),
            None => false,
        };
        if !expected_matches_value || !type_contains_open_var(actual_value) {
            return None;
        }
        let effect = self.resolve(effect).ok()?;
        Some(Type::Thunk {
            effect: Box::new(effect),
            value: Box::new(Type::unit()),
        })
    }

    pub(super) fn slot_solution(&mut self, slot: u32) -> Result<Type, SpecializeError> {
        if let Some(solution) = self.solution {
            return match solution.get(slot)?.cloned() {
                Some(solution) => Ok(solution),
                None => Err(SpecializeError::UndeterminedTypeSlot { slot }),
            };
        }
        if let Some(solution) = self.lazy_solutions.get(&slot) {
            return Ok(solution.clone());
        }
        let solution = self
            .try_slot_solution(slot)?
            .ok_or(SpecializeError::UndeterminedTypeSlot { slot })?;
        self.lazy_solutions.insert(slot, solution.clone());
        Ok(solution)
    }

    pub(super) fn try_slot_solution(&mut self, slot: u32) -> Result<Option<Type>, SpecializeError> {
        let slot_data = self.graph.slot(slot)?;
        let slot_kind = slot_data.kind;
        let lower_bounds = slot_data.lower.clone();
        let upper_bounds = slot_data.upper.clone();
        if !self.resolving.insert(slot) {
            return Ok(None);
        }
        let solution = self.compute_slot_solution(slot, slot_kind, &lower_bounds, &upper_bounds)?;
        self.resolving.remove(&slot);
        Ok(solution)
    }

    pub(super) fn compute_slot_solution(
        &mut self,
        slot: u32,
        slot_kind: TypeSlotKind,
        lower_bounds: &[Type],
        upper_bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let lower = self.join_candidates(slot, slot_kind, lower_bounds)?;
        let upper = self.meet_candidates(slot, slot_kind, upper_bounds)?;
        let solution = match (lower, upper) {
            (Some(lower), Some(upper)) if type_candidates_equivalent(&lower, &upper) => lower,
            (Some(lower), Some(upper))
                if let Some(merged) = merge_open_candidate_shape(&lower, &upper) =>
            {
                merged
            }
            (Some(lower), Some(upper)) if type_candidate_subtype(self.graph, &lower, &upper) => {
                lower
            }
            (Some(lower), Some(upper))
                if slot_kind == TypeSlotKind::Effect
                    && self.effect_lower_filtered_by_upper_bounds(
                        &lower,
                        upper_bounds,
                        &upper,
                    )? =>
            {
                upper
            }
            (Some(lower), Some(upper)) => {
                eprintln!(
                    "slot {slot} conflict lower_bounds={lower_bounds:?} upper_bounds={upper_bounds:?} lower={lower:?} upper={upper:?}"
                );
                for (index, slot) in self.graph.slots.iter().enumerate() {
                    if !slot.lower.is_empty() || !slot.upper.is_empty() {
                        eprintln!(
                            "slot {index} kind={:?} lower={:?} upper={:?} succ={:?} pred={:?}",
                            slot.kind, slot.lower, slot.upper, slot.successors, slot.predecessors
                        );
                    }
                }
                return Err(SpecializeError::ConflictingTypeCandidates {
                    slot,
                    existing: lower,
                    incoming: upper,
                });
            }
            (Some(lower), None) => lower,
            (None, Some(_)) if slot_kind == TypeSlotKind::Effect => Type::pure_effect(),
            (None, Some(upper)) => upper,
            (None, None) if slot_kind == TypeSlotKind::Effect => Type::pure_effect(),
            (None, None) => return Ok(None),
        };
        Ok(Some(solution))
    }

    pub(super) fn join_candidates(
        &mut self,
        slot: u32,
        slot_kind: TypeSlotKind,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut candidate: Option<Type> = None;
        for bound in bounds {
            if is_self_stack_bound(slot, bound) {
                continue;
            }
            let Some(resolved) = self.resolve_candidate_bound(bound)? else {
                continue;
            };
            let resolved = effect_slot_candidate(slot_kind, resolved);
            candidate = Some(match candidate {
                Some(existing) if slot_kind == TypeSlotKind::Effect => {
                    join_effect_type_candidates(existing, resolved)
                }
                Some(existing) => {
                    match join_type_candidates(self.graph, slot, existing.clone(), resolved.clone())
                    {
                        Ok(joined) => joined,
                        Err(error) => {
                            eprintln!(
                                "join slot {slot} conflict bounds={bounds:?} existing={existing:?} incoming={resolved:?}"
                            );
                            for (index, slot) in self.graph.slots.iter().enumerate() {
                                if !slot.lower.is_empty() || !slot.upper.is_empty() {
                                    eprintln!(
                                        "slot {index} kind={:?} lower={:?} upper={:?} succ={:?} pred={:?}",
                                        slot.kind,
                                        slot.lower,
                                        slot.upper,
                                        slot.successors,
                                        slot.predecessors
                                    );
                                }
                            }
                            return Err(error);
                        }
                    }
                }
                None => resolved,
            });
        }
        Ok(candidate)
    }

    pub(super) fn meet_candidates(
        &mut self,
        slot: u32,
        slot_kind: TypeSlotKind,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut candidate: Option<Type> = None;
        for bound in bounds {
            if is_self_stack_bound(slot, bound) {
                continue;
            }
            let Some(resolved) = self.resolve_candidate_bound(bound)? else {
                continue;
            };
            let resolved = effect_slot_candidate(slot_kind, resolved);
            candidate = Some(match candidate {
                Some(existing) if slot_kind == TypeSlotKind::Effect => {
                    meet_effect_type_candidates(existing, resolved)
                }
                Some(existing) => meet_type_candidates(self.graph, slot, existing, resolved)?,
                None => resolved,
            });
        }
        Ok(candidate)
    }

    pub(super) fn resolve_candidate_bound(
        &mut self,
        bound: &Type,
    ) -> Result<Option<Type>, SpecializeError> {
        match bound {
            Type::Union(left, right) => {
                return self.resolve_candidate_union_bound(left, right);
            }
            Type::Intersection(left, right) => {
                return self.resolve_candidate_intersection_bound(left, right);
            }
            _ => {}
        }
        match self.resolve(bound) {
            Ok(ty) => Ok(Some(ty)),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(None),
            Err(error) => Err(error),
        }
    }

    pub(super) fn resolve_candidate_union_bound(
        &mut self,
        left: &Type,
        right: &Type,
    ) -> Result<Option<Type>, SpecializeError> {
        match (self.resolve_branch(left)?, self.resolve_branch(right)?) {
            (ResolvedBranch::Type(left), ResolvedBranch::Type(right)) => {
                Ok(Some(simplify_resolved_union(self.graph, left, right)))
            }
            (ResolvedBranch::Type(_), ResolvedBranch::Undetermined(_))
            | (ResolvedBranch::Undetermined(_), ResolvedBranch::Type(_))
            | (ResolvedBranch::Undetermined(_), ResolvedBranch::Undetermined(_)) => Ok(None),
        }
    }

    pub(super) fn resolve_candidate_intersection_bound(
        &mut self,
        left: &Type,
        right: &Type,
    ) -> Result<Option<Type>, SpecializeError> {
        match (self.resolve_branch(left)?, self.resolve_branch(right)?) {
            (ResolvedBranch::Type(left), ResolvedBranch::Type(right)) => Ok(Some(
                simplify_resolved_intersection(self.graph, left, right),
            )),
            (ResolvedBranch::Type(_), ResolvedBranch::Undetermined(_))
            | (ResolvedBranch::Undetermined(_), ResolvedBranch::Type(_))
            | (ResolvedBranch::Undetermined(_), ResolvedBranch::Undetermined(_)) => Ok(None),
        }
    }

    pub(super) fn effect_lower_filtered_by_upper_bounds(
        &mut self,
        lower: &Type,
        upper_bounds: &[Type],
        upper: &Type,
    ) -> Result<bool, SpecializeError> {
        for bound in upper_bounds {
            if self.effect_lower_filtered_by_upper_bound(lower, bound, upper)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn effect_lower_filtered_by_upper_bound(
        &mut self,
        lower: &Type,
        bound: &Type,
        upper: &Type,
    ) -> Result<bool, SpecializeError> {
        match bound {
            Type::Stack { weight, .. } => {
                let filtered = types::simplify_stack_type(lower.clone(), weight.clone());
                Ok(type_candidates_equivalent(&filtered, upper))
            }
            Type::EffectRow(items) => {
                for item in items {
                    if self.effect_lower_filtered_by_upper_bound(lower, item, upper)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Type::Union(left, right) | Type::Intersection(left, right) => Ok(self
                .effect_lower_filtered_by_upper_bound(lower, left, upper)?
                || self.effect_lower_filtered_by_upper_bound(lower, right, upper)?),
            Type::OpenVar(slot) => {
                let Some(solution) = self.try_slot_solution(*slot)? else {
                    return Ok(false);
                };
                self.effect_lower_filtered_by_upper_bound(lower, &solution, upper)
            }
            _ => Ok(false),
        }
    }

    pub(super) fn resolve_union(
        &mut self,
        left: &Type,
        right: &Type,
    ) -> Result<Type, SpecializeError> {
        match (self.resolve_branch(left)?, self.resolve_branch(right)?) {
            (ResolvedBranch::Type(left), ResolvedBranch::Type(right)) => {
                Ok(simplify_resolved_union(self.graph, left, right))
            }
            (ResolvedBranch::Type(left), ResolvedBranch::Undetermined(_))
            | (ResolvedBranch::Undetermined(_), ResolvedBranch::Type(left)) => Ok(left),
            (ResolvedBranch::Undetermined(slot), ResolvedBranch::Undetermined(_)) => {
                Err(SpecializeError::UndeterminedTypeSlot { slot })
            }
        }
    }

    pub(super) fn resolve_intersection(
        &mut self,
        left: &Type,
        right: &Type,
    ) -> Result<Type, SpecializeError> {
        match (self.resolve_branch(left)?, self.resolve_branch(right)?) {
            (ResolvedBranch::Type(left), ResolvedBranch::Type(right)) => {
                Ok(simplify_resolved_intersection(self.graph, left, right))
            }
            (ResolvedBranch::Type(left), ResolvedBranch::Undetermined(_))
            | (ResolvedBranch::Undetermined(_), ResolvedBranch::Type(left)) => Ok(left),
            (ResolvedBranch::Undetermined(slot), ResolvedBranch::Undetermined(_)) => {
                Err(SpecializeError::UndeterminedTypeSlot { slot })
            }
        }
    }

    pub(super) fn resolve_branch(&mut self, ty: &Type) -> Result<ResolvedBranch, SpecializeError> {
        match self.resolve(ty) {
            Ok(ty) => Ok(ResolvedBranch::Type(ty)),
            Err(SpecializeError::UndeterminedTypeSlot { slot }) => {
                Ok(ResolvedBranch::Undetermined(slot))
            }
            Err(error) => Err(error),
        }
    }
}
