use super::*;

impl<'a, 'solution> TypeResolver<'a, 'solution> {
    pub(super) fn new(graph: &'a TypeGraph<'a>, solution: &'solution Solution) -> Self {
        Self {
            graph,
            solution,
            resolving: HashSet::new(),
            candidate_cache: HashMap::new(),
        }
    }

    pub(super) fn resolve(&mut self, ty: &Type) -> Result<Type, SpecializeError> {
        match ty {
            Type::Any | Type::Never => Ok(ty.clone()),
            Type::OpenVar(slot) => self.slot_solution(*slot),
            Type::Con { path, args } => Ok(Type::Con {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.resolve(arg))
                    .collect::<Result<Vec<_>, _>>()?,
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
                Ok(types::runtime_shape(effect, value))
            }
            Type::Record(fields) => Ok(Type::Record(
                fields
                    .iter()
                    .map(|field| {
                        Ok(TypeField {
                            name: field.name.clone(),
                            value: self.resolve(&field.value)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            )),
            Type::PolyVariant(variants) => Ok(Type::PolyVariant(
                variants
                    .iter()
                    .map(|variant| {
                        Ok(TypeVariant {
                            name: variant.name.clone(),
                            payloads: variant
                                .payloads
                                .iter()
                                .map(|payload| self.resolve(payload))
                                .collect::<Result<Vec<_>, _>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            )),
            Type::Tuple(items) => Ok(Type::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve(item))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Type::EffectRow(items) => Ok(types::simplify_type(Type::EffectRow(
                items
                    .iter()
                    .map(|item| self.resolve_effect_item(item))
                    .collect::<Result<Vec<_>, _>>()?,
            ))),
            Type::Stack { inner, weight } => {
                let resolved = types::simplify_stack_type(self.resolve(inner)?, weight.clone());
                if matches!(resolved, Type::Stack { .. }) {
                    return Err(SpecializeError::UnresolvedStackWeight { ty: resolved });
                }
                Ok(resolved)
            }
            Type::Union(left, right) => {
                let left = self.resolve(left)?;
                let right = self.resolve(right)?;
                self.join_explicit_union(left, right)
            }
            Type::Intersection(left, right) => {
                let left = self.resolve(left)?;
                let right = self.resolve(right)?;
                self.meet_explicit_intersection(left, right)
            }
        }
    }

    pub(super) fn resolve_with_context(
        &mut self,
        ty: &Type,
        context: &Type,
    ) -> Result<Type, SpecializeError> {
        match self.resolve(ty) {
            Ok(resolved) if type_contains_open_var(&resolved) => {
                self.resolve_from_context(&resolved, context, true)
            }
            Ok(ty) => Ok(ty),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => {
                self.resolve_from_context(ty, context, false)
            }
            Err(error) => Err(error),
        }
    }

    pub(super) fn resolve_with_context_leaf(
        &mut self,
        ty: &Type,
        context: &Type,
    ) -> Result<Type, SpecializeError> {
        match self.resolve(ty) {
            Ok(resolved) if type_contains_open_var(&resolved) => {
                self.resolve_from_context(&resolved, context, true)
            }
            Ok(ty) => Ok(ty),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => {
                self.resolve_from_context(ty, context, true)
            }
            Err(error) => Err(error),
        }
    }

    pub(super) fn resolve_from_context(
        &mut self,
        ty: &Type,
        context: &Type,
        allow_leaf: bool,
    ) -> Result<Type, SpecializeError> {
        if let Type::OpenVar(slot) = ty {
            return match self.solution.slots.get(*slot as usize) {
                Some(SlotSolution::Resolved(solution)) => {
                    let solution = solution.clone();
                    self.resolve_from_context(&solution, context, allow_leaf)
                }
                Some(SlotSolution::Unknown) if allow_leaf => self.resolve(context),
                Some(SlotSolution::Unknown) => {
                    Err(SpecializeError::UndeterminedTypeSlot { slot: *slot })
                }
                Some(SlotSolution::Conflicting { existing, incoming }) => {
                    Err(SpecializeError::ConflictingTypeCandidates {
                        slot: *slot,
                        existing: existing.clone(),
                        incoming: incoming.clone(),
                    })
                }
                None => Err(SpecializeError::InvalidTypeSlot { slot: *slot }),
            };
        }
        match (ty, context) {
            (
                Type::Con { path, args },
                Type::Con {
                    path: context_path,
                    args: context_args,
                },
            ) if path == context_path && args.len() == context_args.len() => Ok(Type::Con {
                path: path.clone(),
                args: args
                    .iter()
                    .zip(context_args.iter())
                    .map(|(arg, context)| self.resolve_with_context_leaf(arg, context))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            (
                Type::Fun {
                    arg,
                    arg_effect,
                    ret_effect,
                    ret,
                },
                Type::Fun {
                    arg: context_arg,
                    arg_effect: context_arg_effect,
                    ret_effect: context_ret_effect,
                    ret: context_ret,
                },
            ) => {
                let (arg, arg_effect) =
                    split_declared_runtime_shape(arg.as_ref().clone(), arg_effect.as_ref().clone());
                let (ret, ret_effect) =
                    split_declared_runtime_shape(ret.as_ref().clone(), ret_effect.as_ref().clone());
                let (context_arg, context_arg_effect) = split_declared_runtime_shape(
                    context_arg.as_ref().clone(),
                    context_arg_effect.as_ref().clone(),
                );
                let (context_ret, context_ret_effect) = split_declared_runtime_shape(
                    context_ret.as_ref().clone(),
                    context_ret_effect.as_ref().clone(),
                );
                Ok(Type::Fun {
                    arg: Box::new(self.resolve_with_context_leaf(&arg, &context_arg)?),
                    arg_effect: Box::new(
                        self.resolve_with_context_leaf(&arg_effect, &context_arg_effect)?,
                    ),
                    ret_effect: Box::new(
                        self.resolve_with_context_leaf(&ret_effect, &context_ret_effect)?,
                    ),
                    ret: Box::new(self.resolve_with_context_leaf(&ret, &context_ret)?),
                })
            }
            (
                Type::Thunk { effect, value },
                Type::Thunk {
                    effect: context_effect,
                    value: context_value,
                },
            ) => Ok(types::runtime_shape(
                self.resolve_with_context_leaf(effect, context_effect)?,
                self.resolve_with_context_leaf(value, context_value)?,
            )),
            (Type::Tuple(items), Type::Tuple(context_items))
                if items.len() == context_items.len() =>
            {
                Ok(Type::Tuple(
                    items
                        .iter()
                        .zip(context_items.iter())
                        .map(|(item, context)| self.resolve_with_context_leaf(item, context))
                        .collect::<Result<Vec<_>, _>>()?,
                ))
            }
            (Type::Record(fields), Type::Record(context_fields)) => Ok(Type::Record(
                fields
                    .iter()
                    .map(|field| {
                        let context = record_field_type(&context_fields, &field.name)
                            .map(|field| &field.value)
                            .unwrap_or(&field.value);
                        Ok(TypeField {
                            name: field.name.clone(),
                            value: self.resolve_with_context_leaf(&field.value, context)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            )),
            (Type::PolyVariant(variants), Type::PolyVariant(context_variants)) => {
                Ok(Type::PolyVariant(
                    variants
                        .iter()
                        .map(|variant| {
                            let context = context_variants.iter().find(|context| {
                                context.name == variant.name
                                    && context.payloads.len() == variant.payloads.len()
                            });
                            let payloads = match context {
                                Some(context) => variant
                                    .payloads
                                    .iter()
                                    .zip(context.payloads.iter())
                                    .map(|(payload, context)| {
                                        self.resolve_with_context_leaf(payload, context)
                                    })
                                    .collect::<Result<Vec<_>, _>>()?,
                                None => self.resolve_partial_candidates(&variant.payloads)?,
                            };
                            Ok(TypeVariant {
                                name: variant.name.clone(),
                                payloads,
                            })
                        })
                        .collect::<Result<Vec<_>, SpecializeError>>()?,
                ))
            }
            (Type::EffectRow(items), Type::EffectRow(context_items)) => {
                let mut resolved = Vec::with_capacity(items.len());
                for item in items {
                    let context = context_items
                        .iter()
                        .find(|context| same_effect_row_family(item, context))
                        .unwrap_or(item);
                    resolved.push(self.resolve_with_context_leaf(item, context)?);
                }
                Ok(types::simplify_type(Type::EffectRow(resolved)))
            }
            (Type::Stack { inner, weight }, Type::Stack { inner: context, .. }) => {
                Ok(types::simplify_stack_type(
                    self.resolve_with_context_leaf(inner, context)?,
                    weight.clone(),
                ))
            }
            (Type::Union(left, right), context) => {
                let left = self.resolve_with_context_leaf(left, context)?;
                let right = self.resolve_with_context_leaf(right, context)?;
                self.join_explicit_union(left, right)
            }
            (Type::Intersection(left, right), context) => {
                let left = self.resolve_with_context_leaf(left, context)?;
                let right = self.resolve_with_context_leaf(right, context)?;
                self.meet_explicit_intersection(left, right)
            }
            _ => self.resolve(ty),
        }
    }

    pub(super) fn resolve_effect_item(&mut self, item: &Type) -> Result<Type, SpecializeError> {
        let Type::Con { path, args } = item else {
            return self.resolve(item);
        };
        Ok(Type::Con {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| self.resolve(arg))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    pub(super) fn slot_solution(&mut self, slot: u32) -> Result<Type, SpecializeError> {
        let ty = match self.solution.slots.get(slot as usize) {
            Some(SlotSolution::Resolved(ty)) => ty.clone(),
            Some(SlotSolution::Unknown) => {
                return Err(SpecializeError::UndeterminedTypeSlot { slot });
            }
            Some(SlotSolution::Conflicting { existing, incoming }) => {
                return Err(SpecializeError::ConflictingTypeCandidates {
                    slot,
                    existing: existing.clone(),
                    incoming: incoming.clone(),
                });
            }
            None => return Err(SpecializeError::InvalidTypeSlot { slot }),
        };
        if !self.resolving.insert(slot) {
            return Ok(ty);
        }
        let resolved = self.resolve(&ty);
        self.resolving.remove(&slot);
        resolved
    }

    pub(super) fn try_slot_solution(&mut self, slot: u32) -> Result<Option<Type>, SpecializeError> {
        if let Some(solution) = self.candidate_cache.get(&slot) {
            return Ok(Some(solution.clone()));
        }
        if !self.resolving.insert(slot) {
            return Ok(None);
        }
        let slot_data = self
            .graph
            .slots
            .get(slot as usize)
            .ok_or(SpecializeError::InvalidTypeSlot { slot })?;
        let solution = self.compute_slot_solution(slot, slot_data)?;
        self.resolving.remove(&slot);
        if let Some(solution) = &solution {
            self.candidate_cache.insert(slot, solution.clone());
        }
        Ok(solution)
    }

    pub(super) fn compute_slot_solution(
        &mut self,
        slot: u32,
        slot_data: &TypeSlot,
    ) -> Result<Option<Type>, SpecializeError> {
        let mut lower = self.join_bounds(slot_data.kind, &slot_data.lower)?;
        for bound in &slot_data.weighted_lower {
            let Some(bound) = self.resolve_weight_inert_bound_candidate(bound)? else {
                continue;
            };
            let bound = effect_slot_candidate(slot_data.kind, bound);
            lower = Some(match lower {
                Some(existing) => join_type_candidates(self.graph, existing, bound)?,
                None => bound,
            });
        }
        let mut upper = self.meet_bounds(slot_data.kind, &slot_data.upper)?;
        for bound in &slot_data.weighted_upper {
            let Some(bound) = self.resolve_weight_inert_bound_candidate(bound)? else {
                continue;
            };
            let bound = effect_slot_candidate(slot_data.kind, bound);
            upper = Some(match upper {
                Some(existing) => meet_type_candidates(self.graph, existing, bound)?,
                None => bound,
            });
        }
        let local_exact = match (&lower, &upper) {
            (Some(lower), Some(upper)) if lower == upper => Some(lower.clone()),
            _ => None,
        };
        if let Some(candidate) = local_exact {
            return self.erase_stack_solution_candidate(Some(candidate));
        }
        for predecessor in &slot_data.predecessors {
            let Some(predecessor) = self.try_slot_solution(*predecessor)? else {
                continue;
            };
            let predecessor = effect_slot_candidate(slot_data.kind, predecessor);
            lower = Some(match lower {
                Some(existing) => join_type_candidates(self.graph, existing, predecessor)?,
                None => predecessor,
            });
        }
        for successor in &slot_data.successors {
            let Some(successor) = self.try_slot_solution(*successor)? else {
                continue;
            };
            let successor = effect_slot_candidate(slot_data.kind, successor);
            upper = Some(match upper {
                Some(existing) => meet_type_candidates(self.graph, existing, successor)?,
                None => successor,
            });
        }
        let open_shape_candidate = match (&lower, &upper) {
            (Some(lower), Some(upper)) => merge_open_candidate_shape(lower, upper),
            _ => None,
        };
        let candidate = match (lower, upper) {
            (Some(lower), Some(upper))
                if value_candidate_subtype_thunk(self.graph, &lower, &upper) =>
            {
                Some(lower)
            }
            (Some(lower), Some(upper))
                if thunk_value_candidate_subtype(self.graph, &lower, &upper) =>
            {
                Some(lower)
            }
            (Some(lower), Some(upper)) if slot_data.kind == TypeSlotKind::Effect => {
                if type_candidate_subtype(self.graph, &lower, &upper) {
                    Some(lower)
                } else if let Some(refined) =
                    refine_effect_lower_with_upper(self.graph, &lower, &upper)?
                {
                    Some(refined)
                } else if effect_rows_have_same_families(self.graph, &lower, &upper) {
                    Some(meet_type_candidates(self.graph, lower, upper)?)
                } else {
                    Err(SpecializeError::ConflictingTypeCandidates {
                        slot,
                        existing: lower,
                        incoming: upper,
                    })?
                }
            }
            (Some(Type::OpenVar(_)), Some(upper)) => Some(upper),
            (Some(lower), Some(Type::OpenVar(_))) => Some(lower),
            (Some(lower), Some(upper @ Type::Union(_, _)))
                if type_candidate_subtype(self.graph, &lower, &upper) =>
            {
                Some(lower)
            }
            (Some(lower), Some(upper)) if type_candidate_subtype(self.graph, &lower, &upper) => {
                Some(upper)
            }
            (Some(lower), Some(upper)) if type_candidate_subtype(self.graph, &upper, &lower) => {
                Some(lower)
            }
            (Some(lower), Some(upper)) if lower == upper => Some(lower),
            (Some(_), Some(_)) if open_shape_candidate.is_some() => open_shape_candidate,
            (Some(lower), Some(upper)) if same_candidate_head(&lower, &upper) => {
                Some(prefer_more_resolved_candidate(lower, upper))
            }
            (Some(lower), Some(upper)) => Err(SpecializeError::ConflictingTypeCandidates {
                slot,
                existing: lower,
                incoming: upper,
            })?,
            (Some(lower), None) => Some(lower),
            (None, Some(_)) if slot_data.kind == TypeSlotKind::Effect => Some(Type::pure_effect()),
            (None, Some(upper)) => Some(upper),
            (None, None) => None,
        };
        self.erase_stack_solution_candidate(candidate)
    }

    pub(super) fn erase_stack_solution_candidate(
        &mut self,
        candidate: Option<Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(candidate) = candidate else {
            return Ok(None);
        };
        self.erase_stack_type_candidate(candidate)
    }

    pub(super) fn erase_stack_type_candidate(
        &mut self,
        candidate: Type,
    ) -> Result<Option<Type>, SpecializeError> {
        match candidate {
            Type::Stack { inner, weight } => {
                let Some(inner) = self.resolve_partial_candidate(&inner, false)? else {
                    return Ok(None);
                };
                let candidate = types::simplify_stack_type(inner, weight);
                if matches!(candidate, Type::Stack { .. }) {
                    Ok(None)
                } else {
                    self.erase_stack_type_candidate(candidate)
                }
            }
            Type::Con { path, args } => {
                let Some(args) = self.erase_stack_type_candidates(args)? else {
                    return Ok(None);
                };
                Ok(Some(Type::Con { path, args }))
            }
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => {
                let Some(arg) = self.erase_stack_type_candidate(*arg)? else {
                    return Ok(None);
                };
                let Some(arg_effect) = self.erase_stack_type_candidate(*arg_effect)? else {
                    return Ok(None);
                };
                let Some(ret_effect) = self.erase_stack_type_candidate(*ret_effect)? else {
                    return Ok(None);
                };
                let Some(ret) = self.erase_stack_type_candidate(*ret)? else {
                    return Ok(None);
                };
                Ok(Some(Type::Fun {
                    arg: Box::new(arg),
                    arg_effect: Box::new(arg_effect),
                    ret_effect: Box::new(ret_effect),
                    ret: Box::new(ret),
                }))
            }
            Type::Thunk { effect, value } => {
                let Some(effect) = self.erase_stack_type_candidate(*effect)? else {
                    return Ok(None);
                };
                let Some(value) = self.erase_stack_type_candidate(*value)? else {
                    return Ok(None);
                };
                Ok(Some(types::runtime_shape(effect, value)))
            }
            Type::Record(fields) => {
                let mut out = Vec::with_capacity(fields.len());
                for field in fields {
                    let Some(value) = self.erase_stack_type_candidate(field.value)? else {
                        return Ok(None);
                    };
                    out.push(TypeField {
                        name: field.name,
                        value,
                        optional: field.optional,
                    });
                }
                Ok(Some(Type::Record(out)))
            }
            Type::PolyVariant(variants) => {
                let mut out = Vec::with_capacity(variants.len());
                for variant in variants {
                    let Some(payloads) = self.erase_stack_type_candidates(variant.payloads)? else {
                        return Ok(None);
                    };
                    out.push(TypeVariant {
                        name: variant.name,
                        payloads,
                    });
                }
                Ok(Some(Type::PolyVariant(out)))
            }
            Type::Tuple(items) => {
                let Some(items) = self.erase_stack_type_candidates(items)? else {
                    return Ok(None);
                };
                Ok(Some(Type::Tuple(items)))
            }
            Type::EffectRow(items) => {
                let Some(items) = self.erase_stack_type_candidates(items)? else {
                    return Ok(None);
                };
                Ok(Some(types::simplify_type(Type::EffectRow(items))))
            }
            Type::Union(left, right) => {
                let left = self.erase_stack_type_candidate(*left)?;
                let right = self.erase_stack_type_candidate(*right)?;
                match (left, right) {
                    (Some(left), Some(right)) => Ok(Some(self.join_explicit_union(left, right)?)),
                    (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                }
            }
            Type::Intersection(left, right) => {
                let left = self.erase_stack_type_candidate(*left)?;
                let right = self.erase_stack_type_candidate(*right)?;
                match (left, right) {
                    (Some(left), Some(right)) => {
                        Ok(Some(self.meet_explicit_intersection(left, right)?))
                    }
                    (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                }
            }
            Type::Any | Type::Never | Type::OpenVar(_) => Ok(Some(candidate)),
        }
    }

    pub(super) fn erase_stack_type_candidates(
        &mut self,
        items: Vec<Type>,
    ) -> Result<Option<Vec<Type>>, SpecializeError> {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            let Some(item) = self.erase_stack_type_candidate(item)? else {
                return Ok(None);
            };
            out.push(item);
        }
        Ok(Some(out))
    }

    pub(super) fn resolve_weight_inert_bound_candidate(
        &mut self,
        bound: &WeightedTypeBound,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(ty) = self.resolve_candidate(&bound.ty)? else {
            return Ok(None);
        };
        if stack_weight_cannot_affect_type(self.graph, &ty) {
            Ok(Some(ty))
        } else {
            Ok(None)
        }
    }

    pub(super) fn join_bounds(
        &mut self,
        slot_kind: TypeSlotKind,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut out = None;
        for bound in bounds {
            let Some(bound) = self.resolve_candidate(bound)? else {
                continue;
            };
            if candidate_has_unresolved_stack(self.graph, slot_kind, &bound) {
                continue;
            }
            let bound = effect_slot_candidate(slot_kind, bound);
            out = Some(match out {
                Some(existing) => join_type_candidates(self.graph, existing, bound)?,
                None => bound,
            });
        }
        Ok(out)
    }

    pub(super) fn meet_bounds(
        &mut self,
        slot_kind: TypeSlotKind,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut out = None;
        for bound in bounds {
            let Some(bound) = self.resolve_candidate(bound)? else {
                continue;
            };
            if candidate_has_unresolved_stack(self.graph, slot_kind, &bound) {
                continue;
            }
            let bound = effect_slot_candidate(slot_kind, bound);
            out = Some(match out {
                Some(existing) => meet_type_candidates(self.graph, existing, bound)?,
                None => bound,
            });
        }
        Ok(out)
    }

    pub(super) fn resolve_candidate(&mut self, ty: &Type) -> Result<Option<Type>, SpecializeError> {
        self.resolve_partial_candidate(ty, false)
    }

    pub(super) fn resolve_partial_candidate(
        &mut self,
        ty: &Type,
        allow_unresolved_leaf: bool,
    ) -> Result<Option<Type>, SpecializeError> {
        match ty {
            Type::Any | Type::Never => Ok(Some(ty.clone())),
            Type::OpenVar(slot) => {
                let Some(solution) = self.solution.slots.get(*slot as usize) else {
                    return Err(SpecializeError::InvalidTypeSlot { slot: *slot });
                };
                let ty = match solution {
                    SlotSolution::Resolved(ty) => ty,
                    SlotSolution::Unknown => {
                        return if allow_unresolved_leaf {
                            Ok(Some(Type::OpenVar(*slot)))
                        } else {
                            Ok(None)
                        };
                    }
                    SlotSolution::Conflicting { existing, incoming } => {
                        return Err(SpecializeError::ConflictingTypeCandidates {
                            slot: *slot,
                            existing: existing.clone(),
                            incoming: incoming.clone(),
                        });
                    }
                };
                if !self.resolving.insert(*slot) {
                    return if allow_unresolved_leaf {
                        Ok(Some(Type::OpenVar(*slot)))
                    } else {
                        Ok(None)
                    };
                }
                let resolved = self.resolve_partial_candidate(ty, allow_unresolved_leaf);
                self.resolving.remove(slot);
                resolved
            }
            Type::Con { path, args } => Ok(Some(Type::Con {
                path: path.clone(),
                args: self.resolve_partial_candidates(args)?,
            })),
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => Ok(Some(Type::Fun {
                arg: Box::new(
                    self.resolve_partial_candidate(arg, true)?
                        .unwrap_or_else(|| arg.as_ref().clone()),
                ),
                arg_effect: Box::new(
                    self.resolve_partial_candidate(arg_effect, true)?
                        .unwrap_or_else(|| arg_effect.as_ref().clone()),
                ),
                ret_effect: Box::new(
                    self.resolve_partial_candidate(ret_effect, true)?
                        .unwrap_or_else(|| ret_effect.as_ref().clone()),
                ),
                ret: Box::new(
                    self.resolve_partial_candidate(ret, true)?
                        .unwrap_or_else(|| ret.as_ref().clone()),
                ),
            })),
            Type::Thunk { effect, value } => Ok(Some(types::runtime_shape(
                self.resolve_partial_candidate(effect, true)?
                    .unwrap_or_else(|| effect.as_ref().clone()),
                self.resolve_partial_candidate(value, true)?
                    .unwrap_or_else(|| value.as_ref().clone()),
            ))),
            Type::Record(fields) => Ok(Some(Type::Record(
                fields
                    .iter()
                    .map(|field| {
                        Ok(TypeField {
                            name: field.name.clone(),
                            value: self
                                .resolve_partial_candidate(&field.value, true)?
                                .unwrap_or_else(|| field.value.clone()),
                            optional: field.optional,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            ))),
            Type::PolyVariant(variants) => Ok(Some(Type::PolyVariant(
                variants
                    .iter()
                    .map(|variant| {
                        Ok(TypeVariant {
                            name: variant.name.clone(),
                            payloads: self.resolve_partial_candidates(&variant.payloads)?,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            ))),
            Type::Tuple(items) => Ok(Some(Type::Tuple(self.resolve_partial_candidates(items)?))),
            Type::EffectRow(items) => self.resolve_effect_row_candidate(items),
            Type::Stack { inner, weight } => {
                let Some(inner) = self.resolve_partial_candidate(inner, allow_unresolved_leaf)?
                else {
                    return Ok(None);
                };
                let candidate = types::simplify_stack_type(inner, weight.clone());
                if type_contains_stack(&candidate) {
                    Ok(None)
                } else {
                    Ok(Some(candidate))
                }
            }
            Type::Union(left, right) => {
                let left = self.resolve_partial_candidate(left, true)?;
                let right = self.resolve_partial_candidate(right, true)?;
                match (left, right) {
                    (Some(left), Some(right)) => Ok(Some(self.join_explicit_union(left, right)?)),
                    (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                }
            }
            Type::Intersection(left, right) => {
                let left = self.resolve_partial_candidate(left, true)?;
                let right = self.resolve_partial_candidate(right, true)?;
                match (left, right) {
                    (Some(left), Some(right)) => {
                        Ok(Some(self.meet_explicit_intersection(left, right)?))
                    }
                    (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                }
            }
        }
    }

    pub(super) fn resolve_partial_candidates(
        &mut self,
        items: &[Type],
    ) -> Result<Vec<Type>, SpecializeError> {
        items
            .iter()
            .map(|item| {
                let fallback = item.clone();
                self.resolve_partial_candidate(item, true)
                    .map(|resolved| resolved.unwrap_or(fallback))
            })
            .collect()
    }

    pub(super) fn resolve_effect_row_candidate(
        &mut self,
        items: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let (items, stack_tail) = match items.last() {
            Some(tail @ Type::Stack { .. }) if type_is_effect_tail_candidate(self.graph, tail) => {
                (&items[..items.len() - 1], Some(tail.clone()))
            }
            _ => (items, None),
        };
        let mut resolved = self.resolve_partial_candidates(items)?;
        if let Some(tail) = stack_tail {
            resolved.push(tail);
        }
        Ok(Some(types::simplify_type(Type::EffectRow(resolved))))
    }

    fn join_explicit_union(&self, left: Type, right: Type) -> Result<Type, SpecializeError> {
        match join_type_candidates(self.graph, left.clone(), right.clone()) {
            Ok(ty) => Ok(ty),
            Err(SpecializeError::ConflictingTypeCandidates { .. }) => Ok(types::simplify_type(
                Type::Union(Box::new(left), Box::new(right)),
            )),
            Err(error) => Err(error),
        }
    }

    fn meet_explicit_intersection(&self, left: Type, right: Type) -> Result<Type, SpecializeError> {
        match meet_type_candidates(self.graph, left.clone(), right.clone()) {
            Ok(ty) => Ok(ty),
            Err(SpecializeError::ConflictingTypeCandidates { .. }) => Ok(types::simplify_type(
                Type::Intersection(Box::new(left), Box::new(right)),
            )),
            Err(error) => Err(error),
        }
    }
}
