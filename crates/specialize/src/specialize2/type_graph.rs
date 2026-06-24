use super::*;

mod bounds;
mod effect_rows;

impl<'a> TypeGraph<'a> {
    pub(super) fn new(arena: &'a poly_expr::Arena) -> Self {
        Self {
            arena,
            effect_family_paths: effect_family_paths(arena),
            slots: Vec::new(),
            pending: VecDeque::new(),
            queued_constraints: HashSet::new(),
            row_residuals: HashMap::new(),
            closed_effect_subtraction_consumers: HashSet::new(),
            role_demands: Vec::new(),
        }
    }

    pub(super) fn is_effect_family_path(&self, path: &[String]) -> bool {
        self.effect_family_paths
            .iter()
            .any(|family| effect_paths_same_family(family, path))
    }

    pub(super) fn fresh_value(&mut self) -> Type {
        self.fresh_slot(TypeSlotKind::Value)
    }

    pub(super) fn fresh_effect(&mut self) -> Type {
        self.fresh_slot(TypeSlotKind::Effect)
    }

    pub(super) fn fresh_slot(&mut self, kind: TypeSlotKind) -> Type {
        let id = self.slots.len() as u32;
        self.slots.push(TypeSlot::new(kind));
        Type::OpenVar(id)
    }

    pub(super) fn constrain_exact(
        &mut self,
        left: Type,
        right: Type,
    ) -> Result<(), SpecializeError> {
        self.constrain_subtype(left.clone(), right.clone())?;
        self.constrain_subtype(right, left)
    }

    pub(super) fn constrain_subtype(
        &mut self,
        lower: Type,
        upper: Type,
    ) -> Result<(), SpecializeError> {
        self.constrain_weighted_subtype(lower, empty_stack_weight(), upper, empty_stack_weight())
    }

    pub(super) fn constrain_weighted_subtype(
        &mut self,
        lower: Type,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        let (lower_weight, upper_weight) = if lower_weight == upper_weight {
            (empty_stack_weight(), empty_stack_weight())
        } else {
            (lower_weight, upper_weight)
        };
        if lower != upper {
            let constraint = SubtypeConstraint {
                lower,
                lower_weight,
                upper,
                upper_weight,
            };
            if self.queued_constraints.insert(constraint.clone()) {
                self.pending.push_back(constraint);
            }
        }
        Ok(())
    }

    pub(super) fn add_role_demands(
        &mut self,
        demands: impl IntoIterator<Item = types::InstantiatedRolePredicate>,
    ) {
        self.role_demands.extend(demands);
    }

    pub(super) fn constrain_recursive_bounds(
        &mut self,
        bounds: Vec<types::InstantiatedRecursiveBound>,
    ) -> Result<(), SpecializeError> {
        for bound in bounds {
            self.constrain_subtype(bound.lower, bound.value.clone())?;
            self.constrain_subtype(bound.value, bound.upper)?;
        }
        Ok(())
    }

    pub(super) fn solve_role_demands(&mut self) -> Result<(), SpecializeError> {
        let mut applied = HashSet::new();
        loop {
            self.solve_constraints()?;
            let solution = self.solve_slots()?;
            let demands = self.role_demands.clone();
            let mut progressed = false;
            for demand in demands {
                if applied.contains(&demand) {
                    continue;
                }
                let input_types = {
                    let mut resolver = TypeResolver::new(self, &solution);
                    resolve_role_input_types(&mut resolver, &demand)?
                };
                let Some(input_types) = input_types else {
                    continue;
                };
                let applications = self
                    .arena
                    .role_impls
                    .candidates(&demand.role)
                    .iter()
                    .filter_map(|candidate| {
                        roles::candidate_application(
                            &self.arena.typ,
                            &demand,
                            candidate,
                            &input_types,
                        )
                    })
                    .collect::<Vec<_>>();
                let [application] = applications.as_slice() else {
                    continue;
                };
                let associated = application.associated.clone();
                let prerequisites = application.prerequisites.clone();
                for (lower, candidate, upper) in associated {
                    self.constrain_subtype(lower, candidate.clone())?;
                    self.constrain_subtype(candidate, upper)?;
                }
                self.add_role_demands(prerequisites);
                applied.insert(demand);
                progressed = true;
            }
            if !progressed {
                self.solve_constraints()?;
                self.close_pure_effect_subtraction_tails_until_stable()?;
                return Ok(());
            }
        }
    }

    pub(super) fn solve_constraints(&mut self) -> Result<(), SpecializeError> {
        while let Some(constraint) = self.pending.pop_front() {
            self.process_subtype(
                constraint.lower,
                constraint.lower_weight,
                constraint.upper,
                constraint.upper_weight,
            )?;
        }
        Ok(())
    }

    pub(super) fn close_pure_effect_subtraction_tails_until_stable(
        &mut self,
    ) -> Result<(), SpecializeError> {
        loop {
            while let Some(constraint) = self.pending.pop_front() {
                self.process_subtype(
                    constraint.lower,
                    constraint.lower_weight,
                    constraint.upper,
                    constraint.upper_weight,
                )?;
            }
            if !self.close_pure_effect_subtraction_tails()? {
                return Ok(());
            }
        }
    }

    pub(super) fn process_subtype(
        &mut self,
        lower: Type,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        let (lower, lower_weight) = peel_stack_weight(lower, lower_weight);
        let (upper, upper_weight) = peel_stack_weight(upper, upper_weight);
        let unweighted =
            stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight);
        if lower == upper && unweighted {
            return Ok(());
        }
        if unweighted && self.effect_row_lower_returns_to_same_tail(&lower, &upper) {
            return Ok(());
        }
        match (lower, upper) {
            (Type::Never, _) | (_, Type::Any) => Ok(()),
            (Type::OpenVar(lower), Type::OpenVar(upper)) if unweighted => {
                self.add_edge(lower, upper)
            }
            (Type::OpenVar(lower), Type::OpenVar(upper)) => {
                self.add_weighted_edge(lower, upper, lower_weight, upper_weight)
            }
            (Type::Union(left, right), upper) => {
                self.constrain_weighted_subtype(
                    *left,
                    lower_weight.clone(),
                    upper.clone(),
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(*right, lower_weight, upper, upper_weight)
            }
            (lower, Type::Intersection(left, right)) => {
                self.constrain_weighted_subtype(
                    lower.clone(),
                    lower_weight.clone(),
                    *left,
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(lower, lower_weight, *right, upper_weight)
            }
            (Type::OpenVar(slot), upper) => {
                self.add_upper_weighted(slot, lower_weight, upper, upper_weight)
            }
            (lower, Type::OpenVar(slot)) => {
                self.add_lower_weighted(slot, lower, lower_weight, upper_weight)
            }
            (
                Type::Fun {
                    arg: lower_arg,
                    arg_effect: lower_arg_eff,
                    ret_effect: lower_ret_eff,
                    ret: lower_ret,
                },
                Type::Fun {
                    arg: upper_arg,
                    arg_effect: upper_arg_eff,
                    ret_effect: upper_ret_eff,
                    ret: upper_ret,
                },
            ) => {
                let (lower_arg, lower_arg_eff) =
                    split_declared_runtime_shape(*lower_arg, *lower_arg_eff);
                let (upper_arg, upper_arg_eff) =
                    split_declared_runtime_shape(*upper_arg, *upper_arg_eff);
                let (lower_ret, lower_ret_eff) =
                    split_declared_runtime_shape(*lower_ret, *lower_ret_eff);
                let (upper_ret, upper_ret_eff) =
                    split_declared_runtime_shape(*upper_ret, *upper_ret_eff);
                self.constrain_weighted_subtype(
                    upper_arg,
                    upper_weight.clone(),
                    lower_arg,
                    lower_weight.clone(),
                )?;
                self.constrain_weighted_subtype(
                    upper_arg_eff,
                    upper_weight.clone(),
                    lower_arg_eff,
                    lower_weight.clone(),
                )?;
                self.constrain_weighted_subtype(
                    lower_ret_eff,
                    lower_weight.clone(),
                    upper_ret_eff,
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(lower_ret, lower_weight, upper_ret, upper_weight)
            }
            (
                Type::Thunk {
                    effect: lower_effect,
                    value: lower_value,
                },
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) => {
                self.constrain_weighted_subtype(
                    *lower_effect,
                    lower_weight.clone(),
                    *upper_effect,
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(
                    *lower_value,
                    lower_weight,
                    *upper_value,
                    upper_weight,
                )
            }
            (
                lower,
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) => {
                self.constrain_weighted_subtype(
                    lower,
                    lower_weight.clone(),
                    *upper_value,
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(
                    Type::pure_effect(),
                    lower_weight,
                    *upper_effect,
                    upper_weight,
                )
            }
            (
                Type::Thunk {
                    value: lower_value, ..
                },
                upper,
            ) => self.constrain_weighted_subtype(*lower_value, lower_weight, upper, upper_weight),
            (
                Type::Con {
                    path: lower_path,
                    args: lower_args,
                },
                Type::Con {
                    path: upper_path,
                    args: upper_args,
                },
            ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
                if !unweighted
                    && self.effect_family_item_blocked_by_weight(
                        &lower_path,
                        &lower_args,
                        &lower_weight,
                        &upper_weight,
                    )
                {
                    return Ok(());
                }
                for (lower, upper) in lower_args.into_iter().zip(upper_args) {
                    self.constrain_weighted_subtype(
                        lower.clone(),
                        lower_weight.clone(),
                        upper.clone(),
                        upper_weight.clone(),
                    )?;
                    self.constrain_weighted_subtype(
                        upper,
                        upper_weight.clone(),
                        lower,
                        lower_weight.clone(),
                    )?;
                }
                Ok(())
            }
            (
                Type::Con {
                    path: lower_path,
                    args: lower_args,
                },
                Type::Con {
                    path: upper_path,
                    args: upper_args,
                },
            ) => {
                if !unweighted {
                    return Ok(());
                }
                let lower_ty = Type::Con {
                    path: lower_path.clone(),
                    args: lower_args,
                };
                let upper_ty = Type::Con {
                    path: upper_path.clone(),
                    args: upper_args,
                };
                self.constrain_direct_cast(&lower_path, &upper_path, lower_ty, upper_ty)
            }
            (Type::Tuple(lower_items), Type::Tuple(upper_items))
                if lower_items.len() == upper_items.len() =>
            {
                for (lower, upper) in lower_items.into_iter().zip(upper_items) {
                    self.constrain_weighted_subtype(
                        lower,
                        lower_weight.clone(),
                        upper,
                        upper_weight.clone(),
                    )?;
                }
                Ok(())
            }
            (Type::Tuple(lower_items), Type::Tuple(upper_items)) => {
                unsatisfied_subtype(Type::Tuple(lower_items), Type::Tuple(upper_items))
            }
            (Type::Record(lower_fields), Type::Record(upper_fields)) => {
                let missing_required_field = upper_fields.iter().any(|upper_field| {
                    !upper_field.optional
                        && record_field_type(&lower_fields, &upper_field.name).is_none()
                });
                if missing_required_field {
                    return unsatisfied_subtype(
                        Type::Record(lower_fields),
                        Type::Record(upper_fields),
                    );
                }
                for upper_field in upper_fields {
                    if let Some(lower_field) = record_field_type(&lower_fields, &upper_field.name) {
                        self.constrain_weighted_subtype(
                            lower_field.value.clone(),
                            lower_weight.clone(),
                            upper_field.value,
                            upper_weight.clone(),
                        )?;
                    }
                }
                Ok(())
            }
            (Type::PolyVariant(lower_variants), Type::PolyVariant(upper_variants)) => {
                if lower_variants
                    .iter()
                    .any(|lower_variant| matching_variant(&upper_variants, lower_variant).is_none())
                {
                    return unsatisfied_subtype(
                        Type::PolyVariant(lower_variants),
                        Type::PolyVariant(upper_variants),
                    );
                }
                for lower_variant in lower_variants {
                    let upper_variant = matching_variant(&upper_variants, &lower_variant)
                        .expect("poly variant mismatch checked above");
                    for (lower, upper) in lower_variant
                        .payloads
                        .into_iter()
                        .zip(upper_variant.payloads.iter().cloned())
                    {
                        self.constrain_weighted_subtype(
                            lower,
                            lower_weight.clone(),
                            upper,
                            upper_weight.clone(),
                        )?;
                    }
                }
                Ok(())
            }
            (Type::EffectRow(lower_items), Type::EffectRow(upper_items)) => self
                .constrain_effect_rows_weighted(
                    lower_items,
                    lower_weight,
                    upper_items,
                    upper_weight,
                ),
            _ => Ok(()),
        }
    }

    pub(super) fn effect_row_lower_returns_to_same_tail(&self, lower: &Type, upper: &Type) -> bool {
        let (Type::EffectRow(items), Type::OpenVar(upper)) = (lower, upper) else {
            return false;
        };
        let Some(Type::OpenVar(tail)) = items.last() else {
            return false;
        };
        tail == upper
            && self
                .slots
                .get(*tail as usize)
                .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
    }

    pub(super) fn constrain_direct_cast(
        &mut self,
        source: &[String],
        target: &[String],
        lower: Type,
        upper: Type,
    ) -> Result<(), SpecializeError> {
        let candidates = self
            .arena
            .cast_rules
            .iter()
            .filter(|rule| rule.source == source && rule.target == target)
            .cloned()
            .collect::<Vec<_>>();
        for candidate in candidates {
            let predicate = self.instantiate_cast_scheme(candidate.def, &candidate.scheme)?;
            self.constrain_subtype(
                predicate,
                types::pure_function_type(lower.clone(), upper.clone()),
            )?;
        }
        Ok(())
    }

    pub(super) fn instantiate_cast_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let instantiated = types::instantiate_principal_scheme_for_inference_with_fresh_and_roles(
            self.arena,
            def,
            scheme,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.fresh_value(),
                types::SchemeQuantifierKind::Effect => self.fresh_effect(),
            },
        )?;
        self.add_role_demands(instantiated.role_predicates);
        self.constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }
}

fn unsatisfied_subtype(lower: Type, upper: Type) -> Result<(), SpecializeError> {
    Err(SpecializeError::UnsatisfiedSubtype { lower, upper })
}
