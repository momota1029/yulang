use super::*;

impl<'a> SchemeMaterializer<'a> {
    pub(super) fn materialize_pos(
        &self,
        id: PosId,
        context: TypeContext,
    ) -> Result<Type, SpecializeError> {
        Ok(match self.arena.pos(id) {
            Pos::Bot if self.track_empty_bounds => self.materialize_empty_bound(context),
            Pos::Bot => Type::Never,
            Pos::Var(var) => self.materialize_var(*var, context),
            Pos::Con(path, args) => Type::Con {
                path: path.clone(),
                args: self.materialize_con_args(path, args)?,
            },
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.materialize_function_type(
                self.materialize_neg(*arg, TypeContext::Value)?,
                self.materialize_neg(*arg_eff, TypeContext::Effect)?,
                self.materialize_pos(*ret_eff, TypeContext::Effect)?,
                self.materialize_pos(*ret, TypeContext::Value)?,
            ),
            Pos::Record(fields) => Type::Record(self.materialize_fields(
                fields,
                TypeContext::Value,
                Self::materialize_pos,
            )?),
            Pos::RecordTailSpread { fields, tail } => {
                let mut fields =
                    self.materialize_fields(fields, TypeContext::Value, Self::materialize_pos)?;
                if let Type::Record(tail) = self.materialize_pos(*tail, TypeContext::Value)? {
                    fields.extend(tail);
                }
                Type::Record(fields)
            }
            Pos::RecordHeadSpread { tail, fields } => {
                let mut out = match self.materialize_pos(*tail, TypeContext::Value)? {
                    Type::Record(fields) => fields,
                    _ => Vec::new(),
                };
                out.extend(self.materialize_fields(
                    fields,
                    TypeContext::Value,
                    Self::materialize_pos,
                )?);
                Type::Record(out)
            }
            Pos::PolyVariant(variants) => {
                Type::PolyVariant(self.materialize_pos_variants(variants, TypeContext::Value)?)
            }
            Pos::Tuple(items) => Type::Tuple(self.materialize_poss(items, TypeContext::Value)?),
            Pos::Row(items) => Type::EffectRow(self.materialize_poss(items, TypeContext::Effect)?),
            Pos::Stack { inner, weight } => stack_type(
                self.materialize_pos(*inner, context)?,
                self.materialize_stack_weight(weight)?,
            ),
            Pos::NonSubtract(inner, subtract) => stack_type(
                self.materialize_pos(*inner, context)?,
                mono::StackWeight {
                    entries: vec![StackWeightEntry {
                        id: subtract.0,
                        pops: 1,
                        floor: Vec::new(),
                        stack: Vec::new(),
                    }],
                },
            ),
            Pos::Union(left, right) => simplify_union_type(
                self.materialize_pos(*left, context)?,
                self.materialize_pos(*right, context)?,
            ),
        })
    }

    pub(super) fn materialize_neg(
        &self,
        id: NegId,
        context: TypeContext,
    ) -> Result<Type, SpecializeError> {
        Ok(match self.arena.neg(id) {
            Neg::Top if self.track_empty_bounds => self.materialize_empty_bound(context),
            Neg::Top => Type::Any,
            Neg::Bot => Type::Never,
            Neg::Var(var) => self.materialize_var(*var, context),
            Neg::Con(path, args) => Type::Con {
                path: path.clone(),
                args: self.materialize_con_args(path, args)?,
            },
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.materialize_function_type(
                self.materialize_pos(*arg, TypeContext::Value)?,
                self.materialize_pos(*arg_eff, TypeContext::Effect)?,
                self.materialize_neg(*ret_eff, TypeContext::Effect)?,
                self.materialize_neg(*ret, TypeContext::Value)?,
            ),
            Neg::Record(fields) => Type::Record(self.materialize_fields(
                fields,
                TypeContext::Value,
                Self::materialize_neg,
            )?),
            Neg::PolyVariant(variants) => {
                Type::PolyVariant(self.materialize_neg_variants(variants, TypeContext::Value)?)
            }
            Neg::Tuple(items) => Type::Tuple(self.materialize_negs(items, TypeContext::Value)?),
            Neg::Row(items, tail) => {
                let mut items = self.materialize_negs(items, TypeContext::Effect)?;
                let tail = self.materialize_neg(*tail, TypeContext::Effect)?;
                match tail {
                    Type::EffectRow(tail_items) => items.extend(tail_items),
                    Type::Any | Type::Never => {}
                    tail if tail.is_pure_effect() => {}
                    tail => items.push(tail),
                }
                Type::EffectRow(items)
            }
            Neg::Stack { inner, weight } => stack_type(
                self.materialize_neg(*inner, context)?,
                self.materialize_stack_weight(weight)?,
            ),
            Neg::Intersection(left, right) => simplify_intersection_type(
                self.materialize_neg(*left, context)?,
                self.materialize_neg(*right, context)?,
            ),
        })
    }

    pub(super) fn materialize_neu(
        &self,
        id: NeuId,
        context: TypeContext,
    ) -> Result<Type, SpecializeError> {
        Ok(match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                if self.bound_materialization == BoundMaterialization::Fresh
                    && let Some(ty) = self.inline_bound_substitution.get(&id)
                {
                    return Ok(ty.clone());
                }
                let has_lower = !matches!(self.arena.pos(*lower), Pos::Bot);
                let has_upper = !matches!(self.arena.neg(*upper), Neg::Top);
                match (has_lower, has_upper) {
                    (true, true) => simplify_intersection_type(
                        self.materialize_pos(*lower, context)?,
                        self.materialize_neg(*upper, context)?,
                    ),
                    (true, false) => self.materialize_pos(*lower, context)?,
                    (false, true) => self.materialize_neg(*upper, context)?,
                    (false, false) => match context {
                        _ if self.track_empty_bounds => self.materialize_empty_bound(context),
                        TypeContext::Value => Type::unit(),
                        TypeContext::Effect => Type::pure_effect(),
                    },
                }
            }
            Neu::Con(path, args) => Type::Con {
                path: path.clone(),
                args: self.materialize_con_args(path, args)?,
            },
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.materialize_function_type(
                self.materialize_neu(*arg, TypeContext::Value)?,
                self.materialize_neu(*arg_eff, TypeContext::Effect)?,
                self.materialize_neu(*ret_eff, TypeContext::Effect)?,
                self.materialize_neu(*ret, TypeContext::Value)?,
            ),
            Neu::Record(fields) => Type::Record(self.materialize_fields(
                fields,
                TypeContext::Value,
                Self::materialize_neu,
            )?),
            Neu::PolyVariant(variants) => {
                Type::PolyVariant(self.materialize_neu_variants(variants, TypeContext::Value)?)
            }
            Neu::Tuple(items) => Type::Tuple(self.materialize_neus(items, TypeContext::Value)?),
        })
    }

    pub(super) fn materialize_function_type(
        &self,
        arg: Type,
        arg_effect: Type,
        ret_effect: Type,
        ret: Type,
    ) -> Type {
        match self.function_materialization {
            FunctionMaterialization::Runtime => {
                runtime_function_type(arg, arg_effect, ret_effect, ret)
            }
            FunctionMaterialization::Inference => {
                inference_function_type(arg, arg_effect, ret_effect, ret)
            }
        }
    }

    pub(super) fn materialize_var(&self, var: TypeVar, context: TypeContext) -> Type {
        if let Some(ty) = self.substitution.get(&var) {
            return ty.clone();
        }
        if self.quantifiers.contains(&var) {
            return QuantifierKind::from_context(context).default_type();
        }
        Type::OpenVar(var.0)
    }

    pub(super) fn materialize_empty_bound(&self, context: TypeContext) -> Type {
        if context == TypeContext::Effect {
            return Type::pure_effect();
        }
        self.empty_bound_types
            .borrow_mut()
            .pop_front()
            .unwrap_or_else(|| QuantifierKind::from_context(context).default_type())
    }

    pub(super) fn materialize_fields<T>(
        &self,
        fields: &[RecordField<T>],
        context: TypeContext,
        materialize: fn(&Self, T, TypeContext) -> Result<Type, SpecializeError>,
    ) -> Result<Vec<TypeField>, SpecializeError>
    where
        T: Copy,
    {
        fields
            .iter()
            .map(|field| {
                Ok(TypeField {
                    name: field.name.clone(),
                    value: materialize(self, field.value, context)?,
                    optional: field.optional,
                })
            })
            .collect()
    }

    pub(super) fn materialize_con_args(
        &self,
        path: &[String],
        args: &[NeuId],
    ) -> Result<Vec<Type>, SpecializeError> {
        args.iter()
            .enumerate()
            .map(|(index, arg)| self.materialize_neu(*arg, con_arg_context(path, index)))
            .collect()
    }

    pub(super) fn materialize_pos_variants(
        &self,
        variants: &[(String, Vec<PosId>)],
        context: TypeContext,
    ) -> Result<Vec<TypeVariant>, SpecializeError> {
        variants
            .iter()
            .map(|(name, payloads)| {
                Ok(TypeVariant {
                    name: name.clone(),
                    payloads: self.materialize_poss(payloads, context)?,
                })
            })
            .collect()
    }

    pub(super) fn materialize_neg_variants(
        &self,
        variants: &[(String, Vec<NegId>)],
        context: TypeContext,
    ) -> Result<Vec<TypeVariant>, SpecializeError> {
        variants
            .iter()
            .map(|(name, payloads)| {
                Ok(TypeVariant {
                    name: name.clone(),
                    payloads: self.materialize_negs(payloads, context)?,
                })
            })
            .collect()
    }

    pub(super) fn materialize_neu_variants(
        &self,
        variants: &[(String, Vec<NeuId>)],
        context: TypeContext,
    ) -> Result<Vec<TypeVariant>, SpecializeError> {
        variants
            .iter()
            .map(|(name, payloads)| {
                Ok(TypeVariant {
                    name: name.clone(),
                    payloads: self.materialize_neus(payloads, context)?,
                })
            })
            .collect()
    }

    pub(super) fn materialize_poss(
        &self,
        ids: &[PosId],
        context: TypeContext,
    ) -> Result<Vec<Type>, SpecializeError> {
        ids.iter()
            .map(|id| self.materialize_pos(*id, context))
            .collect()
    }

    pub(super) fn materialize_negs(
        &self,
        ids: &[NegId],
        context: TypeContext,
    ) -> Result<Vec<Type>, SpecializeError> {
        ids.iter()
            .map(|id| self.materialize_neg(*id, context))
            .collect()
    }

    pub(super) fn materialize_neus(
        &self,
        ids: &[NeuId],
        context: TypeContext,
    ) -> Result<Vec<Type>, SpecializeError> {
        ids.iter()
            .map(|id| self.materialize_neu(*id, context))
            .collect()
    }

    pub(super) fn materialize_stack_weight(
        &self,
        weight: &StackWeight,
    ) -> Result<mono::StackWeight, SpecializeError> {
        Ok(mono::StackWeight {
            entries: weight
                .entries()
                .iter()
                .map(|entry| {
                    Ok(StackWeightEntry {
                        id: entry.id.0,
                        pops: entry.pops,
                        floor: self.materialize_subtractabilities(&entry.floor)?,
                        stack: self.materialize_subtractabilities(&entry.stack)?,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    pub(super) fn materialize_subtractabilities(
        &self,
        items: &[Subtractability],
    ) -> Result<Vec<EffectFamilies>, SpecializeError> {
        items
            .iter()
            .map(|item| self.materialize_subtractability(item))
            .collect()
    }

    pub(super) fn materialize_subtractability(
        &self,
        item: &Subtractability,
    ) -> Result<EffectFamilies, SpecializeError> {
        Ok(match item {
            Subtractability::Empty => EffectFamilies::Empty,
            Subtractability::All => EffectFamilies::All,
            Subtractability::AllExcept(path, args) => {
                EffectFamilies::AllExcept(vec![self.materialize_effect_family(path, args)?])
            }
            Subtractability::AllExceptMany(families) => EffectFamilies::AllExcept(
                families
                    .iter()
                    .map(|(path, args)| self.materialize_effect_family(path, args))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Subtractability::Set(path, args) => {
                EffectFamilies::Set(vec![self.materialize_effect_family(path, args)?])
            }
            Subtractability::SetMany(families) => EffectFamilies::Set(
                families
                    .iter()
                    .map(|(path, args)| self.materialize_effect_family(path, args))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        })
    }

    pub(super) fn materialize_effect_family(
        &self,
        path: &[String],
        args: &[NeuId],
    ) -> Result<EffectFamily, SpecializeError> {
        Ok(EffectFamily {
            path: path.to_vec(),
            args: self.materialize_neus(args, TypeContext::Value)?,
        })
    }

    pub(super) fn materialize_role_predicates(
        &self,
        scheme: &Scheme,
    ) -> Result<Vec<InstantiatedRolePredicate>, SpecializeError> {
        scheme
            .role_predicates
            .iter()
            .map(|predicate| {
                Ok(InstantiatedRolePredicate {
                    role: predicate.role.clone(),
                    inputs: predicate
                        .inputs
                        .iter()
                        .map(|arg| self.materialize_role_arg(*arg))
                        .collect::<Result<Vec<_>, _>>()?,
                    associated: predicate
                        .associated
                        .iter()
                        .map(|associated| {
                            let arg = self.materialize_role_neu_arg(associated.value)?;
                            Ok(InstantiatedRoleAssociatedType {
                                name: associated.name.clone(),
                                lower: arg.lower,
                                upper: arg.upper,
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                })
            })
            .collect()
    }

    pub(super) fn materialize_recursive_bounds(
        &self,
        scheme: &Scheme,
    ) -> Result<Vec<InstantiatedRecursiveBound>, SpecializeError> {
        scheme
            .recursive_bounds
            .iter()
            .map(|bound| {
                let value = self.materialize_type_var(bound.var);
                let bounds = self.materialize_role_neu_arg(bound.bounds)?;
                Ok(InstantiatedRecursiveBound {
                    value,
                    lower: bounds.lower,
                    upper: bounds.upper,
                })
            })
            .collect()
    }

    pub(super) fn materialize_inline_bounds(
        &self,
    ) -> Result<Vec<InstantiatedRecursiveBound>, SpecializeError> {
        if self.bound_materialization != BoundMaterialization::Fresh {
            return Ok(Vec::new());
        }
        let mut bounds = Vec::new();
        for id in &self.inline_bound_order {
            let Some(value) = self.inline_bound_substitution.get(id).cloned() else {
                continue;
            };
            let Neu::Bounds(lower, upper) = self.arena.neu(*id) else {
                continue;
            };
            let context = self
                .inline_bound_kinds
                .get(id)
                .copied()
                .map(TypeContext::from)
                .unwrap_or(TypeContext::Value);
            bounds.push(InstantiatedRecursiveBound {
                value,
                lower: if matches!(self.arena.pos(*lower), Pos::Bot) {
                    Type::Never
                } else {
                    self.materialize_pos(*lower, context)?
                },
                upper: if matches!(self.arena.neg(*upper), Neg::Top) {
                    Type::Any
                } else {
                    self.materialize_neg(*upper, context)?
                },
            });
        }
        Ok(bounds)
    }

    pub(super) fn materialize_role_arg(
        &self,
        arg: RolePredicateArg,
    ) -> Result<InstantiatedRoleArg, SpecializeError> {
        match arg {
            RolePredicateArg::Covariant(lower) => Ok(InstantiatedRoleArg {
                lower: self.materialize_pos(lower, TypeContext::Value)?,
                upper: Type::Any,
            }),
            RolePredicateArg::Contravariant(upper) => Ok(InstantiatedRoleArg {
                lower: Type::Never,
                upper: self.materialize_neg(upper, TypeContext::Value)?,
            }),
            RolePredicateArg::Invariant(value) => self.materialize_role_neu_arg(value),
        }
    }

    pub(super) fn materialize_role_neu_arg(
        &self,
        id: NeuId,
    ) -> Result<InstantiatedRoleArg, SpecializeError> {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => Ok(InstantiatedRoleArg {
                lower: self.materialize_pos(*lower, TypeContext::Value)?,
                upper: self.materialize_neg(*upper, TypeContext::Value)?,
            }),
            _ => {
                let ty = self.materialize_neu(id, TypeContext::Value)?;
                Ok(InstantiatedRoleArg {
                    lower: ty.clone(),
                    upper: ty,
                })
            }
        }
    }

    pub(super) fn materialize_type_var(&self, var: TypeVar) -> Type {
        self.substitution.get(&var).cloned().unwrap_or_else(|| {
            self.kinds
                .get(&var)
                .copied()
                .unwrap_or(QuantifierKind::Value)
                .default_type()
        })
    }
}
