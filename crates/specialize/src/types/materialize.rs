use super::*;

const MAX_MATERIALIZED_PROVENANCE_PATHS: usize = 256;

impl<'a> SchemeMaterializer<'a> {
    #[allow(dead_code)] // SUBP-F will seed positive TypeGraph roots through this companion.
    pub(super) fn materialize_pos_with_provenance(
        &self,
        id: PosId,
        context: TypeContext,
        sidecar: &SubtypeProvenanceSidecar,
        owner: TypeOccurrenceOwner,
        role: TypeOccurrenceRole,
    ) -> Result<MaterializedTypeWithProvenance, SpecializeError> {
        // Semantic materialization remains the sole source of truth. The adjacent collector below
        // reads only the source poly graph and the frozen sidecar; it cannot affect this result.
        let ty = self.materialize_pos(id, context)?;
        let mut collector = MaterializationProvenanceCollector::new(sidecar, owner, role);
        collector.project_pos(self, id, TypePositionPath::default());
        Ok(MaterializedTypeWithProvenance {
            ty,
            provenance: collector.finish(),
        })
    }

    #[allow(dead_code)] // SUBP-F will seed negative TypeGraph roots through this companion.
    pub(super) fn materialize_neg_with_provenance(
        &self,
        id: NegId,
        context: TypeContext,
        sidecar: &SubtypeProvenanceSidecar,
        owner: TypeOccurrenceOwner,
        role: TypeOccurrenceRole,
    ) -> Result<MaterializedTypeWithProvenance, SpecializeError> {
        let ty = self.materialize_neg(id, context)?;
        let mut collector = MaterializationProvenanceCollector::new(sidecar, owner, role);
        collector.project_neg(self, id, TypePositionPath::default());
        Ok(MaterializedTypeWithProvenance {
            ty,
            provenance: collector.finish(),
        })
    }

    #[allow(dead_code)] // SUBP-F will seed invariant TypeGraph roots through this companion.
    pub(super) fn materialize_neu_with_provenance(
        &self,
        id: NeuId,
        context: TypeContext,
        sidecar: &SubtypeProvenanceSidecar,
        owner: TypeOccurrenceOwner,
        role: TypeOccurrenceRole,
    ) -> Result<MaterializedTypeWithProvenance, SpecializeError> {
        let ty = self.materialize_neu(id, context)?;
        let mut collector = MaterializationProvenanceCollector::new(sidecar, owner, role);
        collector.project_neu(self, id, TypePositionPath::default());
        Ok(MaterializedTypeWithProvenance {
            ty,
            provenance: collector.finish(),
        })
    }

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
                self.materialize_neg_function_arg_effect(*arg_eff)?,
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
            Pos::NonSubtract(inner, weight) => stack_type(
                self.materialize_pos(*inner, context)?,
                self.materialize_stack_weight(weight)?,
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

    fn materialize_neg_function_arg_effect(&self, id: NegId) -> Result<Type, SpecializeError> {
        match self.arena.neg(id) {
            Neg::Top => Ok(Type::Any),
            _ => self.materialize_neg(id, TypeContext::Effect),
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
            self.kind_for(var)
                .unwrap_or(QuantifierKind::Value)
                .default_type()
        })
    }
}

struct MaterializationProvenanceCollector<'a> {
    sidecar: &'a SubtypeProvenanceSidecar,
    owner: TypeOccurrenceOwner,
    role: TypeOccurrenceRole,
    positions: Vec<MaterializedPositionProvenance>,
    completeness: ProvenanceCompleteness,
    exhausted: bool,
}

impl<'a> MaterializationProvenanceCollector<'a> {
    fn new(
        sidecar: &'a SubtypeProvenanceSidecar,
        owner: TypeOccurrenceOwner,
        role: TypeOccurrenceRole,
    ) -> Self {
        Self {
            sidecar,
            owner,
            role,
            positions: Vec::new(),
            completeness: ProvenanceCompleteness::Complete,
            exhausted: false,
        }
    }

    fn finish(self) -> MaterializedTypeProvenance {
        MaterializedTypeProvenance {
            positions: self.positions,
            completeness: self.completeness,
        }
    }

    fn record_owned_path(&mut self, path: &TypePositionPath) {
        let key = poly::provenance::TypeOccurrenceKey {
            owner: self.owner,
            role: self.role,
            path: path.clone(),
        };
        let Some(occurrence) = self.sidecar.occurrences.get(&key) else {
            return;
        };
        self.insert_or_merge(path, &occurrence.anchors, occurrence.completeness);
    }

    fn mark_incomplete(&mut self, path: &TypePositionPath) {
        self.completeness = ProvenanceCompleteness::Incomplete;
        self.insert_or_merge(path, &[], ProvenanceCompleteness::Incomplete);
    }

    fn insert_or_merge(
        &mut self,
        path: &TypePositionPath,
        anchors: &[ProvenanceAnchor],
        completeness: ProvenanceCompleteness,
    ) {
        if let Some(position) = self.positions.iter_mut().find(|item| item.path == *path) {
            for anchor in anchors {
                if !position.anchors.contains(anchor) {
                    position.anchors.push(*anchor);
                }
            }
            if completeness == ProvenanceCompleteness::Incomplete {
                position.completeness = ProvenanceCompleteness::Incomplete;
                self.completeness = ProvenanceCompleteness::Incomplete;
            }
            return;
        }
        if self.positions.len() >= MAX_MATERIALIZED_PROVENANCE_PATHS {
            self.completeness = ProvenanceCompleteness::Incomplete;
            self.exhausted = true;
            return;
        }
        if completeness == ProvenanceCompleteness::Incomplete {
            self.completeness = ProvenanceCompleteness::Incomplete;
        }
        self.positions.push(MaterializedPositionProvenance {
            path: path.clone(),
            anchors: anchors.to_vec(),
            completeness,
        });
    }

    fn project_pos(
        &mut self,
        materializer: &SchemeMaterializer<'_>,
        id: PosId,
        path: TypePositionPath,
    ) {
        if self.exhausted {
            return;
        }
        self.record_owned_path(&path);
        match materializer.arena.pos(id) {
            Pos::Bot if materializer.track_empty_bounds => self.mark_incomplete(&path),
            Pos::Var(var) if materializer.substitution.contains_key(var) => {
                self.mark_incomplete(&path)
            }
            Pos::Con(_, args) => self.project_neu_args(materializer, args, &path),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                if materializer.function_materialization == FunctionMaterialization::Runtime {
                    self.mark_incomplete(&path);
                } else {
                    self.project_neg(
                        materializer,
                        *arg,
                        child_path(&path, poly::provenance::TypePositionStep::FunctionArgument),
                    );
                    self.project_neg(
                        materializer,
                        *arg_eff,
                        child_path(
                            &path,
                            poly::provenance::TypePositionStep::FunctionArgumentEffect,
                        ),
                    );
                    self.project_pos(
                        materializer,
                        *ret_eff,
                        child_path(
                            &path,
                            poly::provenance::TypePositionStep::FunctionReturnEffect,
                        ),
                    );
                    self.project_pos(
                        materializer,
                        *ret,
                        child_path(&path, poly::provenance::TypePositionStep::FunctionReturn),
                    );
                }
            }
            Pos::Record(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    self.project_pos(materializer, field.value, record_field_path(&path, index));
                }
            }
            Pos::PolyVariant(items) => {
                for (item, (_, payloads)) in items.iter().enumerate() {
                    for (payload, value) in payloads.iter().enumerate() {
                        self.project_pos(
                            materializer,
                            *value,
                            variant_payload_path(&path, item, payload),
                        );
                    }
                }
            }
            Pos::Tuple(items) => {
                for (index, value) in items.iter().enumerate() {
                    self.project_pos(materializer, *value, tuple_path(&path, index));
                }
            }
            Pos::Row(items) => self.project_pos_row(materializer, items, &path),
            Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::Stack { .. }
            | Pos::NonSubtract(..)
            | Pos::Union(..) => self.mark_incomplete(&path),
            Pos::Bot | Pos::Var(_) => {}
        }
    }

    fn project_neg(
        &mut self,
        materializer: &SchemeMaterializer<'_>,
        id: NegId,
        path: TypePositionPath,
    ) {
        if self.exhausted {
            return;
        }
        self.record_owned_path(&path);
        match materializer.arena.neg(id) {
            Neg::Top if materializer.track_empty_bounds => self.mark_incomplete(&path),
            Neg::Var(var) if materializer.substitution.contains_key(var) => {
                self.mark_incomplete(&path)
            }
            Neg::Con(_, args) => self.project_neu_args(materializer, args, &path),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                if materializer.function_materialization == FunctionMaterialization::Runtime {
                    self.mark_incomplete(&path);
                } else {
                    self.project_pos(
                        materializer,
                        *arg,
                        child_path(&path, poly::provenance::TypePositionStep::FunctionArgument),
                    );
                    self.project_pos(
                        materializer,
                        *arg_eff,
                        child_path(
                            &path,
                            poly::provenance::TypePositionStep::FunctionArgumentEffect,
                        ),
                    );
                    self.project_neg(
                        materializer,
                        *ret_eff,
                        child_path(
                            &path,
                            poly::provenance::TypePositionStep::FunctionReturnEffect,
                        ),
                    );
                    self.project_neg(
                        materializer,
                        *ret,
                        child_path(&path, poly::provenance::TypePositionStep::FunctionReturn),
                    );
                }
            }
            Neg::Record(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    self.project_neg(materializer, field.value, record_field_path(&path, index));
                }
            }
            Neg::PolyVariant(items) => {
                for (item, (_, payloads)) in items.iter().enumerate() {
                    for (payload, value) in payloads.iter().enumerate() {
                        self.project_neg(
                            materializer,
                            *value,
                            variant_payload_path(&path, item, payload),
                        );
                    }
                }
            }
            Neg::Tuple(items) => {
                for (index, value) in items.iter().enumerate() {
                    self.project_neg(materializer, *value, tuple_path(&path, index));
                }
            }
            Neg::Row(items, tail) => {
                for (item, value) in items.iter().enumerate() {
                    self.project_neg_row_item(materializer, *value, item, &path);
                }
                self.project_neg(
                    materializer,
                    *tail,
                    child_path(&path, poly::provenance::TypePositionStep::RowTail),
                );
            }
            Neg::Stack { .. } | Neg::Intersection(..) => self.mark_incomplete(&path),
            Neg::Top | Neg::Bot | Neg::Var(_) => {}
        }
    }

    fn project_neu(
        &mut self,
        materializer: &SchemeMaterializer<'_>,
        id: NeuId,
        path: TypePositionPath,
    ) {
        if self.exhausted {
            return;
        }
        self.record_owned_path(&path);
        match materializer.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                if materializer.inline_bound_substitution.contains_key(&id) {
                    self.mark_incomplete(&path);
                    return;
                }
                let has_lower = !matches!(materializer.arena.pos(*lower), Pos::Bot);
                let has_upper = !matches!(materializer.arena.neg(*upper), Neg::Top);
                match (has_lower, has_upper) {
                    (true, false) => self.project_pos(materializer, *lower, path),
                    (false, true) => self.project_neg(materializer, *upper, path),
                    _ => self.mark_incomplete(&path),
                }
            }
            Neu::Con(_, args) => self.project_neu_args(materializer, args, &path),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                if materializer.function_materialization == FunctionMaterialization::Runtime {
                    self.mark_incomplete(&path);
                } else {
                    self.project_neu(
                        materializer,
                        *arg,
                        child_path(&path, poly::provenance::TypePositionStep::FunctionArgument),
                    );
                    self.project_neu(
                        materializer,
                        *arg_eff,
                        child_path(
                            &path,
                            poly::provenance::TypePositionStep::FunctionArgumentEffect,
                        ),
                    );
                    self.project_neu(
                        materializer,
                        *ret_eff,
                        child_path(
                            &path,
                            poly::provenance::TypePositionStep::FunctionReturnEffect,
                        ),
                    );
                    self.project_neu(
                        materializer,
                        *ret,
                        child_path(&path, poly::provenance::TypePositionStep::FunctionReturn),
                    );
                }
            }
            Neu::Record(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    self.project_neu(materializer, field.value, record_field_path(&path, index));
                }
            }
            Neu::PolyVariant(items) => {
                for (item, (_, payloads)) in items.iter().enumerate() {
                    for (payload, value) in payloads.iter().enumerate() {
                        self.project_neu(
                            materializer,
                            *value,
                            variant_payload_path(&path, item, payload),
                        );
                    }
                }
            }
            Neu::Tuple(items) => {
                for (index, value) in items.iter().enumerate() {
                    self.project_neu(materializer, *value, tuple_path(&path, index));
                }
            }
        }
    }

    fn project_neu_args(
        &mut self,
        materializer: &SchemeMaterializer<'_>,
        args: &[NeuId],
        path: &TypePositionPath,
    ) {
        for (argument, value) in args.iter().enumerate() {
            let step = poly::provenance::TypePositionStep::ConstructorArgument {
                alternative: poly::provenance::TypePositionIndex::from_usize(0),
                argument: poly::provenance::TypePositionIndex::from_usize(argument),
            };
            self.project_neu(materializer, *value, child_path(path, step));
        }
    }

    fn project_pos_row(
        &mut self,
        materializer: &SchemeMaterializer<'_>,
        items: &[PosId],
        path: &TypePositionPath,
    ) {
        for (item, value) in items.iter().enumerate() {
            let Pos::Con(_, args) = materializer.arena.pos(*value) else {
                self.mark_incomplete(path);
                continue;
            };
            for (argument, value) in args.iter().enumerate() {
                self.project_neu(
                    materializer,
                    *value,
                    row_item_argument_path(path, item, argument),
                );
            }
        }
    }

    fn project_neg_row_item(
        &mut self,
        materializer: &SchemeMaterializer<'_>,
        value: NegId,
        item: usize,
        path: &TypePositionPath,
    ) {
        let Neg::Con(_, args) = materializer.arena.neg(value) else {
            self.mark_incomplete(path);
            return;
        };
        for (argument, value) in args.iter().enumerate() {
            self.project_neu(
                materializer,
                *value,
                row_item_argument_path(path, item, argument),
            );
        }
    }
}

fn child_path(
    path: &TypePositionPath,
    step: poly::provenance::TypePositionStep,
) -> TypePositionPath {
    let mut out = path.clone();
    out.push(step);
    out
}

fn tuple_path(path: &TypePositionPath, index: usize) -> TypePositionPath {
    child_path(
        path,
        poly::provenance::TypePositionStep::TupleElement(
            poly::provenance::TypePositionIndex::from_usize(index),
        ),
    )
}

fn record_field_path(path: &TypePositionPath, field: usize) -> TypePositionPath {
    child_path(
        path,
        poly::provenance::TypePositionStep::RecordField {
            alternative: poly::provenance::TypePositionIndex::from_usize(0),
            field: poly::provenance::TypePositionIndex::from_usize(field),
        },
    )
}

fn variant_payload_path(path: &TypePositionPath, item: usize, payload: usize) -> TypePositionPath {
    child_path(
        path,
        poly::provenance::TypePositionStep::VariantPayload {
            alternative: poly::provenance::TypePositionIndex::from_usize(0),
            item: poly::provenance::TypePositionIndex::from_usize(item),
            payload: poly::provenance::TypePositionIndex::from_usize(payload),
        },
    )
}

fn row_item_argument_path(
    path: &TypePositionPath,
    item: usize,
    argument: usize,
) -> TypePositionPath {
    child_path(
        path,
        poly::provenance::TypePositionStep::RowItemArgument {
            item: poly::provenance::TypePositionIndex::from_usize(item),
            argument: poly::provenance::TypePositionIndex::from_usize(argument),
        },
    )
}
