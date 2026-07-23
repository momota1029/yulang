use super::*;

mod bounds;
mod effect_rows;

const MAX_SUBTYPE_PROVENANCE_RECORDS: usize = 16_384;
const MAX_INCOMING_PROVENANCE_PER_RECORD: usize = 64;
const MAX_SHADOW_SUBTYPE_FAILURES: usize = 256;
const MAX_MATERIALIZED_POSITIONS_PER_RECORD: usize = 256;
const MAX_ANCHORS_PER_MATERIALIZED_POSITION: usize = 64;

#[cfg(test)]
std::thread_local! {
    static SHADOW_SUBTYPE_FAILURE_CAPTURE: std::cell::RefCell<
        Option<Vec<SubtypeFailureProvenance>>,
    > = const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
pub(super) fn capture_shadow_subtype_failures<T>(
    f: impl FnOnce() -> T,
) -> (T, Vec<SubtypeFailureProvenance>) {
    SHADOW_SUBTYPE_FAILURE_CAPTURE.with(|capture| {
        let mut capture = capture.borrow_mut();
        assert!(
            capture.is_none(),
            "shadow subtype failure capture cannot be nested"
        );
        *capture = Some(Vec::new());
    });
    let guard = ShadowSubtypeFailureCaptureGuard;
    let result = f();
    let failures = SHADOW_SUBTYPE_FAILURE_CAPTURE.with(|capture| {
        capture
            .borrow_mut()
            .take()
            .expect("shadow subtype failure capture remains active")
    });
    drop(guard);
    (result, failures)
}

#[cfg(test)]
struct ShadowSubtypeFailureCaptureGuard;

#[cfg(test)]
impl Drop for ShadowSubtypeFailureCaptureGuard {
    fn drop(&mut self) {
        SHADOW_SUBTYPE_FAILURE_CAPTURE.with(|capture| {
            capture.borrow_mut().take();
        });
    }
}

#[cfg(test)]
fn capture_shadow_subtype_failure(failure: &SubtypeFailureProvenance) {
    SHADOW_SUBTYPE_FAILURE_CAPTURE.with(|capture| {
        if let Some(failures) = capture.borrow_mut().as_mut() {
            failures.push(failure.clone());
        }
    });
}

impl<'a> TypeGraph<'a> {
    pub(super) fn new(arena: &'a poly_expr::Arena) -> Self {
        Self {
            arena,
            effect_family_paths: effect_family_paths(arena),
            slots: Vec::new(),
            pending: VecDeque::new(),
            queued_constraints: HashSet::new(),
            subtype_provenance_records: Vec::new(),
            subtype_provenance_by_key: HashMap::new(),
            subtype_position_provenance: Vec::new(),
            shadow_subtype_failures: Vec::new(),
            subtype_provenance_metrics: SpecializeSubtypeProvenanceMetrics::default(),
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

    pub(super) fn constrain_materialized_subtype(
        &mut self,
        lower: types::MaterializedTypeWithProvenance,
        upper: types::MaterializedTypeWithProvenance,
    ) -> Result<(), SpecializeError> {
        let lower_positions = lower.provenance;
        let upper_positions = upper.provenance;
        let completeness =
            compose_completeness(lower_positions.completeness, upper_positions.completeness);
        let lower_anchors = anchors_at_root(&lower_positions);
        let upper_anchors = anchors_at_root(&upper_positions);
        self.intern_weighted_subtype(
            lower.ty,
            empty_stack_weight(),
            upper.ty,
            empty_stack_weight(),
            SpecializeProvenanceDerivation::Root {
                lower: lower_anchors,
                upper: upper_anchors,
            },
            SubtypePositionProvenance {
                lower: lower_positions,
                upper: upper_positions,
            },
            completeness,
        );
        Ok(())
    }

    pub(super) fn constrain_weighted_subtype(
        &mut self,
        lower: Type,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        self.intern_weighted_subtype(
            lower,
            lower_weight,
            upper,
            upper_weight,
            SpecializeProvenanceDerivation::Root {
                lower: Vec::new(),
                upper: Vec::new(),
            },
            incomplete_positions(),
            ProvenanceCompleteness::Incomplete,
        );
        Ok(())
    }

    fn intern_weighted_subtype(
        &mut self,
        lower: Type,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
        derivation: SpecializeProvenanceDerivation,
        positions: SubtypePositionProvenance,
        completeness: ProvenanceCompleteness,
    ) -> Option<SpecializeSubtypeProvenanceRecordId> {
        let (lower_weight, upper_weight) = if lower_weight == upper_weight {
            (empty_stack_weight(), empty_stack_weight())
        } else {
            (lower_weight, upper_weight)
        };
        if lower == upper {
            return None;
        }
        let constraint = SubtypeConstraint {
            lower,
            lower_weight,
            upper,
            upper_weight,
        };
        let record =
            self.intern_provenance_record(constraint.clone(), derivation, positions, completeness);
        if self.queued_constraints.insert(constraint.clone()) {
            self.pending.push_back(constraint);
            self.subtype_provenance_metrics.semantic_enqueues += 1;
        }
        record
    }

    fn intern_provenance_record(
        &mut self,
        semantic_key: SubtypeConstraint,
        derivation: SpecializeProvenanceDerivation,
        positions: SubtypePositionProvenance,
        completeness: ProvenanceCompleteness,
    ) -> Option<SpecializeSubtypeProvenanceRecordId> {
        self.subtype_provenance_metrics.incoming_considered += 1;
        if let Some(id) = self.subtype_provenance_by_key.get(&semantic_key).copied() {
            self.merge_positions(id, positions);
            let record = &mut self.subtype_provenance_records[id.index()];
            record.completeness = compose_completeness(record.completeness, completeness);
            if record.incoming.contains(&derivation) {
                self.subtype_provenance_metrics.incoming_deduplicated += 1;
            } else if record.incoming.len() < MAX_INCOMING_PROVENANCE_PER_RECORD {
                record.incoming.push(derivation);
                self.subtype_provenance_metrics.incoming_inserted += 1;
            } else {
                record.completeness = ProvenanceCompleteness::Incomplete;
                self.subtype_provenance_metrics.budget_exhaustions += 1;
            }
            return Some(id);
        }
        if self.subtype_provenance_records.len() >= MAX_SUBTYPE_PROVENANCE_RECORDS {
            self.subtype_provenance_metrics.budget_exhaustions += 1;
            return None;
        }
        let id = SpecializeSubtypeProvenanceRecordId(
            u32::try_from(self.subtype_provenance_records.len())
                .expect("specialize provenance record fits in u32"),
        );
        self.subtype_provenance_records
            .push(SpecializeSubtypeProvenanceRecord {
                semantic_key: semantic_key.clone(),
                incoming: vec![derivation],
                completeness,
            });
        self.subtype_position_provenance.push(positions);
        self.subtype_provenance_by_key.insert(semantic_key, id);
        self.subtype_provenance_metrics.records += 1;
        self.subtype_provenance_metrics.incoming_inserted += 1;
        Some(id)
    }

    fn merge_positions(
        &mut self,
        id: SpecializeSubtypeProvenanceRecordId,
        incoming: SubtypePositionProvenance,
    ) {
        let existing = &mut self.subtype_position_provenance[id.index()];
        let exhausted = merge_materialized_positions(&mut existing.lower, incoming.lower)
            | merge_materialized_positions(&mut existing.upper, incoming.upper);
        if exhausted {
            self.subtype_provenance_records[id.index()].completeness =
                ProvenanceCompleteness::Incomplete;
            self.subtype_provenance_metrics.budget_exhaustions += 1;
        }
    }

    fn constrain_structural_subtype(
        &mut self,
        lower: Type,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
        parent: Option<SpecializeSubtypeProvenanceRecordId>,
        lower_step: TypePositionStep,
        upper_step: TypePositionStep,
    ) -> Result<(), SpecializeError> {
        let Some(parent) = parent else {
            return self.constrain_weighted_subtype(lower, lower_weight, upper, upper_weight);
        };
        let parent_positions = &self.subtype_position_provenance[parent.index()];
        let positions = SubtypePositionProvenance {
            lower: advance_materialized_positions(&parent_positions.lower, lower_step),
            upper: advance_materialized_positions(&parent_positions.upper, upper_step),
        };
        let completeness = compose_completeness(
            self.subtype_provenance_records[parent.index()].completeness,
            compose_completeness(positions.lower.completeness, positions.upper.completeness),
        );
        self.intern_weighted_subtype(
            lower,
            lower_weight,
            upper,
            upper_weight,
            SpecializeProvenanceDerivation::Structural {
                parent,
                step: lower_step,
            },
            positions,
            completeness,
        );
        Ok(())
    }

    fn record_shadow_failure(
        &mut self,
        record: Option<SpecializeSubtypeProvenanceRecordId>,
    ) -> Option<UnsatisfiedSubtypeProvenance> {
        let Some(record) = record else {
            return None;
        };
        if self.shadow_subtype_failures.len() >= MAX_SHADOW_SUBTYPE_FAILURES {
            self.subtype_provenance_records[record.index()].completeness =
                ProvenanceCompleteness::Incomplete;
            self.subtype_provenance_metrics.budget_exhaustions += 1;
            return None;
        }
        let positions = &self.subtype_position_provenance[record.index()];
        let failure = SubtypeFailureProvenance {
            record,
            lower: anchors_at_root(&positions.lower),
            upper: anchors_at_root(&positions.upper),
            completeness: self.subtype_provenance_records[record.index()].completeness,
        };
        #[cfg(test)]
        capture_shadow_subtype_failure(&failure);
        let provenance = UnsatisfiedSubtypeProvenance {
            lower: failure.lower.clone(),
            upper: failure.upper.clone(),
            completeness: failure.completeness,
        };
        self.shadow_subtype_failures.push(failure);
        Some(provenance)
    }

    fn constrain_open_var_bound_pair(
        &mut self,
        lower: Type,
        lower_parent: Option<SpecializeSubtypeProvenanceRecordId>,
        upper: Type,
        upper_parent: Option<SpecializeSubtypeProvenanceRecordId>,
    ) -> Result<(), SpecializeError> {
        let lower_positions = lower_parent
            .map(|parent| {
                self.subtype_position_provenance[parent.index()]
                    .lower
                    .clone()
            })
            .unwrap_or_else(|| incomplete_positions().lower);
        let upper_positions = upper_parent
            .map(|parent| {
                self.subtype_position_provenance[parent.index()]
                    .upper
                    .clone()
            })
            .unwrap_or_else(|| incomplete_positions().upper);
        let completeness =
            compose_completeness(lower_positions.completeness, upper_positions.completeness);
        let parents = [lower_parent, upper_parent].into_iter().flatten().collect();
        self.intern_weighted_subtype(
            lower,
            empty_stack_weight(),
            upper,
            empty_stack_weight(),
            SpecializeProvenanceDerivation::OpenVarBound { parents },
            SubtypePositionProvenance {
                lower: lower_positions,
                upper: upper_positions,
            },
            completeness,
        );
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
            let provenance = self.subtype_provenance_by_key.get(&constraint).copied();
            self.process_subtype(
                constraint.lower,
                constraint.lower_weight,
                constraint.upper,
                constraint.upper_weight,
                provenance,
            )?;
        }
        Ok(())
    }

    pub(super) fn close_pure_effect_subtraction_tails_until_stable(
        &mut self,
    ) -> Result<(), SpecializeError> {
        loop {
            while let Some(constraint) = self.pending.pop_front() {
                let provenance = self.subtype_provenance_by_key.get(&constraint).copied();
                self.process_subtype(
                    constraint.lower,
                    constraint.lower_weight,
                    constraint.upper,
                    constraint.upper_weight,
                    provenance,
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
        provenance: Option<SpecializeSubtypeProvenanceRecordId>,
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
            (Type::OpenVar(slot), upper) => self.add_upper_weighted_with_provenance(
                slot,
                lower_weight,
                upper,
                upper_weight,
                provenance,
            ),
            (lower, Type::OpenVar(slot)) => self.add_lower_weighted_with_provenance(
                slot,
                lower,
                lower_weight,
                upper_weight,
                provenance,
            ),
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
                for (index, (lower, upper)) in lower_items.into_iter().zip(upper_items).enumerate()
                {
                    self.constrain_structural_subtype(
                        lower,
                        lower_weight.clone(),
                        upper,
                        upper_weight.clone(),
                        provenance,
                        TypePositionStep::TupleElement(
                            poly::provenance::TypePositionIndex::from_usize(index),
                        ),
                        TypePositionStep::TupleElement(
                            poly::provenance::TypePositionIndex::from_usize(index),
                        ),
                    )?;
                }
                Ok(())
            }
            (Type::Tuple(lower_items), Type::Tuple(upper_items)) => {
                let provenance = self.record_shadow_failure(provenance);
                unsatisfied_subtype(
                    Type::Tuple(lower_items),
                    Type::Tuple(upper_items),
                    provenance,
                )
            }
            (Type::Record(lower_fields), Type::Record(upper_fields)) => {
                let missing_required_field = upper_fields.iter().any(|upper_field| {
                    !upper_field.optional
                        && record_field_type(&lower_fields, &upper_field.name).is_none()
                });
                if missing_required_field {
                    let provenance = self.record_shadow_failure(provenance);
                    return unsatisfied_subtype(
                        Type::Record(lower_fields),
                        Type::Record(upper_fields),
                        provenance,
                    );
                }
                for (upper_index, upper_field) in upper_fields.into_iter().enumerate() {
                    if let Some((lower_index, lower_field)) = lower_fields
                        .iter()
                        .enumerate()
                        .find(|(_, field)| field.name == upper_field.name)
                    {
                        self.constrain_structural_subtype(
                            lower_field.value.clone(),
                            lower_weight.clone(),
                            upper_field.value,
                            upper_weight.clone(),
                            provenance,
                            TypePositionStep::RecordField {
                                alternative: poly::provenance::TypePositionIndex::from_usize(0),
                                field: poly::provenance::TypePositionIndex::from_usize(lower_index),
                            },
                            TypePositionStep::RecordField {
                                alternative: poly::provenance::TypePositionIndex::from_usize(0),
                                field: poly::provenance::TypePositionIndex::from_usize(upper_index),
                            },
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
                    let provenance = self.record_shadow_failure(provenance);
                    return unsatisfied_subtype(
                        Type::PolyVariant(lower_variants),
                        Type::PolyVariant(upper_variants),
                        provenance,
                    );
                }
                for (lower_item, lower_variant) in lower_variants.into_iter().enumerate() {
                    let (upper_item, upper_variant) = upper_variants
                        .iter()
                        .enumerate()
                        .find(|(_, variant)| variant.name == lower_variant.name)
                        .expect("poly variant mismatch checked above");
                    for (payload, (lower, upper)) in lower_variant
                        .payloads
                        .into_iter()
                        .zip(upper_variant.payloads.iter().cloned())
                        .enumerate()
                    {
                        self.constrain_structural_subtype(
                            lower,
                            lower_weight.clone(),
                            upper,
                            upper_weight.clone(),
                            provenance,
                            TypePositionStep::VariantPayload {
                                alternative: poly::provenance::TypePositionIndex::from_usize(0),
                                item: poly::provenance::TypePositionIndex::from_usize(lower_item),
                                payload: poly::provenance::TypePositionIndex::from_usize(payload),
                            },
                            TypePositionStep::VariantPayload {
                                alternative: poly::provenance::TypePositionIndex::from_usize(0),
                                item: poly::provenance::TypePositionIndex::from_usize(upper_item),
                                payload: poly::provenance::TypePositionIndex::from_usize(payload),
                            },
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
        #[cfg(test)]
        observe_ordinary_cast_resolution(
            self.arena,
            OrdinaryCastShadowSeam::TypeGraphConstraint,
            source,
            target,
        );
        let candidates = self
            .arena
            .cast_rules
            .iter()
            .filter(|rule| {
                rule.kind == poly_expr::CastRuleKind::Value
                    && rule.source == source
                    && rule.target == target
            })
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

fn incomplete_positions() -> SubtypePositionProvenance {
    SubtypePositionProvenance {
        lower: types::MaterializedTypeProvenance {
            positions: Vec::new(),
            completeness: ProvenanceCompleteness::Incomplete,
        },
        upper: types::MaterializedTypeProvenance {
            positions: Vec::new(),
            completeness: ProvenanceCompleteness::Incomplete,
        },
    }
}

fn anchors_at_root(provenance: &types::MaterializedTypeProvenance) -> Vec<ProvenanceAnchor> {
    let mut anchors = Vec::new();
    for position in &provenance.positions {
        if !position.path.0.is_empty() {
            continue;
        }
        for anchor in &position.anchors {
            if !anchors.contains(anchor) {
                anchors.push(*anchor);
            }
        }
    }
    anchors
}

fn advance_materialized_positions(
    provenance: &types::MaterializedTypeProvenance,
    step: TypePositionStep,
) -> types::MaterializedTypeProvenance {
    let positions = provenance
        .positions
        .iter()
        .filter_map(|position| {
            let Some((first, rest)) = position.path.0.split_first() else {
                return Some(position.clone());
            };
            (*first == step).then(|| types::MaterializedPositionProvenance {
                path: poly::provenance::TypePositionPath(rest.to_vec()),
                anchors: position.anchors.clone(),
                completeness: position.completeness,
            })
        })
        .collect();
    types::MaterializedTypeProvenance {
        positions,
        completeness: provenance.completeness,
    }
}

fn merge_materialized_positions(
    existing: &mut types::MaterializedTypeProvenance,
    incoming: types::MaterializedTypeProvenance,
) -> bool {
    let mut exhausted = false;
    existing.completeness = compose_completeness(existing.completeness, incoming.completeness);
    for position in incoming.positions {
        if let Some(current) = existing
            .positions
            .iter_mut()
            .find(|current| current.path == position.path)
        {
            current.completeness =
                compose_completeness(current.completeness, position.completeness);
            for anchor in position.anchors {
                if !current.anchors.contains(&anchor) {
                    if current.anchors.len() < MAX_ANCHORS_PER_MATERIALIZED_POSITION {
                        current.anchors.push(anchor);
                    } else {
                        current.completeness = ProvenanceCompleteness::Incomplete;
                        existing.completeness = ProvenanceCompleteness::Incomplete;
                        exhausted = true;
                    }
                }
            }
        } else if existing.positions.len() < MAX_MATERIALIZED_POSITIONS_PER_RECORD {
            existing.positions.push(position);
        } else {
            existing.completeness = ProvenanceCompleteness::Incomplete;
            exhausted = true;
        }
    }
    exhausted
}

fn compose_completeness(
    left: ProvenanceCompleteness,
    right: ProvenanceCompleteness,
) -> ProvenanceCompleteness {
    if left == ProvenanceCompleteness::Complete && right == ProvenanceCompleteness::Complete {
        ProvenanceCompleteness::Complete
    } else {
        ProvenanceCompleteness::Incomplete
    }
}

fn unsatisfied_subtype(
    lower: Type,
    upper: Type,
    provenance: Option<UnsatisfiedSubtypeProvenance>,
) -> Result<(), SpecializeError> {
    Err(SpecializeError::UnsatisfiedSubtype {
        lower,
        upper,
        origin: None,
        provenance,
    })
}
