//! Operation-local polarity copies for the private mixed graph solver.
use crate::*;

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct Key(ExtrusionEndpoint, Polarity, u32);
#[derive(Clone, Copy)]
enum Work {
    Visit(Key),
    Function(Key, [Key; 4], [Term; 4]),
    EffectView(Key, u32, Key),
    Bound(ExtrusionEndpoint, Polarity, Key, crate::candidate_effect::BoundKey),
    IncomingAllowance(u32, u32, Key, crate::candidate_effect::BoundKey),
}
fn opposite(p: Polarity) -> Polarity {
    match p {
        Polarity::Positive => Polarity::Negative,
        Polarity::Negative => Polarity::Positive,
    }
}
impl InferenceSession {
    pub(super) fn candidate_extrude(
        &mut self,
        initial: ExtrusionEndpoint,
        polarity: Polarity,
        level: u32,
    ) -> Result<ExtrusionEndpoint, SolveAvailabilityError> {
        // Row identities are memoized before traversing bounds. Structural
        // memoization is separate; neither memo survives source mutation.
        let mut rows = HashMap::new();
        let mut structure = HashMap::new();
        let mut work = Vec::new();
        // Finish structural nodes before following selected row bounds. A
        // bound may name the Function currently being rebuilt through a row.
        let mut pending_bounds = Vec::new();
        let mut view_remap = HashMap::new();
        let mut charge = 0usize;
        let result = (|| {
            // Account each capacity delta before nested constructors can sample it.
            macro_rules! work_push {
                ($items:ident, $item:expr) => {{
                    let item = $item;
                    let old = $items.capacity();
                    $items
                        .try_reserve(1)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                    self.candidate_scratch_growth(
                        &mut charge,
                        ($items.capacity() - old)
                            .checked_mul(std::mem::size_of::<Work>())
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                    )?;
                    $items.push(item);
                    Ok::<(), SolveAvailabilityError>(())
                }};
            }
            macro_rules! map_insert {
                ($map:ident, $key:expr, $value:expr) => {{
                    let key = $key;
                    let value = $value;
                    let old = $map.capacity();
                    $map.try_reserve(1)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                    self.candidate_scratch_growth(
                        &mut charge,
                        ($map.capacity() - old)
                            .checked_mul(std::mem::size_of::<(Key, ExtrusionEndpoint)>())
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                    )?;
                    $map.insert(key, value);
                    Ok::<(), SolveAvailabilityError>(())
                }};
            }
            let root = Key(self.canonical_extrusion(initial), polarity, level);
            work_push!(work, Work::Visit(root))?;
            while let Some(task) = work.pop().or_else(|| pending_bounds.pop()) {
                match task {
                    Work::Visit(key @ Key(endpoint, p, target)) => {
                        if rows.contains_key(&key) || structure.contains_key(&key) {
                            continue;
                        }
                        let row = match endpoint {
                            ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(i)) => {
                                Some((false, i, self.value_levels[i as usize]))
                            }
                            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(i)) => {
                                Some((true, i, self.effect_levels[i as usize]))
                            }
                            _ => None,
                        };
                        if let Some((effect, ordinal, original_level)) = row {
                            if original_level <= target {
                                map_insert!(rows, key, endpoint)?;
                                continue;
                            }
                            let i = ordinal as usize;
                            // Snapshot lengths before the one-sided source link.
                            let (direct, exact) = if effect {
                                let b = &self.effect_bounds[i];
                                if p == Polarity::Positive {
                                    (b.direct_lower_rows.len(), b.exact_non_variable_lowers.len())
                                } else {
                                    (b.direct_upper_rows.len(), b.exact_non_variable_uppers.len())
                                }
                            } else {
                                let b = &self.bounds[i];
                                if p == Polarity::Positive {
                                    (b.direct_lower_rows.len(), b.exact_non_variable_lowers.len())
                                } else {
                                    (b.direct_upper_rows.len(), b.exact_non_variable_uppers.len())
                                }
                            };
                            let copy = if effect {
                                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(
                                    self.fresh_effect_at_level(target)?,
                                ))
                            } else {
                                ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(
                                    self.fresh_value_at_level(target)?,
                                ))
                            };
                            self.retain_extrusion_parent(copy, endpoint, p, target)?;
                            map_insert!(rows, key, copy)?;
                            self.candidate_insert_bound(endpoint, opposite(p), copy)?;
                            for n in (0..direct + exact).rev() {
                                let bound = if effect {
                                    let b = &self.effect_bounds[i];
                                    ExtrusionEndpoint::Effect(if n < direct {
                                        EffectEndpointKey::EffectRow(if p == Polarity::Positive {
                                            b.direct_lower_rows[n]
                                        } else {
                                            b.direct_upper_rows[n]
                                        })
                                    } else if p == Polarity::Positive {
                                        b.exact_non_variable_lowers[n - direct]
                                    } else {
                                        b.exact_non_variable_uppers[n - direct]
                                    })
                                } else {
                                    let b = &self.bounds[i];
                                    ExtrusionEndpoint::Value(if n < direct {
                                        ValueEndpointKey::ValueRow(if p == Polarity::Positive {
                                            b.direct_lower_rows[n]
                                        } else {
                                            b.direct_upper_rows[n]
                                        })
                                    } else if p == Polarity::Positive {
                                        b.exact_non_variable_lowers[n - direct]
                                    } else {
                                        b.exact_non_variable_uppers[n - direct]
                                    })
                                };
                                let child = Key(self.canonical_extrusion(bound), p, target);
                                work_push!(
                                    pending_bounds,
                                    Work::Bound(
                                        copy,
                                        p,
                                        child,
                                        crate::candidate_effect::BoundKey(endpoint, p, bound)
                                    )
                                )?;
                                work_push!(pending_bounds, Work::Visit(child))?;
                            }
                            if effect && p == Polarity::Positive {
                                let ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(copied_tail)) = copy else { unreachable!() };
                                let mut record = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra
                                    .capture_incidence.get(&ordinal).map(|bucket| bucket.head);
                                while let Some(index) = record {
                                    let incidence = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_records[index];
                                    record = incidence.next;
                                    let source = self.canonical_extrusion(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(incidence.source)));
                                    let source_key = Key(source, Polarity::Positive, target);
                                    work_push!(pending_bounds, Work::IncomingAllowance(copied_tail, incidence.view, source_key,
                                        crate::candidate_effect::BoundKey(source, Polarity::Negative, ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(incidence.view)))))?;
                                    work_push!(pending_bounds, Work::Visit(source_key))?;
                                }
                            }
                            continue;
                        }
                        if let ExtrusionEndpoint::Effect(
                            EffectEndpointKey::Allowance(id)
                            | EffectEndpointKey::Support(id)
                            | EffectEndpointKey::AnnotationMember(id, _),
                        ) = endpoint
                        {
                            let tail = self
                                .candidate_graph
                                .as_ref()
                                .unwrap()
                                .intrusion
                                .effect_algebra
                                .views[id as usize]
                                .tail;
                            if let Some(tail) = tail {
                                let child = Key(
                                    self.canonical_extrusion(ExtrusionEndpoint::Effect(
                                        EffectEndpointKey::EffectRow(tail),
                                    )),
                                    p,
                                    target,
                                );
                                work_push!(work, Work::EffectView(key, id, child))?;
                                work_push!(work, Work::Visit(child))?;
                            } else {
                                map_insert!(structure, key, endpoint)?;
                            }
                            continue;
                        }
                        let ports = match endpoint {
                            ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(t)) => {
                                Self::positive_function_children(
                                    &self.store,
                                    ValueEndpointKey::PositiveFunction(t),
                                )
                            }
                            ExtrusionEndpoint::Value(ValueEndpointKey::NegativeFunction(t)) => {
                                Self::negative_function_children(
                                    &self.store,
                                    ValueEndpointKey::NegativeFunction(t),
                                )
                            }
                            _ => None,
                        };
                        if let Some((a, ae, re, r)) = ports {
                            let terms = [a, ae, re, r];
                            let children = [
                                Key(
                                    ExtrusionEndpoint::Value(self.value_endpoint(a, opposite(p))),
                                    opposite(p),
                                    target,
                                ),
                                Key(
                                    ExtrusionEndpoint::Effect(
                                        self.effect_endpoint(ae, opposite(p)),
                                    ),
                                    opposite(p),
                                    target,
                                ),
                                Key(
                                    ExtrusionEndpoint::Effect(self.effect_endpoint(re, p)),
                                    p,
                                    target,
                                ),
                                Key(
                                    ExtrusionEndpoint::Value(self.value_endpoint(r, p)),
                                    p,
                                    target,
                                ),
                            ];
                            work_push!(work, Work::Function(key, children, terms))?;
                            for child in children.into_iter().rev() {
                                work_push!(work, Work::Visit(child))?;
                            }
                        } else {
                            map_insert!(structure, key, endpoint)?;
                        }
                    }
                    Work::EffectView(key, id, child) => {
                        let endpoint = rows
                            .get(&child)
                            .or_else(|| structure.get(&child))
                            .copied()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(tail)) =
                            endpoint
                        else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        let old = view_remap.capacity();
                        view_remap
                            .try_reserve(1)
                            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                        self.candidate_scratch_growth(
                            &mut charge,
                            (view_remap.capacity() - old)
                                .checked_mul(std::mem::size_of::<((u32, Option<u32>), u32)>())
                                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                        )?;
                        let copy =
                            self.candidate_remapped_effect_view(id, Some(tail), &mut view_remap)?;
                        let copied = match key.0 {
                            ExtrusionEndpoint::Effect(EffectEndpointKey::Support(_)) => {
                                EffectEndpointKey::Support(copy)
                            }
                            ExtrusionEndpoint::Effect(EffectEndpointKey::AnnotationMember(
                                _,
                                member,
                            )) => EffectEndpointKey::AnnotationMember(copy, member),
                            _ => EffectEndpointKey::Allowance(copy),
                        };
                        map_insert!(structure, key, ExtrusionEndpoint::Effect(copied))?;
                    }
                    Work::IncomingAllowance(tail, view, source_key, original) => {
                        let source = rows.get(&source_key).or_else(|| structure.get(&source_key)).copied()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let old = view_remap.capacity();
                        view_remap.try_reserve(1).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                        self.candidate_scratch_growth(&mut charge, (view_remap.capacity() - old)
                            .checked_mul(std::mem::size_of::<((u32, Option<u32>), u32)>())
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?)?;
                        let mapped = self.candidate_remapped_effect_view(view, Some(tail), &mut view_remap)?;
                        let allowance = ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(mapped));
                        self.candidate_insert_bound(source, Polarity::Negative, allowance)?;
                        self.candidate_transfer_bound_origins(original,
                            crate::candidate_effect::BoundKey(source, Polarity::Negative, allowance),
                            candidate_context::TransportReason::Extrusion { operation: initial, polarity, target_level: level })?;
                    }
                    Work::Bound(owner, p, key, source) => {
                        let copied = rows
                            .get(&key)
                            .or_else(|| structure.get(&key))
                            .copied()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        self.candidate_insert_bound(owner, p, copied)?;
                        self.candidate_transfer_bound_origins(
                            source,
                            crate::candidate_effect::BoundKey(
                                self.canonical_extrusion(owner),
                                p,
                                self.canonical_extrusion(copied),
                            ),
                            candidate_context::TransportReason::Extrusion { operation: initial, polarity, target_level: level },
                        )?;
                    }
                    Work::Function(key @ Key(original, p, _), children, originals) => {
                        let mut terms = originals;
                        let mut changed = false;
                        for i in 0..4 {
                            let endpoint = rows
                                .get(&children[i])
                                .or_else(|| structure.get(&children[i]))
                                .copied()
                                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                            if endpoint != children[i].0 {
                                changed = true;
                                terms[i] = self.candidate_endpoint_term(endpoint, children[i].1)?;
                            }
                        }
                        let result = if !changed {
                            original
                        } else {
                            ExtrusionEndpoint::Value(if p == Polarity::Positive {
                                ValueEndpointKey::PositiveFunction(self.positive_function_term(
                                    terms[0], terms[1], terms[2], terms[3],
                                )?)
                            } else {
                                ValueEndpointKey::NegativeFunction(self.negative_function_term(
                                    terms[0], terms[1], terms[2], terms[3],
                                )?)
                            })
                        };
                        map_insert!(structure, key, result)?;
                    }
                }
            }
            let result = rows
                .get(&root)
                .or_else(|| structure.get(&root))
                .copied()
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            Ok(result)
        })();
        drop((rows, structure, work, pending_bounds, view_remap));
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
        result
    }
    fn candidate_endpoint_term(
        &mut self,
        endpoint: ExtrusionEndpoint,
        p: Polarity,
    ) -> Result<Term, SolveAvailabilityError> {
        Ok(match endpoint {
            ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(i)) => {
                self.live_value_term(p, i)?
            }
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(i)) => {
                self.live_effect_term(p, i)?
            }
            ExtrusionEndpoint::Value(
                ValueEndpointKey::PositiveFunction(t) | ValueEndpointKey::NegativeFunction(t),
            ) => t,
            _ => return Err(SolveAvailabilityError::IdentityExhausted),
        })
    }

    /// Install only the selected side, including initialization of copies.
    /// Positive selects a lower bound; negative selects an upper bound.
    pub(super) fn candidate_insert_bound(
        &mut self,
        owner: ExtrusionEndpoint,
        p: Polarity,
        bound: ExtrusionEndpoint,
    ) -> Result<(), SolveAvailabilityError> {
        let processing = self.candidate_graph.as_ref().ok_or(SolveAvailabilityError::IdentityExhausted)?.intrusion.effect_algebra.context.processing;
        self.candidate_insert_bound_with_evidence(owner, p, bound, true,
            candidate_context::BoundAdmissionCause::OwnerEmission { processing }).map(|_| ())
    }
    pub(super) fn candidate_insert_bound_without_capture(
        &mut self, owner: ExtrusionEndpoint, p: Polarity, bound: ExtrusionEndpoint,
    ) -> Result<(), SolveAvailabilityError> {
        let processing = self.candidate_graph.as_ref().ok_or(SolveAvailabilityError::IdentityExhausted)?.intrusion.effect_algebra.context.processing;
        self.candidate_insert_bound_with_evidence(owner, p, bound, false,
            candidate_context::BoundAdmissionCause::OwnerEmission { processing }).map(|_| ())
    }
    pub(super) fn candidate_insert_bound_with_evidence(
        &mut self, owner: ExtrusionEndpoint, p: Polarity, bound: ExtrusionEndpoint, capture: bool,
        cause: candidate_context::BoundAdmissionCause,
    ) -> Result<candidate_context::BoundEmissionId, SolveAvailabilityError> {
        let mut physical: candidate_context::PhysicalBoundSlot;
        macro_rules! insert_bound {
            ($rows:ident, $index:expr, $field:ident, $item:expr, $lane:expr, $effect:expr) => {{
                let i = $index;
                let old = self.$rows[i].$field.capacity();
                let reserved = reserve_f5b(&mut self.$rows[i].$field, 1, $lane);
                self.record_incoming_bound_capacity_growth(
                    i,
                    $effect,
                    $lane,
                    old,
                    self.$rows[i].$field.capacity(),
                    std::mem::size_of_val(&$item),
                    reserved,
                )?;
                physical.index = self.$rows[i].$field.len();
                self.$rows[i].$field.push($item);
            }};
        }
        let owner = self.canonical_extrusion(owner);
        let bound = self.canonical_extrusion(bound);
        use candidate_context::BoundLane;
        use candidate_scheme::RowKey;
        let (row, lane) = match (owner, bound, p) {
            (ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(i)), ExtrusionEndpoint::Value(item), p)
                if (i as usize) < self.bounds.len() => (RowKey::Value(i), match (p, item) {
                    (Polarity::Positive, ValueEndpointKey::ValueRow(_)) => BoundLane::ValueLowerRow,
                    (Polarity::Negative, ValueEndpointKey::ValueRow(_)) => BoundLane::ValueUpperRow,
                    (Polarity::Positive, _) => BoundLane::ValueLowerAtom,
                    (Polarity::Negative, _) => BoundLane::ValueUpperAtom,
                }),
            (ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(i)), ExtrusionEndpoint::Effect(item), p)
                if (i as usize) < self.effect_bounds.len() => (RowKey::Effect(i), match (p, item) {
                    (Polarity::Positive, EffectEndpointKey::EffectRow(_)) => BoundLane::EffectLowerRow,
                    (Polarity::Negative, EffectEndpointKey::EffectRow(_)) => BoundLane::EffectUpperRow,
                    (Polarity::Positive, _) => BoundLane::EffectLowerAtom,
                    (Polarity::Negative, _) => BoundLane::EffectUpperAtom,
                }),
            _ => return Err(SolveAvailabilityError::IdentityExhausted),
        };
        let admission = self.candidate_bound_origin_with_evidence(crate::candidate_effect::BoundKey(owner, p, bound), None, cause)?;
        self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.reserve_evidence_emission()?;
        physical = candidate_context::PhysicalBoundSlot { owner: row, lane, index: 0 };
        match (owner, bound) {
            (
                ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(i)),
                ExtrusionEndpoint::Value(item),
            ) => {
                let i = i as usize;
                self.journal_value_row(i)?;
                match (p, item) {
                    (Polarity::Positive, ValueEndpointKey::ValueRow(row)) => insert_bound!(
                        bounds,
                        i,
                        direct_lower_rows,
                        row,
                        F5bCapacityLane::ValueDirectLower,
                        false
                    ),
                    (Polarity::Negative, ValueEndpointKey::ValueRow(row)) => insert_bound!(
                        bounds,
                        i,
                        direct_upper_rows,
                        row,
                        F5bCapacityLane::ValueDirectUpper,
                        false
                    ),
                    (Polarity::Positive, item) => {
                        insert_bound!(
                            bounds,
                            i,
                            exact_non_variable_lowers,
                            item,
                            F5bCapacityLane::ValueExactLower,
                            false
                        );
                        self.bounds[i].has_int_positive_lower |=
                            item == ValueEndpointKey::IntPositive;
                        self.bounds[i].has_unit_positive_lower |=
                            item == ValueEndpointKey::UnitPositive;
                    }
                    (Polarity::Negative, item) => insert_bound!(
                        bounds,
                        i,
                        exact_non_variable_uppers,
                        item,
                        F5bCapacityLane::ValueExactUpper,
                        false
                    ),
                }
                if p == Polarity::Positive {
                    self.execution_counters.lower_bound_insertions += 1;
                } else {
                    self.execution_counters.upper_bound_insertions += 1;
                }
            }
            (
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(i)),
                ExtrusionEndpoint::Effect(item),
            ) => {
                let i = i as usize;
                self.journal_effect_row(i)?;
                match (p, item) {
                    (Polarity::Positive, EffectEndpointKey::EffectRow(row)) => insert_bound!(
                        effect_bounds,
                        i,
                        direct_lower_rows,
                        row,
                        F5bCapacityLane::EffectDirectLower,
                        true
                    ),
                    (Polarity::Negative, EffectEndpointKey::EffectRow(row)) => insert_bound!(
                        effect_bounds,
                        i,
                        direct_upper_rows,
                        row,
                        F5bCapacityLane::EffectDirectUpper,
                        true
                    ),
                    (Polarity::Positive, item) => {
                        insert_bound!(
                            effect_bounds,
                            i,
                            exact_non_variable_lowers,
                            item,
                            F5bCapacityLane::EffectExactLower,
                            true
                        );
                        self.effect_bounds[i].has_bottom_lower |=
                            item == EffectEndpointKey::BottomPositive;
                    }
                    (Polarity::Negative, item) => {
                        insert_bound!(
                            effect_bounds,
                            i,
                            exact_non_variable_uppers,
                            item,
                            F5bCapacityLane::EffectExactUpper,
                            true
                        );
                        self.effect_bounds[i].has_empty_upper |=
                            item == EffectEndpointKey::EmptyNegative;
                    }
                }
            }
            _ => return Err(SolveAvailabilityError::IdentityExhausted),
        }
        if capture { self.candidate_register_capture_bound(crate::candidate_effect::BoundKey(owner, p, bound))?; }
        let graph = self.candidate_graph.as_mut().ok_or(SolveAvailabilityError::IdentityExhausted)?;
        graph.intrusion.dirty = true;
        let emission = graph.intrusion.effect_algebra.context.evidence_emit(admission, physical);
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        #[cfg(test)]
        self.candidate_evidence_failure(candidate_context::EvidenceFailurePoint::Emission)?;
        Ok(emission)
    }

    pub(super) fn candidate_opposite_count(
        &self,
        owner: ExtrusionEndpoint,
        p: Polarity,
    ) -> Result<usize, SolveAvailabilityError> {
        Ok(match self.canonical_extrusion(owner) {
            ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(i)) => {
                let b = &self.bounds[i as usize];
                if p == Polarity::Positive {
                    b.direct_upper_rows.len() + b.exact_non_variable_uppers.len()
                } else {
                    b.direct_lower_rows.len() + b.exact_non_variable_lowers.len()
                }
            }
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(i)) => {
                let b = &self.effect_bounds[i as usize];
                if p == Polarity::Positive {
                    b.direct_upper_rows.len() + b.exact_non_variable_uppers.len()
                } else {
                    b.direct_lower_rows.len() + b.exact_non_variable_lowers.len()
                }
            }
            _ => return Err(SolveAvailabilityError::IdentityExhausted),
        })
    }
    pub(super) fn candidate_opposite_bound(
        &self,
        owner: ExtrusionEndpoint,
        p: Polarity,
        n: usize,
    ) -> ExtrusionEndpoint {
        self.canonical_extrusion(match self.canonical_extrusion(owner) {
            ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(i)) => {
                let b = &self.bounds[i as usize];
                let (direct, exact) = if p == Polarity::Positive {
                    (&b.direct_upper_rows, &b.exact_non_variable_uppers)
                } else {
                    (&b.direct_lower_rows, &b.exact_non_variable_lowers)
                };
                ExtrusionEndpoint::Value(if n < direct.len() {
                    ValueEndpointKey::ValueRow(direct[n])
                } else {
                    exact[n - direct.len()]
                })
            }
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(i)) => {
                let b = &self.effect_bounds[i as usize];
                let (direct, exact) = if p == Polarity::Positive {
                    (&b.direct_upper_rows, &b.exact_non_variable_uppers)
                } else {
                    (&b.direct_lower_rows, &b.exact_non_variable_lowers)
                };
                ExtrusionEndpoint::Effect(if n < direct.len() {
                    EffectEndpointKey::EffectRow(direct[n])
                } else {
                    exact[n - direct.len()]
                })
            }
            _ => unreachable!(),
        })
    }

    /// Scheme initialization is entered with an idle solver. Each induced
    /// comparison drains the owning worklist and replays its diagnostic with
    /// the incoming use's provenance; no mutable completed parent is reused.
    #[cfg(test)]
    pub(super) fn candidate_restore_bound(
        &mut self, owner: ExtrusionEndpoint, p: Polarity, bound: ExtrusionEndpoint,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<(), SolveAvailabilityError> {
        let processing = self.candidate_graph.as_ref().ok_or(SolveAvailabilityError::IdentityExhausted)?.intrusion.effect_algebra.context.processing;
        self.candidate_restore_bound_with_evidence(owner, p, bound, occurrence, cause,
            candidate_context::BoundAdmissionCause::OwnerEmission { processing }).map(|_| ())
    }

    pub(super) fn candidate_restore_bound_with_evidence(
        &mut self,
        owner: ExtrusionEndpoint,
        p: Polarity,
        bound: ExtrusionEndpoint,
        occurrence: &ConstraintOccurrenceId,
        cause: &CauseId,
        evidence: candidate_context::BoundAdmissionCause,
    ) -> Result<candidate_context::BoundEmissionId, SolveAvailabilityError> {
        assert!(
            self.typed_worklist.is_empty(),
            "scheme initialization owns an idle worklist"
        );
        let emission = self.candidate_insert_bound_with_evidence(owner, p, bound, true, evidence)?;
        let owner = self.canonical_extrusion(owner);
        let bound = self.canonical_extrusion(bound);
        let count = self.candidate_opposite_count(owner, p)?;
        for n in 0..count {
            let other = self.canonical_extrusion(self.candidate_opposite_bound(owner, p, n));
            let (lower, upper) = if p == Polarity::Positive {
                (bound, other)
            } else {
                (other, bound)
            };
            let task = match (lower, upper) {
                (ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) => {
                    LiveConstraintTask::Value(CanonicalValuePairKey { lower, upper })
                }
                (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)) => {
                    LiveConstraintTask::Effect(lower, upper)
                }
                _ => unreachable!(),
            };
            let opposite = if p == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
            let inserted = crate::candidate_effect::BoundKey(self.canonical_extrusion(owner), p, bound);
            let existing = crate::candidate_effect::BoundKey(self.canonical_extrusion(owner), opposite, other);
            let (lower_input, upper_input) = if p == Polarity::Positive { (inserted, existing) } else { (existing, inserted) };
            self.candidate_context_restore_replay(lower_input, upper_input, task, |session, relations| {
                for &relation in relations {
                    session.constrain_live_item(TypedWorkItem { task, relation: Some(relation) }, occurrence, cause)?;
                }
                Ok(())
            })?;
        }
        Ok(emission)
    }

    pub(super) fn candidate_replay_bound(
        &mut self,
        owner: ExtrusionEndpoint,
        p: Polarity,
        bound: ExtrusionEndpoint,
        parent: Option<CanonicalValuePairKey>,
    ) -> Result<(), SolveAvailabilityError> {
        let owner = self.canonical_extrusion(owner);
        let bound = self.canonical_extrusion(bound);
        let count = self.candidate_opposite_count(owner, p)?;
        for n in 0..count {
            let other = self.canonical_extrusion(self.candidate_opposite_bound(owner, p, n));
            let (lower, upper) = if p == Polarity::Positive {
                (bound, other)
            } else {
                (other, bound)
            };
            let task = match (lower, upper) {
                (ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) => {
                    let child = CanonicalValuePairKey { lower, upper };
                    if let Some(parent) = parent {
                        self.record_diagnostic_edge(parent, child, None)?;
                    }
                    if p == Polarity::Positive {
                        self.execution_counters.lower_bound_replays += 1;
                    } else {
                        self.execution_counters.upper_bound_replays += 1;
                    }
                    LiveConstraintTask::Value(child)
                }
                (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)) => {
                    LiveConstraintTask::Effect(lower, upper)
                }
                _ => unreachable!(),
            };
            let opposite = if p == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
            let inserted = crate::candidate_effect::BoundKey(self.canonical_extrusion(owner), p, bound);
            let existing = crate::candidate_effect::BoundKey(self.canonical_extrusion(owner), opposite, other);
            let (lower_input, upper_input) = if p == Polarity::Positive { (inserted, existing) } else { (existing, inserted) };
            self.candidate_context_replay(lower_input, upper_input, task, |session, relations| {
                for &relation in relations {
                    session.enqueue_item(TypedWorkItem { task, relation: Some(relation) }, false)?;
                }
                Ok(())
            })?;
        }
        Ok(())
    }

    pub(super) fn candidate_apply_value(
        &mut self,
        key: CanonicalValuePairKey,
    ) -> Result<usize, SolveAvailabilityError> {
        let key = CanonicalValuePairKey { lower: self.canonical_value(key.lower), upper: self.canonical_value(key.upper) };
        if key.lower == key.upper {
            return Ok(0);
        }
        let (owner, p, bound) = match (key.lower, key.upper) {
            (ValueEndpointKey::ValueRow(a), ValueEndpointKey::ValueRow(b))
                if self.value_levels[b as usize] <= self.value_levels[a as usize] =>
            {
                (a, Polarity::Negative, key.upper)
            }
            (_, ValueEndpointKey::ValueRow(b)) => (b, Polarity::Positive, key.lower),
            (ValueEndpointKey::ValueRow(a), _) => (a, Polarity::Negative, key.upper),
            _ => return Ok(0),
        };
        let old_int = self.bounds[owner as usize].has_int_positive_lower;
        let old_unit = self.bounds[owner as usize].has_unit_positive_lower;
        let owner = ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(owner));
        let bound = ExtrusionEndpoint::Value(bound);
        self.candidate_insert_bound(owner, p, bound)?;
        self.candidate_replay_bound(owner, p, bound, Some(key))?;
        let ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(i)) = owner else {
            unreachable!()
        };
        Ok(usize::from(
            !old_int && self.bounds[i as usize].has_int_positive_lower,
        ) + usize::from(!old_unit && self.bounds[i as usize].has_unit_positive_lower))
    }

    pub(super) fn candidate_apply_effect(
        &mut self,
        lower: EffectEndpointKey,
        upper: EffectEndpointKey,
    ) -> Result<(), SolveAvailabilityError> {
        let lower = self.canonical_effect(lower);
        let upper = self.canonical_effect(upper);
        if lower == upper {
            return Ok(());
        }
        let (i, p, bound) = match (lower, upper) {
            (EffectEndpointKey::EffectRow(a), EffectEndpointKey::EffectRow(b))
                if self.effect_levels[b as usize] <= self.effect_levels[a as usize] =>
            {
                (a, Polarity::Negative, upper)
            }
            (_, EffectEndpointKey::EffectRow(b)) => (b, Polarity::Positive, lower),
            (EffectEndpointKey::EffectRow(a), _) => (a, Polarity::Negative, upper),
            _ => return self.candidate_check_effect_operand(lower, upper),
        };
        let owner = ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(i));
        let bound = ExtrusionEndpoint::Effect(bound);
        self.candidate_insert_bound(owner, p, bound)?;
        self.candidate_replay_bound(owner, p, bound, None)
    }
}
