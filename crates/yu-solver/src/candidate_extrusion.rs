//! Operation-local polarity copies for the private mixed graph solver.
use crate::*;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Key(ExtrusionEndpoint, Polarity, u32);
#[derive(Clone, Copy, Debug)]
enum Work {
    Visit(Key),
    Function(Key, [Key; 4], [Term; 4]),
    Tuple(Key, usize, usize),
    Record(Key, usize, usize),
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
        let occurrence = self.begin_candidate_extrusion()?;
        #[cfg(test)]
        candidate_context::r148_trace(format!(
            "extrusion-start occurrence={occurrence} initial={initial:?} polarity={polarity:?} target={level} processing={:?}",
            self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.processing));
        let parent_start = self.candidate_graph.as_ref().unwrap().intrusion.parents.len();
        // Row identities are memoized before traversing bounds. Structural
        // memoization is separate; neither memo survives source mutation.
        let mut rows = HashMap::new();
        let mut structure = HashMap::new();
        let mut work = Vec::new();
        // Finish structural nodes before following selected row bounds. A
        // bound may name the Function currently being rebuilt through a row.
        let mut pending_bounds = Vec::new();
        let mut view_remap = HashMap::new();
        let mut initialized_allowances = Vec::new();
        let mut tuple_ports: Vec<(Key, Term)> = Vec::new();
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
                #[cfg(test)]
                candidate_context::r148_trace(format!("work-pop occurrence={occurrence} task={task:?}"));
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
                            self.retain_extrusion_parent(copy, endpoint, p, target, occurrence)?;
                            map_insert!(rows, key, copy)?;
                            let processing = self.candidate_graph.as_ref().ok_or(SolveAvailabilityError::IdentityExhausted)?.intrusion.effect_algebra.context.processing;
                            self.candidate_insert_bound_with_evidence(endpoint, opposite(p), copy, true,
                                candidate_context::BoundAdmissionCause::ExtrusionLink { processing })?;
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
                        if let ExtrusionEndpoint::Value(ValueEndpointKey::PositiveRecord(term)) = endpoint {
                            if p != Polarity::Positive { return Err(SolveAvailabilityError::ReceiptMismatch); }
                            let TermView::PositiveRecord { fields } = self.store.term_view(term)
                                .map_err(|_| SolveAvailabilityError::ReceiptMismatch)? else { return Err(SolveAvailabilityError::ReceiptMismatch); };
                            let start = tuple_ports.len();
                            let len = fields.len();
                            let old = tuple_ports.capacity();
                            tuple_ports.try_reserve_exact(len).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                            for (_, element) in fields {
                                tuple_ports.push((Key(ExtrusionEndpoint::Value(self.value_endpoint(*element, p)), p, target), *element));
                            }
                            self.candidate_scratch_growth(&mut charge, (tuple_ports.capacity() - old)
                                .checked_mul(std::mem::size_of::<(Key, Term)>()).ok_or(SolveAvailabilityError::IdentityExhausted)?)?;
                            work_push!(work, Work::Record(key, start, len))?;
                            for index in (start..start + len).rev() { work_push!(work, Work::Visit(tuple_ports[index].0))?; }
                            continue;
                        }
                        if let ExtrusionEndpoint::Value(ValueEndpointKey::PositiveTuple(term, arity)
                            | ValueEndpointKey::NegativeTuple(term, arity)) = endpoint
                        {
                            let elements = match self.store.term_view(term).map_err(|_| SolveAvailabilityError::IdentityExhausted)? {
                                TermView::PositiveTuple { elements } if p == Polarity::Positive => elements,
                                TermView::NegativeTuple { elements } if p == Polarity::Negative => elements,
                                _ => return Err(SolveAvailabilityError::IdentityExhausted),
                            };
                            if elements.len() != arity || arity == 0 { return Err(SolveAvailabilityError::IdentityExhausted); }
                            let start = tuple_ports.len();
                            let old = tuple_ports.capacity();
                            tuple_ports.try_reserve_exact(arity).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                            for &element in elements {
                                tuple_ports.push((Key(ExtrusionEndpoint::Value(self.value_endpoint(element, p)), p, target), element));
                            }
                            self.candidate_scratch_growth(&mut charge, (tuple_ports.capacity() - old)
                                .checked_mul(std::mem::size_of::<(Key, Term)>()).ok_or(SolveAvailabilityError::IdentityExhausted)?)?;
                            work_push!(work, Work::Tuple(key, start, arity))?;
                            for index in (start..start + arity).rev() {
                                work_push!(work, Work::Visit(tuple_ports[index].0))?;
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
                        self.candidate_insert_copied_bound(source, Polarity::Negative, allowance, true, original,
                            candidate_context::TransportReason::Extrusion { operation: initial, polarity, target_level: level })?;
                        let installed = crate::candidate_effect::BoundKey(
                            self.canonical_extrusion(source), Polarity::Negative,
                            self.canonical_extrusion(allowance));
                        self.candidate_transfer_bound_origins(original,
                            installed,
                            candidate_context::TransportReason::Extrusion { operation: initial, polarity, target_level: level })?;
                        let old = initialized_allowances.capacity();
                        initialized_allowances.try_reserve(1)
                            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                        self.candidate_scratch_growth(&mut charge,
                            (initialized_allowances.capacity() - old)
                                .checked_mul(std::mem::size_of::<crate::candidate_effect::BoundKey>())
                                .ok_or(SolveAvailabilityError::IdentityExhausted)?)?;
                        initialized_allowances.push(installed);
                    }
                    Work::Bound(owner, p, key, source) => {
                        #[cfg(test)]
                        candidate_context::r148_trace(format!("work-bound occurrence={occurrence} operation={initial:?} operation_polarity={polarity:?} target={level} raw={source:?} owner={owner:?} side={p:?} selected={key:?}"));
                        let copied = rows
                            .get(&key)
                            .or_else(|| structure.get(&key))
                            .copied()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        self.candidate_insert_copied_bound(owner, p, copied, true, source,
                            candidate_context::TransportReason::Extrusion { operation: initial, polarity, target_level: level })?;
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
                    Work::Record(key @ Key(original, p, _), start, len) => {
                        let children = tuple_ports.get(start..start.checked_add(len).ok_or(SolveAvailabilityError::IdentityExhausted)?)
                            .ok_or(SolveAvailabilityError::ReceiptMismatch)?;
                        let changed = children.iter().any(|(child, _)| rows.get(child).or_else(|| structure.get(child)).copied() != Some(child.0));
                        let result = if !changed { original } else {
                            let ExtrusionEndpoint::Value(ValueEndpointKey::PositiveRecord(term)) = original else { return Err(SolveAvailabilityError::ReceiptMismatch); };
                            let TermView::PositiveRecord { fields } = self.store.term_view(term).map_err(|_| SolveAvailabilityError::ReceiptMismatch)?
                                else { return Err(SolveAvailabilityError::ReceiptMismatch); };
                            let mut mapped = Vec::new();
                            mapped.try_reserve_exact(len).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                            for (label, term) in fields { mapped.push((label.clone(), *term)); }
                            let temporary = mapped.iter().try_fold(mapped.capacity().checked_mul(std::mem::size_of::<(Box<str>, Term)>())
                                .ok_or(SolveAvailabilityError::IdentityExhausted)?, |n, (label, _)| n.checked_add(label.len()).ok_or(SolveAvailabilityError::IdentityExhausted))?;
                            self.candidate_scratch_growth(&mut charge, temporary)?;
                            let rebuilt = (|| {
                                for ((_, mapped_term), (child, original_term)) in mapped.iter_mut().zip(children) {
                                    let copied = rows.get(child).or_else(|| structure.get(child)).copied().ok_or(SolveAvailabilityError::ReceiptMismatch)?;
                                    *mapped_term = if copied == child.0 { *original_term } else { self.candidate_endpoint_term(copied, p)? };
                                }
                                let term = self.with_term_events(|arena| arena.positive_record(&mapped))?;
                                Ok::<_, SolveAvailabilityError>(ExtrusionEndpoint::Value(ValueEndpointKey::PositiveRecord(term)))
                            })();
                            drop(mapped);
                            self.candidate_graph.as_mut().unwrap().scratch_bytes -= temporary;
                            charge -= temporary;
                            rebuilt?
                        };
                        map_insert!(structure, key, result)?;
                    }
                    Work::Tuple(key @ Key(original, p, _), start, len) => {
                        let children = tuple_ports.get(start..start.checked_add(len).ok_or(SolveAvailabilityError::IdentityExhausted)?)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let mut changed = false;
                        for &(child, _) in children {
                            let copied = rows.get(&child).or_else(|| structure.get(&child))
                                .copied().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                            changed |= copied != child.0;
                        }
                        let result = if !changed {
                            original
                        } else {
                            let mut elements = Vec::new();
                            elements.try_reserve_exact(len).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                            let temporary = elements.capacity().checked_mul(std::mem::size_of::<Term>())
                                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                            self.candidate_scratch_growth(&mut charge, temporary)?;
                            let rebuilt = (|| {
                                for &(child, original_term) in children {
                                    let copied = rows.get(&child).or_else(|| structure.get(&child))
                                        .copied().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                    elements.push(if copied == child.0 { original_term } else { self.candidate_endpoint_term(copied, p)? });
                                }
                                let term = self.with_term_events(|terms| match p {
                                    Polarity::Positive => terms.positive_tuple(&elements),
                                    Polarity::Negative => terms.negative_tuple(&elements),
                                })?;
                                Ok::<_, SolveAvailabilityError>(ExtrusionEndpoint::Value(match p {
                                    Polarity::Positive => ValueEndpointKey::PositiveTuple(term, len),
                                    Polarity::Negative => ValueEndpointKey::NegativeTuple(term, len),
                                }))
                            })();
                            drop(elements);
                            self.candidate_graph.as_mut().unwrap().scratch_bytes -= temporary;
                            charge -= temporary;
                            rebuilt?
                        };
                        map_insert!(structure, key, result)?;
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
            #[cfg(test)]
            candidate_context::r148_trace(format!("extrusion-finish occurrence={occurrence} output={result:?}"));
            self.finish_candidate_extrusion(occurrence, parent_start, result)?;
            // Selected Work::Bound copies are one-sided; only incoming cuts
            // add the opposite side. Wait for all selected lower fibers before
            // replaying those cuts. The existing outer drain owns the children.
            for &crate::candidate_effect::BoundKey(owner, p, bound) in &initialized_allowances {
                self.candidate_replay_bound(owner, p, bound, None)?;
            }
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            Ok(result)
        })();
        drop((rows, structure, work, pending_bounds, view_remap, initialized_allowances, tuple_ports));
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
                ValueEndpointKey::PositiveFunction(t) | ValueEndpointKey::NegativeFunction(t)
                | ValueEndpointKey::PositiveTuple(t, _) | ValueEndpointKey::NegativeTuple(t, _) | ValueEndpointKey::PositiveRecord(t),
            ) => t,
            _ => return Err(SolveAvailabilityError::IdentityExhausted),
        })
    }

    /// Install only the selected side, including initialization of copies.
    /// Positive selects a lower bound; negative selects an upper bound.
    // Physical copy bootstrap owns storage and diagnostics only. Exact
    // source fibers are installed by candidate_transfer_bound_origins next.
    pub(super) fn candidate_insert_copied_bound(
        &mut self, owner: ExtrusionEndpoint, polarity: Polarity, bound: ExtrusionEndpoint, capture: bool,
        source: crate::candidate_effect::BoundKey, reason: candidate_context::TransportReason,
    ) -> Result<(), SolveAvailabilityError> {
        let state = &self.candidate_graph.as_ref().ok_or(SolveAvailabilityError::IdentityExhausted)?.intrusion.effect_algebra.context;
        if !state.scoped_enabled {
            let processing = state.processing;
            return self.candidate_insert_bound_with_evidence(owner, polarity, bound, capture,
                candidate_context::BoundAdmissionCause::OwnerEmission { processing }).map(|_| ());
        }
        let snapshot = state.evidence_snapshot(source, None)
            .with_gap(candidate_context::CoverageGap::MissingOriginAssociation);
        let antecedent = self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.import_evidence(snapshot)?;
        self.candidate_insert_bound_with_evidence(owner, polarity, bound, capture,
            candidate_context::BoundAdmissionCause::BoundTransport { antecedent, through: reason }).map(|_| ())
    }
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
    /// Read the exact item back from its addressed physical bound vector. This
    /// runs immediately after the append; the retained evidence stores the
    /// resulting complete key, not a copy of either row vector.
    fn candidate_physical_slot_bound(
        &self, slot: candidate_context::PhysicalBoundSlot,
    ) -> Option<crate::candidate_effect::BoundKey> {
        use candidate_context::BoundLane;
        use candidate_scheme::RowKey;
        let owner = match slot.owner {
            RowKey::Value(row) => ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(row)),
            RowKey::Effect(row) => ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
        };
        let (polarity, item) = match (slot.owner, slot.lane) {
            (RowKey::Value(row), BoundLane::ValueLowerRow) => (
                Polarity::Positive,
                ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(
                    *self.bounds.get(row as usize)?.direct_lower_rows.get(slot.index)?,
                )),
            ),
            (RowKey::Value(row), BoundLane::ValueUpperRow) => (
                Polarity::Negative,
                ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(
                    *self.bounds.get(row as usize)?.direct_upper_rows.get(slot.index)?,
                )),
            ),
            (RowKey::Value(row), BoundLane::ValueLowerAtom) => (
                Polarity::Positive,
                ExtrusionEndpoint::Value(*self.bounds.get(row as usize)?.exact_non_variable_lowers.get(slot.index)?),
            ),
            (RowKey::Value(row), BoundLane::ValueUpperAtom) => (
                Polarity::Negative,
                ExtrusionEndpoint::Value(*self.bounds.get(row as usize)?.exact_non_variable_uppers.get(slot.index)?),
            ),
            (RowKey::Effect(row), BoundLane::EffectLowerRow) => (
                Polarity::Positive,
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(
                    *self.effect_bounds.get(row as usize)?.direct_lower_rows.get(slot.index)?,
                )),
            ),
            (RowKey::Effect(row), BoundLane::EffectUpperRow) => (
                Polarity::Negative,
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(
                    *self.effect_bounds.get(row as usize)?.direct_upper_rows.get(slot.index)?,
                )),
            ),
            (RowKey::Effect(row), BoundLane::EffectLowerAtom) => (
                Polarity::Positive,
                ExtrusionEndpoint::Effect(*self.effect_bounds.get(row as usize)?.exact_non_variable_lowers.get(slot.index)?),
            ),
            (RowKey::Effect(row), BoundLane::EffectUpperAtom) => (
                Polarity::Negative,
                ExtrusionEndpoint::Effect(*self.effect_bounds.get(row as usize)?.exact_non_variable_uppers.get(slot.index)?),
            ),
            _ => return None,
        };
        Some(crate::candidate_effect::BoundKey(owner, polarity, item))
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
                self.preflight_bound_capacity_growth(
                    i, $effect, self.$rows[i].$field.len(), old,
                )?;
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
        let expected_bound = crate::candidate_effect::BoundKey(owner, p, bound);
        let readback_bound = self.candidate_physical_slot_bound(physical)
            .ok_or(SolveAvailabilityError::ReceiptMismatch)?;
        if readback_bound != expected_bound {
            return Err(SolveAvailabilityError::ReceiptMismatch);
        }
        if capture { self.candidate_register_capture_bound(crate::candidate_effect::BoundKey(owner, p, bound))?; }
        let graph = self.candidate_graph.as_mut().ok_or(SolveAvailabilityError::IdentityExhausted)?;
        graph.intrusion.dirty = true;
        let emission = graph.intrusion.effect_algebra.context.evidence_emit(admission, physical,
            candidate_context::PhysicalBoundReadback {
                slot: physical,
                bound: readback_bound,
                phase: candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend,
            });
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

    #[cfg(test)]
    pub(super) fn candidate_restore_bound_with_evidence(
        &mut self,
        owner: ExtrusionEndpoint,
        p: Polarity,
        bound: ExtrusionEndpoint,
        occurrence: &ConstraintOccurrenceId,
        cause: &CauseId,
        evidence: candidate_context::BoundAdmissionCause,
    ) -> Result<candidate_context::BoundEmissionId, SolveAvailabilityError> {
        let restoration = self.candidate_begin_bound_restoration(owner, p, bound, occurrence, cause, evidence)?;
        self.candidate_drive_bound_restoration(restoration)
    }

    pub(super) fn candidate_begin_bound_restoration(
        &mut self,
        owner: ExtrusionEndpoint,
        p: Polarity,
        bound: ExtrusionEndpoint,
        occurrence: &ConstraintOccurrenceId,
        cause: &CauseId,
        evidence: candidate_context::BoundAdmissionCause,
    ) -> Result<candidate_context::ReplayOperationId, SolveAvailabilityError> {
        assert!(
            self.typed_worklist.is_empty(),
            "scheme initialization owns an idle worklist"
        );
        self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.reserve_restoration()?;
        let emission = self.candidate_insert_bound_with_evidence(owner, p, bound, true, evidence)?;
        let owner = self.canonical_extrusion(owner);
        let bound = self.canonical_extrusion(bound);
        let count = self.candidate_opposite_count(owner, p)?;
        Ok(self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.retain_restoration(
            owner, p, bound, emission, count, occurrence.clone(), cause.clone()))
    }

    pub(super) fn candidate_drive_bound_restoration(
        &mut self, restoration: candidate_context::ReplayOperationId,
    ) -> Result<candidate_context::BoundEmissionId, SolveAvailabilityError> {
        loop {
            if let Some(emission) = self.candidate_step_bound_restoration(restoration)? { return Ok(emission); }
        }
    }
    // One completed owner operation. Typed children and diagnostics remain
    // atomic; a local parent may retain the handle between these operations.
    pub(super) fn candidate_step_bound_restoration(
        &mut self, restoration: candidate_context::ReplayOperationId,
    ) -> Result<Option<candidate_context::BoundEmissionId>, SolveAvailabilityError> {
        self.candidate_step_bound_restoration_child(restoration, false)
    }
    // Both adapters use the same saved-count/live-index owner. The private
    // retained adapter stops after one whole child operation or receipt delivery.
    pub(super) fn candidate_step_bound_restoration_child(
        &mut self, restoration: candidate_context::ReplayOperationId, retain_child_step: bool,
    ) -> Result<Option<candidate_context::BoundEmissionId>, SolveAvailabilityError> {
        let operation = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.restoration(restoration)?;
        let (owner, p, bound, n, count, active, emission) = (operation.owner, operation.polarity, operation.bound,
            operation.next_opposite, operation.opposite_count, operation.replay, operation.emission);
        let (occurrence, cause) = (operation.occurrence.clone(), operation.cause.clone());
        let transactional = self.route_journal.is_some();
        let grew = self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.prepare_restoration_update(restoration, transactional)?;
        if grew {
            // A cold resumed route can allocate undo even at a zero-product
            // retirement. Account that retained peak before semantic mutation.
            if self.incoming_route_accounting_active { self.observe_typed_route_capacity(true)?; }
            else {
                #[cfg(test)]
                incoming_sample_trace::reason("candidate_step_bound_restoration_child-restoration-undo-growth");
                self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            }
        }
        if n == count {
            self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.retire_restoration(restoration, transactional);
            return Ok(Some(emission));
        }
        if let Some(replay) = active {
            self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.validate_restoration_replay(restoration, replay)?;
            if retain_child_step {
                let step = self.candidate_context_step_replay_child(replay, &occurrence, &cause)?;
                if step == candidate_context::ReplayChildStep::More
                    || !self.candidate_context_replay_returned(replay)? { return Ok(None); }
            } else {
                if self.candidate_context_drive_replay(replay, Some((&occurrence, &cause)))?
                    != candidate_context::ReplayDriveOutcome::Complete {
                    return Err(SolveAvailabilityError::IdentityExhausted);
                }
            }
            self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.advance_restoration(restoration, transactional);
            return Ok(None);
        }
        // Re-read the live canonical owner at the saved index; earlier
        // children may append bounds or redirect its representative.
        let owner = self.canonical_extrusion(owner);
        let bound = self.canonical_extrusion(bound);
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
        let replay = self.candidate_context_begin_replay(lower_input, upper_input, task, true)?;
        self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.set_restoration_replay(restoration, replay);
        Ok(None)
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
            let replay = self.candidate_context_begin_replay(lower_input, upper_input, task, false)?;
            self.candidate_context_drive_replay(replay, None)?;
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
