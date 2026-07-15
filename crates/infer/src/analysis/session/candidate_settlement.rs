use super::*;

const MAX_CANDIDATE_SETTLEMENT_PASSES: usize = 8;

/// Candidate-local proof that the late mutable pass routed this head through normal apply lanes.
///
/// These keys deliberately remain separate from the session-global cache-interface evidence. A
/// Stage 4 audit may read them only for the zero-prerequisite candidate identified by `impl_def`.
#[derive(Debug, Clone)]
pub(in crate::analysis) struct CandidateSettlementFact {
    pub(in crate::analysis) merge_constraints: FxHashSet<CompactMergeConstraintKey>,
    pub(in crate::analysis) subtype_constraints: FxHashSet<CompactSubtypeConstraintKey>,
    stable_raw_head: CompactRoleConstraint,
    stable_simplified_head: CompactRoleConstraint,
    stable_subtype_keys: FxHashSet<CompactSubtypeConstraintKey>,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CandidateSettlementSafetyWitness {
    pub(crate) binding_count_before: usize,
    pub(crate) binding_count_after: usize,
    pub(crate) typed_lets_before: usize,
    pub(crate) typed_lets_after: usize,
    pub(crate) missing_schemes_before: usize,
    pub(crate) missing_schemes_after: usize,
    pub(crate) all_binding_schemes_unchanged: bool,
    pub(crate) eligible_candidates: usize,
    pub(crate) recorded_candidates: usize,
    pub(crate) unstable_candidates: Vec<DefId>,
}

impl AnalysisSession {
    /// Settle source, zero-prerequisite candidate heads after ordinary analysis has quiesced.
    ///
    /// Each candidate gets a bounded, independent restart lane. Prerequisites are excluded before
    /// compaction, and role search is never entered. A final read-only rescan removes any fact whose
    /// exact head view was invalidated by a later candidate, which is the fail-closed policy for a
    /// shared boundary/effect binder.
    pub(crate) fn settle_source_role_impl_candidates(
        &mut self,
        source_impl_defs: impl IntoIterator<Item = DefId>,
    ) {
        if self.candidate_settlement_complete {
            return;
        }
        self.candidate_settlement_complete = true;

        #[cfg(test)]
        let schemes_before = binding_scheme_snapshot(&self.poly);

        let source_impl_defs = source_impl_defs.into_iter().collect::<FxHashSet<_>>();
        let mut eligible = self
            .role_impls
            .iter()
            .filter(|candidate| candidate.prerequisites.is_empty())
            .filter_map(|candidate| {
                let impl_def = candidate.impl_def?;
                source_impl_defs
                    .contains(&impl_def)
                    .then(|| candidate.clone())
            })
            .collect::<Vec<_>>();
        eligible.sort_by(|left, right| {
            left.impl_def
                .map(|def| def.0)
                .cmp(&right.impl_def.map(|def| def.0))
                .then_with(|| left.role.cmp(&right.role))
        });

        let mut unstable = Vec::new();
        for candidate in &eligible {
            let impl_def = candidate
                .impl_def
                .expect("eligible source candidates have an impl definition");
            let Some(fact) = self.settle_role_impl_candidate_head(candidate) else {
                unstable.push(impl_def);
                continue;
            };
            if self.candidate_settlements.insert(impl_def, fact).is_some() {
                self.candidate_settlements.remove(&impl_def);
                unstable.push(impl_def);
            }
        }

        // A later candidate may share a machine variable with an earlier one. Do not reconcile or
        // restart across candidates: retain only facts whose exact stable view still matches now.
        for candidate in &eligible {
            let impl_def = candidate
                .impl_def
                .expect("eligible source candidates have an impl definition");
            let stable = self
                .candidate_settlements
                .get(&impl_def)
                .is_some_and(|fact| self.candidate_settlement_fact_is_stable(candidate, fact));
            if !stable && self.candidate_settlements.remove(&impl_def).is_some() {
                unstable.push(impl_def);
            }
        }
        unstable.sort_by_key(|def| def.0);
        unstable.dedup();

        #[cfg(test)]
        {
            let schemes_after = binding_scheme_snapshot(&self.poly);
            let (typed_lets_before, missing_schemes_before) = scheme_counts(&schemes_before);
            let (typed_lets_after, missing_schemes_after) = scheme_counts(&schemes_after);
            self.candidate_settlement_safety_witness = Some(CandidateSettlementSafetyWitness {
                binding_count_before: schemes_before.len(),
                binding_count_after: schemes_after.len(),
                typed_lets_before,
                typed_lets_after,
                missing_schemes_before,
                missing_schemes_after,
                all_binding_schemes_unchanged: binding_scheme_snapshots_equal(
                    &schemes_before,
                    &schemes_after,
                ),
                eligible_candidates: eligible.len(),
                recorded_candidates: self.candidate_settlements.len(),
                unstable_candidates: unstable,
            });
        }
    }

    pub(in crate::analysis) fn cache_candidate_settlement_fact(
        &self,
        candidate: &crate::roles::RoleImplCandidate,
    ) -> Option<&CandidateSettlementFact> {
        if !candidate.prerequisites.is_empty() {
            return None;
        }
        self.candidate_settlements.get(&candidate.impl_def?)
    }

    #[cfg(test)]
    pub(in crate::analysis) fn candidate_settlement_safety_witness(
        &self,
    ) -> Option<&CandidateSettlementSafetyWitness> {
        self.candidate_settlement_safety_witness.as_ref()
    }

    #[cfg(test)]
    pub(in crate::analysis) fn candidate_settlement_fact_counts(
        &self,
        impl_def: DefId,
    ) -> Option<(usize, usize)> {
        self.candidate_settlements
            .get(&impl_def)
            .map(|fact| (fact.merge_constraints.len(), fact.subtype_constraints.len()))
    }

    fn settle_role_impl_candidate_head(
        &mut self,
        candidate: &crate::roles::RoleImplCandidate,
    ) -> Option<CandidateSettlementFact> {
        debug_assert!(candidate.prerequisites.is_empty());
        let mut applied_merge_constraints = FxHashSet::default();
        let mut applied_subtype_constraints = FxHashSet::default();

        for _ in 0..MAX_CANDIDATE_SETTLEMENT_PASSES {
            let (raw_head, merge_constraints) = compact_role_constraint_recording_merge_constraints(
                self.infer.constraints(),
                &candidate.as_constraint(),
            );
            if apply_compact_merge_constraints(
                self.infer.constraints_mut(),
                merge_constraints,
                &mut applied_merge_constraints,
            ) {
                self.route_constraint_events();
                continue;
            }

            let mut root = CompactRoot::default();
            let mut roles = vec![raw_head.clone()];
            crate::analysis::cache_interface::simplify_cache_candidate_component(
                self.infer.constraints(),
                &mut root,
                &mut roles,
            );
            let simplified_head = roles
                .pop()
                .expect("candidate settlement always retains its head carrier");
            let subtype_constraints = collect_interval_dominance_constraints_with_metrics(
                &root,
                &[simplified_head.clone()],
            )
            .0;
            let stable_subtype_keys = compact_subtype_constraint_keys(&subtype_constraints);
            if apply_compact_subtype_constraints(
                self.infer.constraints_mut(),
                subtype_constraints,
                &mut applied_subtype_constraints,
            ) {
                self.route_constraint_events();
                continue;
            }

            return Some(CandidateSettlementFact {
                merge_constraints: applied_merge_constraints,
                subtype_constraints: applied_subtype_constraints,
                stable_raw_head: raw_head,
                stable_simplified_head: simplified_head,
                stable_subtype_keys,
            });
        }
        None
    }

    fn candidate_settlement_fact_is_stable(
        &self,
        candidate: &crate::roles::RoleImplCandidate,
        fact: &CandidateSettlementFact,
    ) -> bool {
        if !candidate.prerequisites.is_empty() {
            return false;
        }
        let (raw_head, merge_constraints) = compact_role_constraint_recording_merge_constraints(
            self.infer.constraints(),
            &candidate.as_constraint(),
        );
        if raw_head != fact.stable_raw_head
            || unapplied_compact_merge_constraint_count(&merge_constraints, &fact.merge_constraints)
                != 0
        {
            return false;
        }

        let mut root = CompactRoot::default();
        let mut roles = vec![raw_head];
        crate::analysis::cache_interface::simplify_cache_candidate_component(
            self.infer.constraints(),
            &mut root,
            &mut roles,
        );
        let Some(simplified_head) = roles.pop() else {
            return false;
        };
        if simplified_head != fact.stable_simplified_head {
            return false;
        }
        let subtype_constraints =
            collect_interval_dominance_constraints_with_metrics(&root, &[simplified_head]).0;
        compact_subtype_constraint_keys(&subtype_constraints) == fact.stable_subtype_keys
            && unapplied_compact_subtype_constraint_count(
                &subtype_constraints,
                &fact.subtype_constraints,
            ) == 0
    }
}

#[cfg(test)]
fn binding_scheme_snapshot(poly: &PolyArena) -> Vec<(DefId, Option<Scheme>)> {
    let mut schemes = poly
        .defs
        .iter()
        .filter_map(|(def, item)| match item {
            Def::Let { scheme, .. } => Some((def, scheme.clone())),
            Def::Mod { .. } | Def::Arg => None,
        })
        .collect::<Vec<_>>();
    schemes.sort_by_key(|(def, _)| def.0);
    schemes
}

#[cfg(test)]
fn scheme_counts(schemes: &[(DefId, Option<Scheme>)]) -> (usize, usize) {
    let typed = schemes
        .iter()
        .filter(|(_, scheme)| scheme.is_some())
        .count();
    (typed, schemes.len().saturating_sub(typed))
}

#[cfg(test)]
fn binding_scheme_snapshots_equal(
    before: &[(DefId, Option<Scheme>)],
    after: &[(DefId, Option<Scheme>)],
) -> bool {
    before.len() == after.len()
        && before
            .iter()
            .zip(after)
            .all(|((before_def, before), (after_def, after))| {
                before_def == after_def
                    && match (before, after) {
                        (None, None) => true,
                        (Some(before), Some(after)) => {
                            before.quantifiers == after.quantifiers
                                && before.role_predicates == after.role_predicates
                                && before.recursive_bounds == after.recursive_bounds
                                && before.stack_quantifiers == after.stack_quantifiers
                                && before.predicate == after.predicate
                        }
                        (None, Some(_)) | (Some(_), None) => false,
                    }
            })
}
