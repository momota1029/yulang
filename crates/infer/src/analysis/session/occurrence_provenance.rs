use super::*;

use crate::constraints::explain::{PortableProvenanceExportBudget, PortableProvenanceExportRoot};
use crate::constraints::{
    BoundDirection, GeneralizationParent, GeneralizedWitnessRole, OccurrenceProvenanceRoot,
    PendingOccurrenceProvenance,
};
use poly::provenance::{
    OccurrenceProvenance, PortableByteRange, PortableSourceLocation, ProvenanceCompleteness,
    SubtypeProvenanceMetrics, SubtypeProvenanceSidecar, TypeOccurrenceKey, TypeOccurrenceOwner,
    TypeOccurrenceProvenanceTable, TypeOccurrenceRole, TypePositionIndex,
};

impl AnalysisSession {
    pub(crate) fn register_type_occurrence_bounds(
        &mut self,
        key: TypeOccurrenceKey,
        var: TypeVar,
        direction: BoundDirection,
        fresh_source_parent: Option<DefId>,
    ) {
        let Some(bounds) = self.infer.constraints().bounds().of(var) else {
            return;
        };
        let ids = match direction {
            BoundDirection::Lower => bounds.lower_record_ids(),
            BoundDirection::Upper => bounds.upper_record_ids(),
        }
        .to_vec();
        self.register_type_occurrence_roots(
            key,
            ids.into_iter().map(OccurrenceProvenanceRoot::Bound),
            crate::constraints::ProvenanceCompleteness::Complete,
            fresh_source_parent,
        );
    }

    pub(crate) fn register_type_occurrence_roots(
        &mut self,
        key: TypeOccurrenceKey,
        roots: impl IntoIterator<Item = OccurrenceProvenanceRoot>,
        mut completeness: crate::constraints::ProvenanceCompleteness,
        fresh_source_parent: Option<DefId>,
    ) {
        if let Some(parent) = fresh_source_parent {
            self.fresh_source_occurrences.insert(key.clone());
            self.fresh_source_defs.insert(parent);
        }
        let roots = roots.into_iter().collect::<Vec<_>>();
        if roots.is_empty() {
            completeness = crate::constraints::ProvenanceCompleteness::Incomplete;
        }
        let entry = self
            .type_occurrence_provenance
            .entry(key)
            .or_insert_with(|| PendingOccurrenceProvenance {
                roots: Vec::new(),
                completeness,
            });
        for root in roots {
            if !entry.roots.contains(&root) {
                entry.roots.push(root);
            }
        }
        if completeness == crate::constraints::ProvenanceCompleteness::Incomplete {
            entry.completeness = crate::constraints::ProvenanceCompleteness::Incomplete;
        }
    }

    pub(crate) fn build_subtype_provenance_sidecar(&self) -> SubtypeProvenanceSidecar {
        let mut pending = self
            .type_occurrence_provenance
            .iter()
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect::<Vec<_>>();
        self.append_generalized_occurrences(&mut pending);
        let mut merged = Vec::<(TypeOccurrenceKey, PendingOccurrenceProvenance)>::new();
        let mut merged_index = FxHashMap::<TypeOccurrenceKey, usize>::default();
        for (key, provenance) in pending {
            if let Some(index) = merged_index.get(&key).copied() {
                let existing = &mut merged[index].1;
                for root in provenance.roots {
                    if !existing.roots.contains(&root) {
                        existing.roots.push(root);
                    }
                }
                if provenance.completeness == crate::constraints::ProvenanceCompleteness::Incomplete
                {
                    existing.completeness = crate::constraints::ProvenanceCompleteness::Incomplete;
                }
            } else {
                merged_index.insert(key.clone(), merged.len());
                merged.push((key, provenance));
            }
        }
        let mut pending = merged;
        let def_parents = def_parent_map(&self.poly);
        pending.sort_by_key(|(key, _)| {
            occurrence_export_sort_key(
                key,
                self.is_fresh_source_occurrence(key, &def_parents),
            )
        });

        let mut roots = Vec::new();
        let mut ranges = Vec::with_capacity(pending.len());
        for (_, provenance) in &pending {
            let start = roots.len();
            roots.extend(provenance.roots.iter().map(|root| match root {
                OccurrenceProvenanceRoot::Constraint(id) => {
                    PortableProvenanceExportRoot::Constraint(*id)
                }
                OccurrenceProvenanceRoot::Bound(id) => PortableProvenanceExportRoot::Bound(*id),
            }));
            ranges.push(start..roots.len());
        }

        if roots.is_empty() {
            return SubtypeProvenanceSidecar::empty();
        }
        let export = self
            .infer
            .constraints()
            .export_portable_provenance(
                &roots,
                PortableProvenanceExportBudget::default(),
                |boundary, kind| {
                    let span = match kind {
                        crate::constraints::ConstraintOriginKind::ApplicationArgument => self
                            .source_boundary_provenance
                            .application_argument(boundary)
                            .map(|provenance| &provenance.argument_span),
                        crate::constraints::ConstraintOriginKind::Pattern => {
                            self.source_boundary_provenance.pattern(boundary)
                        }
                        crate::constraints::ConstraintOriginKind::BodyRequirement(_) => self
                            .source_boundary_provenance
                            .body_requirement(boundary)
                            .map(|provenance| &provenance.use_span),
                        _ => None,
                    }?;
                    Some(PortableSourceLocation {
                        module: span
                            .file
                            .segments
                            .iter()
                            .map(|name| name.0.clone())
                            .collect(),
                        range: PortableByteRange {
                            start: u32::try_from(span.range.start).ok()?,
                            end: u32::try_from(span.range.end).ok()?,
                        },
                    })
                },
            )
            .expect("registered occurrence roots belong to this constraint session");

        let mut occurrences = TypeOccurrenceProvenanceTable::default();
        for ((key, pending), range) in pending.into_iter().zip(ranges) {
            let anchors = export.root_anchors[range]
                .iter()
                .copied()
                .flatten()
                .collect::<Vec<_>>();
            let complete = pending.completeness
                == crate::constraints::ProvenanceCompleteness::Complete
                && anchors.len() == pending.roots.len()
                && anchors.iter().all(|anchor| {
                    export.snapshot.anchor(*anchor).is_some_and(|record| {
                        record.completeness == ProvenanceCompleteness::Complete
                    })
                });
            occurrences.insert(
                key,
                OccurrenceProvenance {
                    anchors,
                    completeness: if complete {
                        ProvenanceCompleteness::Complete
                    } else {
                        ProvenanceCompleteness::Incomplete
                    },
                },
            );
        }
        let complete_occurrences = occurrences
            .iter()
            .filter(|(_, provenance)| provenance.completeness == ProvenanceCompleteness::Complete)
            .count();
        let metrics = SubtypeProvenanceMetrics {
            occurrence_count: occurrences.len(),
            anchor_count: occurrences
                .iter()
                .map(|(_, provenance)| provenance.anchors.len())
                .sum(),
            complete_occurrences,
            incomplete_occurrences: occurrences.len().saturating_sub(complete_occurrences),
            snapshot_nodes: export.snapshot.nodes().len(),
            snapshot_edges: export.snapshot.edges().len(),
            snapshot_logical_bytes: export.snapshot.logical_bytes_proxy(),
        };
        SubtypeProvenanceSidecar {
            snapshot: export.snapshot,
            occurrences,
            metrics,
        }
    }

    fn is_fresh_source_occurrence(
        &self,
        key: &TypeOccurrenceKey,
        def_parents: &FxHashMap<DefId, DefId>,
    ) -> bool {
        if self.fresh_source_occurrences.contains(key) {
            return true;
        }
        let TypeOccurrenceOwner::Definition(mut def) = key.owner else {
            return false;
        };
        loop {
            if self.fresh_source_defs.contains(&def) {
                return true;
            }
            let Some(parent) = def_parents.get(&def).copied() else {
                return false;
            };
            def = parent;
        }
    }

    fn append_generalized_occurrences(
        &self,
        pending: &mut Vec<(TypeOccurrenceKey, PendingOccurrenceProvenance)>,
    ) {
        let machine = self.infer.constraints();
        for (_, scheme) in machine.generalized_scheme_records_iter() {
            for witness_id in &scheme.witnesses {
                let Some(witness) = machine.generalized_scheme_witness(*witness_id) else {
                    continue;
                };
                let role = match witness.role {
                    GeneralizedWitnessRole::RecursiveLowerBound => {
                        TypeOccurrenceRole::DefinitionRecursiveLower(TypePositionIndex::from_usize(
                            0,
                        ))
                    }
                    GeneralizedWitnessRole::RecursiveUpperBound => {
                        TypeOccurrenceRole::DefinitionRecursiveUpper(TypePositionIndex::from_usize(
                            0,
                        ))
                    }
                    _ => TypeOccurrenceRole::DefinitionPredicate,
                };
                let mut roots = Vec::new();
                for derivation in &witness.incoming {
                    for parent in &derivation.parents {
                        let root = match parent {
                            GeneralizationParent::Constraint(id) => {
                                OccurrenceProvenanceRoot::Constraint(*id)
                            }
                            GeneralizationParent::Bound(id) => OccurrenceProvenanceRoot::Bound(*id),
                        };
                        if !roots.contains(&root) {
                            roots.push(root);
                        }
                    }
                }
                pending.push((
                    TypeOccurrenceKey {
                        owner: TypeOccurrenceOwner::Definition(scheme.owner),
                        role,
                        path: witness.path.to_type_position_path(),
                    },
                    PendingOccurrenceProvenance {
                        roots,
                        completeness: witness.completeness,
                    },
                ));
            }
        }
    }
}

fn occurrence_export_sort_key(
    key: &TypeOccurrenceKey,
    is_fresh_source: bool,
) -> (bool, Vec<u32>) {
    (!is_fresh_source, occurrence_sort_key(key))
}

fn occurrence_sort_key(key: &TypeOccurrenceKey) -> Vec<u32> {
    let mut out = match key.owner {
        TypeOccurrenceOwner::Definition(id) => vec![0, id.0],
        TypeOccurrenceOwner::Expression(id) => vec![1, id.0],
        TypeOccurrenceOwner::Pattern(id) => vec![2, id.0],
    };
    match key.role {
        TypeOccurrenceRole::DefinitionPredicate => out.push(0),
        TypeOccurrenceRole::DefinitionRecursiveLower(index) => {
            out.extend([1, index.index() as u32]);
        }
        TypeOccurrenceRole::DefinitionRecursiveUpper(index) => {
            out.extend([2, index.index() as u32]);
        }
        TypeOccurrenceRole::ExpressionActual => out.push(3),
        TypeOccurrenceRole::ExpressionExpected => out.push(4),
        TypeOccurrenceRole::PatternInput => out.push(5),
        TypeOccurrenceRole::PatternRequirement => out.push(6),
    }
    out.push(u32::try_from(key.path.depth()).unwrap_or(u32::MAX));
    out.extend(key.path.0.iter().flat_map(path_step_sort_key));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_source_occurrence_precedes_dependency_under_small_anchor_budget() {
        const MAX_ANCHORS: usize = 1;
        let dependency = TypeOccurrenceKey {
            owner: TypeOccurrenceOwner::Definition(DefId(0)),
            role: TypeOccurrenceRole::DefinitionPredicate,
            path: Default::default(),
        };
        let fresh = TypeOccurrenceKey {
            owner: TypeOccurrenceOwner::Expression(poly::expr::ExprId(99)),
            role: TypeOccurrenceRole::ExpressionActual,
            path: Default::default(),
        };
        let mut competing = vec![(dependency.clone(), false), (fresh.clone(), true)];
        competing.sort_by_key(|(key, is_fresh)| occurrence_export_sort_key(key, *is_fresh));

        let retained = competing
            .into_iter()
            .take(MAX_ANCHORS)
            .map(|(key, _)| key)
            .collect::<Vec<_>>();
        assert_eq!(retained, vec![fresh]);
    }
}

fn path_step_sort_key(step: &poly::provenance::TypePositionStep) -> Vec<u32> {
    use poly::provenance::TypePositionStep;
    match *step {
        TypePositionStep::FunctionArgument => vec![0],
        TypePositionStep::FunctionArgumentEffect => vec![1],
        TypePositionStep::FunctionReturnEffect => vec![2],
        TypePositionStep::FunctionReturn => vec![3],
        TypePositionStep::ConstructorArgument {
            alternative,
            argument,
        } => {
            vec![4, alternative.index() as u32, argument.index() as u32]
        }
        TypePositionStep::TupleElement(index) => vec![5, index.index() as u32],
        TypePositionStep::RecordField { alternative, field } => {
            vec![6, alternative.index() as u32, field.index() as u32]
        }
        TypePositionStep::VariantPayload {
            alternative,
            item,
            payload,
        } => vec![
            7,
            alternative.index() as u32,
            item.index() as u32,
            payload.index() as u32,
        ],
        TypePositionStep::RowItemArgument { item, argument } => {
            vec![8, item.index() as u32, argument.index() as u32]
        }
        TypePositionStep::RowTail => vec![9],
        TypePositionStep::RecursiveBound(index) => vec![10, index.index() as u32],
    }
}
