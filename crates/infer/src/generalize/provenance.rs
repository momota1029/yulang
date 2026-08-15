//! Exact canonical-parent projection for finalized same-session structural positions.
//!
//! PUSP-C records only mappings it can prove from canonical bound iteration. This initial capture
//! follows only paths whose already-selected compact structure preserves an exact output position.
//! Unsupported or ambiguous structural transformations remain incomplete; they never receive a
//! whole-definition fallback parent set.

use rustc_hash::FxHashSet;

use super::*;
use crate::constraints::proof::ProjectionEvaluationRound;
use crate::constraints::{
    BoundRecordId, GeneralizationDerivation, GeneralizationDerivationRule, GeneralizationParent,
    GeneralizedTypePath, GeneralizedTypePathStep, GeneralizedWitnessDraft, GeneralizedWitnessRole,
    ProofFailure, ProvenanceCompleteness, SchemeProjectableLowerReason,
    ScopedLegacyProjectionQuery, StructuralIndex,
};

const MAX_WITNESSES_PER_SCHEME: usize = 128;
const MAX_INCOMING_EDGES_PER_SCHEME: usize = 256;
const MAX_GENERALIZED_PATH_DEPTH: usize = 16;

pub(crate) fn capture_generalized_witnesses(
    machine: &mut ConstraintMachine,
    root: TypeVar,
    generalized: &GeneralizedCompactRoot,
) -> (Vec<GeneralizedWitnessDraft>, ProvenanceCompleteness) {
    let mut round_state = machine.new_projection_evaluation_round();
    machine
        .with_legacy_projection_query(&mut round_state, |query| {
            let mut collector = WitnessCollector::new(&query);
            collector.collect_var(root, true, GeneralizedTypePath::default(), None)?;
            collector.drafts.retain_mut(|draft| {
                if function_argument_only(&draft.path) {
                    return structural_path_survives(&generalized.compact.root, &draft.path);
                }
                if !structural_path_survives(&generalized.compact.root, &draft.path) {
                    draft.completeness = ProvenanceCompleteness::Incomplete;
                }
                true
            });

            let sandwich_incomplete = !generalized.sandwiches.is_empty();
            if sandwich_incomplete {
                for draft in &mut collector.drafts {
                    draft.completeness = ProvenanceCompleteness::Incomplete;
                }
            }
            for (index, _) in generalized.compact.rec_vars.iter().enumerate() {
                let path = GeneralizedTypePath(vec![GeneralizedTypePathStep::RecursiveBound(
                    StructuralIndex::from_usize(index),
                )]);
                collector.drafts.push(GeneralizedWitnessDraft {
                    path: path.clone(),
                    role: GeneralizedWitnessRole::RecursiveLowerBound,
                    incoming: Vec::new(),
                    completeness: ProvenanceCompleteness::Incomplete,
                });
                collector.drafts.push(GeneralizedWitnessDraft {
                    path,
                    role: GeneralizedWitnessRole::RecursiveUpperBound,
                    incoming: Vec::new(),
                    completeness: ProvenanceCompleteness::Incomplete,
                });
            }

            // PUSP-C deliberately does not claim complete whole-scheme coverage until every
            // structural compact transformation has a parallel projection. Individual argument
            // witnesses remain complete when their exact path did not cross a sandwich or the
            // storage budget.
            let scheme_completeness = ProvenanceCompleteness::Incomplete;
            let drafts = std::mem::take(&mut collector.drafts);
            drop(collector);
            Ok(query.complete((drafts, scheme_completeness)))
        })
        // This value is an attempt-local poison only. The gateway records every organically
        // reachable denial in the same machine's terminal latch before returning the error.
        .unwrap_or((Vec::new(), ProvenanceCompleteness::Incomplete))
}

struct WitnessCollector<'scope, 'query> {
    query: &'scope ScopedLegacyProjectionQuery<'query>,
    projection_round: ProjectionEvaluationRound<'scope>,
    drafts: Vec<GeneralizedWitnessDraft>,
    visiting: FxHashSet<(TypeVar, bool)>,
    incoming_edges: usize,
    truncated: bool,
}

#[derive(Clone, Copy)]
enum WitnessParents<'a> {
    Bound(BoundRecordId),
    Selected(&'a [GeneralizationParent]),
}

impl<'a> From<BoundRecordId> for WitnessParents<'a> {
    fn from(record: BoundRecordId) -> Self {
        Self::Bound(record)
    }
}

impl<'scope, 'query> WitnessCollector<'scope, 'query> {
    fn new(query: &'scope ScopedLegacyProjectionQuery<'query>) -> Self {
        Self {
            query,
            projection_round: ProjectionEvaluationRound::new(),
            drafts: Vec::new(),
            visiting: FxHashSet::default(),
            incoming_edges: 0,
            truncated: false,
        }
    }

    fn add<'parents>(
        &mut self,
        path: &GeneralizedTypePath,
        role: GeneralizedWitnessRole,
        parents: impl Into<WitnessParents<'parents>>,
    ) {
        match parents.into() {
            WitnessParents::Bound(record) => {
                self.add_parent(path, role, GeneralizationParent::Bound(record));
            }
            WitnessParents::Selected(parents) => {
                // An empty qualified selection means the formula proved this lower relation but
                // no direct support currently contributes provenance. Keep it parentless rather
                // than fabricating the raw Bound(record) parent used by an unclaimed relation.
                for parent in parents {
                    self.add_parent(path, role, parent.clone());
                }
            }
        }
    }

    fn add_parent(
        &mut self,
        path: &GeneralizedTypePath,
        role: GeneralizedWitnessRole,
        parent: GeneralizationParent,
    ) {
        if self.truncated {
            return;
        }
        let edge = GeneralizationDerivation {
            rule: GeneralizationDerivationRule::BoundCollection,
            parents: vec![parent],
        };
        if let Some(draft) = self
            .drafts
            .iter_mut()
            .find(|draft| draft.path == *path && draft.role == role)
        {
            // Keep duplicate candidates until arena insertion so the storage metrics can distinguish
            // considered edges from the canonical deduplicated set. This remains a flat edge list,
            // never a list of transitive proof paths.
            if self.incoming_edges >= MAX_INCOMING_EDGES_PER_SCHEME {
                draft.completeness = ProvenanceCompleteness::Incomplete;
                self.truncated = true;
            } else {
                draft.incoming.push(edge);
                self.incoming_edges += 1;
            }
            return;
        }
        if self.drafts.len() >= MAX_WITNESSES_PER_SCHEME
            || self.incoming_edges >= MAX_INCOMING_EDGES_PER_SCHEME
        {
            self.truncated = true;
            return;
        }
        self.drafts.push(GeneralizedWitnessDraft {
            path: path.clone(),
            role,
            incoming: vec![edge],
            completeness: ProvenanceCompleteness::Complete,
        });
        self.incoming_edges += 1;
    }

    fn mark_incomplete(&mut self, path: &GeneralizedTypePath, role: GeneralizedWitnessRole) {
        if let Some(draft) = self
            .drafts
            .iter_mut()
            .find(|draft| draft.path == *path && draft.role == role)
        {
            draft.completeness = ProvenanceCompleteness::Incomplete;
            return;
        }
        if self.drafts.len() >= MAX_WITNESSES_PER_SCHEME {
            self.truncated = true;
            return;
        }
        self.drafts.push(GeneralizedWitnessDraft {
            path: path.clone(),
            role,
            incoming: Vec::new(),
            completeness: ProvenanceCompleteness::Incomplete,
        });
    }

    fn collect_var(
        &mut self,
        var: TypeVar,
        positive: bool,
        path: GeneralizedTypePath,
        structural_parent: Option<WitnessParents<'_>>,
    ) -> Result<(), ProofFailure> {
        if self.truncated || path.depth() > MAX_GENERALIZED_PATH_DEPTH {
            self.truncated = true;
            return Ok(());
        }
        if let Some(parent) = structural_parent {
            self.add(&path, GeneralizedWitnessRole::ConstraintRelation, parent);
        }
        if !self.visiting.insert((var, positive)) {
            return Ok(());
        }
        if positive {
            let entries = self
                .query
                .scheme_projectable_lowers_in_scope(var, &mut self.projection_round)?
                .into_iter()
                .map(|entry| {
                    (
                        entry.record,
                        entry.bound.pos,
                        entry.reason,
                        entry.projection_evidence,
                    )
                })
                .collect::<Vec<_>>();
            for (record, endpoint, reason, projection_evidence) in entries {
                match reason {
                    SchemeProjectableLowerReason::Unclaimed => {
                        self.add(&path, GeneralizedWitnessRole::LowerBound, record);
                        self.collect_pos(endpoint, path.clone(), WitnessParents::Bound(record))?;
                    }
                    SchemeProjectableLowerReason::Qualified {
                        uncovered_claims: _,
                        independent_supports,
                    } => {
                        let evidence = projection_evidence.expect(
                            "qualified projection lower must carry its evaluation evidence",
                        );
                        let mut parents = Vec::new();
                        let fail_open = match evidence {
                            crate::constraints::proof::ProjectionEvidence::DecisiveClaimedArm(
                                proof,
                            ) => {
                                parents.push(GeneralizationParent::BoundClaimProjectionProof {
                                    bound: record,
                                    coverage_root: proof.coverage_root(),
                                    representative_claim: proof.representative_claim(),
                                    proof: Box::new(proof),
                                });
                                false
                            }
                            crate::constraints::proof::ProjectionEvidence::ExactWithoutClaimedArm => {
                                false
                            }
                            crate::constraints::proof::ProjectionEvidence::FailOpenIncomplete => {
                                true
                            }
                        };
                        parents.extend(independent_supports.into_iter().map(|carrier| {
                            GeneralizationParent::BoundProjectionProof {
                                bound: record,
                                carrier,
                            }
                        }));
                        let parents = WitnessParents::Selected(&parents);
                        self.add(&path, GeneralizedWitnessRole::LowerBound, parents);
                        if fail_open {
                            self.mark_incomplete(&path, GeneralizedWitnessRole::LowerBound);
                        }
                        self.collect_pos(endpoint, path.clone(), parents)?;
                    }
                }
            }
        } else {
            let entries = self.query.projection_upper_records_in_scope(var);
            for (record, bound) in entries {
                self.add(&path, GeneralizedWitnessRole::UpperBound, record);
                self.collect_neg(bound.neg, path.clone(), record)?;
            }
        }
        self.visiting.remove(&(var, positive));
        Ok(())
    }

    fn collect_pos(
        &mut self,
        id: PosId,
        path: GeneralizedTypePath,
        parent: WitnessParents<'_>,
    ) -> Result<(), ProofFailure> {
        match self.query.pos_shape_in_scope(id) {
            Pos::Var(var) => self.collect_var(var, true, path, Some(parent)),
            Pos::Con(_, args) => self.collect_neu_items(
                &args,
                &path,
                |argument| GeneralizedTypePathStep::ConstructorArgument {
                    alternative: StructuralIndex::from_usize(0),
                    argument,
                },
                parent,
            ),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_neg(
                    arg,
                    child(&path, GeneralizedTypePathStep::FunctionArgument),
                    parent,
                )?;
                // The shipped PUSP graph exposes only the root function argument. Adding root
                // return/effect witnesses would change existing bounded-query topology. Nested
                // function positions are new structural positions and can be captured inertly.
                if path.depth() != 0 {
                    self.collect_neg(
                        arg_eff,
                        child(&path, GeneralizedTypePathStep::FunctionArgumentEffect),
                        parent,
                    )?;
                    self.collect_pos(
                        ret_eff,
                        child(&path, GeneralizedTypePathStep::FunctionReturnEffect),
                        parent,
                    )?;
                    self.collect_pos(
                        ret,
                        child(&path, GeneralizedTypePathStep::FunctionReturn),
                        parent,
                    )?;
                }
                Ok(())
            }
            Pos::Record(fields)
            | Pos::RecordTailSpread { fields, .. }
            | Pos::RecordHeadSpread { fields, .. } => {
                for (field, value) in fields.into_iter().enumerate() {
                    self.collect_pos(
                        value.value,
                        child(
                            &path,
                            GeneralizedTypePathStep::RecordField {
                                alternative: StructuralIndex::from_usize(0),
                                field: StructuralIndex::from_usize(field),
                            },
                        ),
                        parent,
                    )?;
                }
                Ok(())
            }
            Pos::PolyVariant(items) => {
                for (item, (_, payloads)) in items.into_iter().enumerate() {
                    for (payload, value) in payloads.into_iter().enumerate() {
                        self.collect_pos(
                            value,
                            child(
                                &path,
                                GeneralizedTypePathStep::VariantPayload {
                                    alternative: StructuralIndex::from_usize(0),
                                    item: StructuralIndex::from_usize(item),
                                    payload: StructuralIndex::from_usize(payload),
                                },
                            ),
                            parent,
                        )?;
                    }
                }
                Ok(())
            }
            Pos::Tuple(items) => {
                for (index, value) in items.into_iter().enumerate() {
                    self.collect_pos(
                        value,
                        child(
                            &path,
                            GeneralizedTypePathStep::TupleElement(StructuralIndex::from_usize(
                                index,
                            )),
                        ),
                        parent,
                    )?;
                }
                Ok(())
            }
            Pos::Row(items) => self.collect_pos_row_items(&items, &path, parent),
            Pos::Union(lhs, rhs) => {
                self.collect_pos(lhs, path.clone(), parent)?;
                self.collect_pos(rhs, path, parent)
            }
            Pos::NonSubtract(inner, _) | Pos::Stack { inner, .. } => {
                self.collect_pos(inner, path, parent)
            }
            _ => Ok(()),
        }
    }

    fn collect_neg<'parents>(
        &mut self,
        id: NegId,
        path: GeneralizedTypePath,
        parent: impl Into<WitnessParents<'parents>>,
    ) -> Result<(), ProofFailure> {
        let parent = parent.into();
        match self.query.neg_shape_in_scope(id) {
            Neg::Var(var) => self.collect_var(var, false, path, Some(parent)),
            Neg::Con(_, args) => self.collect_neu_items(
                &args,
                &path,
                |argument| GeneralizedTypePathStep::ConstructorArgument {
                    alternative: StructuralIndex::from_usize(0),
                    argument,
                },
                parent,
            ),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_pos(
                    arg,
                    child(&path, GeneralizedTypePathStep::FunctionArgument),
                    parent,
                )?;
                if path.depth() != 0 {
                    self.collect_pos(
                        arg_eff,
                        child(&path, GeneralizedTypePathStep::FunctionArgumentEffect),
                        parent,
                    )?;
                    self.collect_neg(
                        ret_eff,
                        child(&path, GeneralizedTypePathStep::FunctionReturnEffect),
                        parent,
                    )?;
                    self.collect_neg(
                        ret,
                        child(&path, GeneralizedTypePathStep::FunctionReturn),
                        parent,
                    )?;
                }
                Ok(())
            }
            Neg::Record(fields) => {
                for (field, value) in fields.into_iter().enumerate() {
                    self.collect_neg(
                        value.value,
                        child(
                            &path,
                            GeneralizedTypePathStep::RecordField {
                                alternative: StructuralIndex::from_usize(0),
                                field: StructuralIndex::from_usize(field),
                            },
                        ),
                        parent,
                    )?;
                }
                Ok(())
            }
            Neg::PolyVariant(items) => {
                for (item, (_, payloads)) in items.into_iter().enumerate() {
                    for (payload, value) in payloads.into_iter().enumerate() {
                        self.collect_neg(
                            value,
                            child(
                                &path,
                                GeneralizedTypePathStep::VariantPayload {
                                    alternative: StructuralIndex::from_usize(0),
                                    item: StructuralIndex::from_usize(item),
                                    payload: StructuralIndex::from_usize(payload),
                                },
                            ),
                            parent,
                        )?;
                    }
                }
                Ok(())
            }
            Neg::Tuple(items) => {
                for (index, value) in items.into_iter().enumerate() {
                    self.collect_neg(
                        value,
                        child(
                            &path,
                            GeneralizedTypePathStep::TupleElement(StructuralIndex::from_usize(
                                index,
                            )),
                        ),
                        parent,
                    )?;
                }
                Ok(())
            }
            Neg::Row(items, tail) => {
                self.collect_neg_row_items(&items, &path, parent)?;
                self.collect_neg(tail, child(&path, GeneralizedTypePathStep::RowTail), parent)
            }
            Neg::Intersection(lhs, rhs) => {
                self.collect_neg(lhs, path.clone(), parent)?;
                self.collect_neg(rhs, path, parent)
            }
            Neg::Stack { inner, .. } => self.collect_neg(inner, path, parent),
            _ => Ok(()),
        }
    }

    fn collect_neu(
        &mut self,
        id: NeuId,
        path: GeneralizedTypePath,
        parent: WitnessParents<'_>,
    ) -> Result<(), ProofFailure> {
        match self.query.neu_shape_in_scope(id) {
            Neu::Bounds(lower, upper) => {
                self.collect_pos(lower, path.clone(), parent)?;
                self.collect_neg(upper, path, parent)
            }
            Neu::Con(_, args) => self.collect_neu_items(
                &args,
                &path,
                |argument| GeneralizedTypePathStep::ConstructorArgument {
                    alternative: StructuralIndex::from_usize(0),
                    argument,
                },
                parent,
            ),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_neu(
                    arg,
                    child(&path, GeneralizedTypePathStep::FunctionArgument),
                    parent,
                )?;
                if path.depth() != 0 {
                    self.collect_neu(
                        arg_eff,
                        child(&path, GeneralizedTypePathStep::FunctionArgumentEffect),
                        parent,
                    )?;
                    self.collect_neu(
                        ret_eff,
                        child(&path, GeneralizedTypePathStep::FunctionReturnEffect),
                        parent,
                    )?;
                    self.collect_neu(
                        ret,
                        child(&path, GeneralizedTypePathStep::FunctionReturn),
                        parent,
                    )?;
                }
                Ok(())
            }
            Neu::Record(fields) => {
                for (field, value) in fields.into_iter().enumerate() {
                    self.collect_neu(
                        value.value,
                        child(
                            &path,
                            GeneralizedTypePathStep::RecordField {
                                alternative: StructuralIndex::from_usize(0),
                                field: StructuralIndex::from_usize(field),
                            },
                        ),
                        parent,
                    )?;
                }
                Ok(())
            }
            Neu::PolyVariant(items) => {
                for (item, (_, payloads)) in items.into_iter().enumerate() {
                    for (payload, value) in payloads.into_iter().enumerate() {
                        self.collect_neu(
                            value,
                            child(
                                &path,
                                GeneralizedTypePathStep::VariantPayload {
                                    alternative: StructuralIndex::from_usize(0),
                                    item: StructuralIndex::from_usize(item),
                                    payload: StructuralIndex::from_usize(payload),
                                },
                            ),
                            parent,
                        )?;
                    }
                }
                Ok(())
            }
            Neu::Tuple(items) => {
                for (index, value) in items.into_iter().enumerate() {
                    self.collect_neu(
                        value,
                        child(
                            &path,
                            GeneralizedTypePathStep::TupleElement(StructuralIndex::from_usize(
                                index,
                            )),
                        ),
                        parent,
                    )?;
                }
                Ok(())
            }
        }
    }

    fn collect_neu_items(
        &mut self,
        items: &[NeuId],
        path: &GeneralizedTypePath,
        step: impl Fn(StructuralIndex) -> GeneralizedTypePathStep,
        parent: WitnessParents<'_>,
    ) -> Result<(), ProofFailure> {
        for (index, item) in items.iter().copied().enumerate() {
            self.collect_neu(
                item,
                child(path, step(StructuralIndex::from_usize(index))),
                parent,
            )?;
        }
        Ok(())
    }

    fn collect_pos_row_items(
        &mut self,
        items: &[PosId],
        path: &GeneralizedTypePath,
        parent: WitnessParents<'_>,
    ) -> Result<(), ProofFailure> {
        for (item, id) in items.iter().copied().enumerate() {
            if let Pos::Con(_, args) = self.query.pos_shape_in_scope(id) {
                for (argument, value) in args.into_iter().enumerate() {
                    self.collect_neu(
                        value,
                        child(
                            path,
                            GeneralizedTypePathStep::RowItemArgument {
                                item: StructuralIndex::from_usize(item),
                                argument: StructuralIndex::from_usize(argument),
                            },
                        ),
                        parent,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn collect_neg_row_items(
        &mut self,
        items: &[NegId],
        path: &GeneralizedTypePath,
        parent: WitnessParents<'_>,
    ) -> Result<(), ProofFailure> {
        for (item, id) in items.iter().copied().enumerate() {
            if let Neg::Con(_, args) = self.query.neg_shape_in_scope(id) {
                for (argument, value) in args.into_iter().enumerate() {
                    self.collect_neu(
                        value,
                        child(
                            path,
                            GeneralizedTypePathStep::RowItemArgument {
                                item: StructuralIndex::from_usize(item),
                                argument: StructuralIndex::from_usize(argument),
                            },
                        ),
                        parent,
                    )?;
                }
            }
        }
        Ok(())
    }
}

fn child(path: &GeneralizedTypePath, step: GeneralizedTypePathStep) -> GeneralizedTypePath {
    let mut path = path.clone();
    path.push(step);
    path
}

fn function_argument_only(path: &GeneralizedTypePath) -> bool {
    path.0
        .iter()
        .all(|step| *step == GeneralizedTypePathStep::FunctionArgument)
}

enum CompactPosition<'a> {
    Type(&'a CompactType),
    Bounds(&'a CompactBounds),
}

fn structural_path_survives(root: &CompactType, path: &GeneralizedTypePath) -> bool {
    let mut candidates = vec![CompactPosition::Type(root)];
    for step in &path.0 {
        candidates = candidates
            .into_iter()
            .flat_map(|position| advance_compact_position(position, *step))
            .collect();
        if candidates.is_empty() {
            return false;
        }
    }
    true
}

fn advance_compact_position<'a>(
    position: CompactPosition<'a>,
    step: GeneralizedTypePathStep,
) -> Vec<CompactPosition<'a>> {
    use GeneralizedTypePathStep as Step;
    match (position, step) {
        (CompactPosition::Type(ty), Step::FunctionArgument) => ty
            .funs
            .iter()
            .map(|fun| CompactPosition::Type(&fun.arg))
            .collect(),
        (CompactPosition::Type(ty), Step::FunctionArgumentEffect) => ty
            .funs
            .first()
            .filter(|_| ty.funs.len() == 1)
            .map(|fun| vec![CompactPosition::Type(&fun.arg_eff)])
            .unwrap_or_default(),
        (CompactPosition::Type(ty), Step::FunctionReturnEffect) => ty
            .funs
            .first()
            .filter(|_| ty.funs.len() == 1)
            .map(|fun| vec![CompactPosition::Type(&fun.ret_eff)])
            .unwrap_or_default(),
        (CompactPosition::Type(ty), Step::FunctionReturn) => ty
            .funs
            .first()
            .filter(|_| ty.funs.len() == 1)
            .map(|fun| vec![CompactPosition::Type(&fun.ret)])
            .unwrap_or_default(),
        (CompactPosition::Bounds(CompactBounds::Fun { arg, .. }), Step::FunctionArgument) => {
            vec![CompactPosition::Bounds(arg)]
        }
        (
            CompactPosition::Bounds(CompactBounds::Fun { arg_eff, .. }),
            Step::FunctionArgumentEffect,
        ) => vec![CompactPosition::Bounds(arg_eff)],
        (
            CompactPosition::Bounds(CompactBounds::Fun { ret_eff, .. }),
            Step::FunctionReturnEffect,
        ) => vec![CompactPosition::Bounds(ret_eff)],
        (CompactPosition::Bounds(CompactBounds::Fun { ret, .. }), Step::FunctionReturn) => {
            vec![CompactPosition::Bounds(ret)]
        }
        (
            CompactPosition::Type(ty),
            Step::ConstructorArgument {
                alternative,
                argument,
            },
        ) if ty.cons.len() == 1 && alternative.index() == 0 => ty
            .cons
            .values()
            .next()
            .and_then(|args| args.get(argument.index()))
            .map(|arg| vec![CompactPosition::Bounds(arg)])
            .unwrap_or_default(),
        (
            CompactPosition::Bounds(CompactBounds::Con { args, .. }),
            Step::ConstructorArgument {
                alternative,
                argument,
            },
        ) if alternative.index() == 0 => args
            .get(argument.index())
            .map(|arg| vec![CompactPosition::Bounds(arg)])
            .unwrap_or_default(),
        (CompactPosition::Type(ty), Step::TupleElement(index)) if ty.tuples.len() == 1 => ty
            .tuples
            .first()
            .and_then(|tuple| tuple.items.get(index.index()))
            .map(|item| vec![CompactPosition::Type(item)])
            .unwrap_or_default(),
        (CompactPosition::Bounds(CompactBounds::Tuple { items }), Step::TupleElement(index)) => {
            items
                .get(index.index())
                .map(|item| vec![CompactPosition::Bounds(item)])
                .unwrap_or_default()
        }
        (CompactPosition::Type(ty), Step::RecordField { alternative, field })
            if ty.records.len() == 1 && alternative.index() == 0 =>
        {
            ty.records
                .first()
                .and_then(|record| record.fields.get(field.index()))
                .map(|field| vec![CompactPosition::Type(&field.value)])
                .unwrap_or_default()
        }
        (
            CompactPosition::Bounds(CompactBounds::Record { fields }),
            Step::RecordField { alternative, field },
        ) if alternative.index() == 0 => fields
            .get(field.index())
            .map(|field| vec![CompactPosition::Bounds(&field.value)])
            .unwrap_or_default(),
        (
            CompactPosition::Type(ty),
            Step::VariantPayload {
                alternative,
                item,
                payload,
            },
        ) if ty.poly_variants.len() == 1 && alternative.index() == 0 => ty
            .poly_variants
            .first()
            .and_then(|variant| variant.items.get(item.index()))
            .and_then(|(_, payloads)| payloads.get(payload.index()))
            .map(|payload| vec![CompactPosition::Type(payload)])
            .unwrap_or_default(),
        (
            CompactPosition::Bounds(CompactBounds::PolyVariant { items }),
            Step::VariantPayload {
                alternative,
                item,
                payload,
            },
        ) if alternative.index() == 0 => items
            .get(item.index())
            .and_then(|(_, payloads)| payloads.get(payload.index()))
            .map(|payload| vec![CompactPosition::Bounds(payload)])
            .unwrap_or_default(),
        // Row items are normalized into reconstructed `CompactCon` entries. Until that
        // transformation exposes an exact borrowed output-to-parent mapping, retain the
        // collected witness as incomplete rather than attaching a guessed row argument.
        (CompactPosition::Type(_), Step::RowItemArgument { .. }) => Vec::new(),
        (CompactPosition::Type(ty), Step::RowTail) if ty.rows.len() == 1 => ty
            .rows
            .first()
            .map(|row| vec![CompactPosition::Type(&row.tail)])
            .unwrap_or_default(),
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use poly::expr::DefId;

    use super::*;

    #[test]
    fn scoped_capture_matches_legacy_oracle_for_full_local_and_component_drafts() {
        let (mut local_machine, local_owner, _, _) =
            ConstraintMachine::ordinary_no_claim_positive_alias_fixture();
        let local_generalized = empty_generalized_root();
        assert_scoped_capture_matches_legacy(
            &mut local_machine,
            local_owner,
            &local_generalized,
            "local binding",
        );

        let (mut component_machine, _, component_owner, _) =
            ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(true);
        let mut component_generalized = empty_generalized_root();
        component_generalized
            .compact
            .rec_vars
            .push(crate::compact::CompactRecursiveVar {
                var: TypeVar(900),
                bounds: crate::compact::CompactBounds::Interval {
                    lower: CompactType::default(),
                    upper: CompactType::default(),
                },
            });
        component_generalized
            .sandwiches
            .push(crate::compact::CompactSandwich {
                var: TypeVar(901),
                kind: crate::compact::CompactSandwichKind::Fun,
            });
        assert_scoped_capture_matches_legacy(
            &mut component_machine,
            component_owner,
            &component_generalized,
            "component",
        );
    }

    #[test]
    fn scoped_capture_matches_legacy_oracle_through_compound_neutral_and_upper_paths() {
        let mut machine = ConstraintMachine::new();
        let owner = TypeVar(920);
        let positive_leaf = TypeVar(921);
        let upper_owner = TypeVar(922);
        let negative_leaf = TypeVar(923);
        for var in [owner, positive_leaf, upper_owner, negative_leaf] {
            machine.register_type_var(var, TypeLevel::root());
        }

        let nested_lower = machine.alloc_pos(Pos::Var(positive_leaf));
        let nested_upper = machine.alloc_neg(Neg::Var(upper_owner));
        let nested_bounds = machine.alloc_neu(Neu::Bounds(nested_lower, nested_upper));
        let compound_lower = machine.alloc_pos(Pos::Con(
            vec!["witness-compound".into()],
            vec![nested_bounds],
        ));
        let owner_upper = machine.alloc_neg(Neg::Var(owner));
        machine.subtype(
            compound_lower,
            owner_upper,
            crate::constraints::OriginId::unknown_internal(),
        );

        let upper_nested_lower = machine.alloc_pos(Pos::Var(positive_leaf));
        let upper_nested_upper = machine.alloc_neg(Neg::Var(negative_leaf));
        let upper_nested_bounds =
            machine.alloc_neu(Neu::Bounds(upper_nested_lower, upper_nested_upper));
        let upper_compound = machine.alloc_neg(Neg::Con(
            vec!["witness-upper-compound".into()],
            vec![upper_nested_bounds],
        ));
        let upper_source = machine.alloc_pos(Pos::Var(upper_owner));
        machine.subtype(
            upper_source,
            upper_compound,
            crate::constraints::OriginId::unknown_internal(),
        );

        let (drafts, _) = assert_scoped_capture_matches_legacy(
            &mut machine,
            owner,
            &empty_generalized_root(),
            "compound/neutral/upper",
        );
        let nested_path = GeneralizedTypePath(vec![GeneralizedTypePathStep::ConstructorArgument {
            alternative: StructuralIndex::from_usize(0),
            argument: StructuralIndex::from_usize(0),
        }]);
        assert!(drafts.iter().any(|draft| {
            draft.path == nested_path && draft.role == GeneralizedWitnessRole::ConstraintRelation
        }));
        assert!(drafts.iter().any(|draft| {
            draft.path == nested_path && draft.role == GeneralizedWitnessRole::UpperBound
        }));
    }

    fn assert_scoped_capture_matches_legacy(
        machine: &mut ConstraintMachine,
        root: TypeVar,
        generalized: &GeneralizedCompactRoot,
        surface: &str,
    ) -> (Vec<GeneralizedWitnessDraft>, ProvenanceCompleteness) {
        let expected = capture_generalized_witnesses_legacy_oracle(machine, root, generalized);
        let actual = capture_generalized_witnesses(machine, root, generalized);
        assert_eq!(
            actual, expected,
            "{surface} capture must preserve every draft path, role, parent, completeness, and order"
        );
        actual
    }

    // Frozen pre-slice-2 traversal: this test-only oracle deliberately retains the old direct
    // read so scoped migration parity covers every draft field and ordering decision.
    fn capture_generalized_witnesses_legacy_oracle(
        machine: &ConstraintMachine,
        root: TypeVar,
        generalized: &GeneralizedCompactRoot,
    ) -> (Vec<GeneralizedWitnessDraft>, ProvenanceCompleteness) {
        let mut collector = LegacyWitnessCollector::new(machine);
        collector.collect_var(root, true, GeneralizedTypePath::default(), None);
        collector.drafts.retain_mut(|draft| {
            if function_argument_only(&draft.path) {
                return structural_path_survives(&generalized.compact.root, &draft.path);
            }
            if !structural_path_survives(&generalized.compact.root, &draft.path) {
                draft.completeness = ProvenanceCompleteness::Incomplete;
            }
            true
        });

        let sandwich_incomplete = !generalized.sandwiches.is_empty();
        if sandwich_incomplete {
            for draft in &mut collector.drafts {
                draft.completeness = ProvenanceCompleteness::Incomplete;
            }
        }
        for (index, _) in generalized.compact.rec_vars.iter().enumerate() {
            let path = GeneralizedTypePath(vec![GeneralizedTypePathStep::RecursiveBound(
                StructuralIndex::from_usize(index),
            )]);
            collector.drafts.push(GeneralizedWitnessDraft {
                path: path.clone(),
                role: GeneralizedWitnessRole::RecursiveLowerBound,
                incoming: Vec::new(),
                completeness: ProvenanceCompleteness::Incomplete,
            });
            collector.drafts.push(GeneralizedWitnessDraft {
                path,
                role: GeneralizedWitnessRole::RecursiveUpperBound,
                incoming: Vec::new(),
                completeness: ProvenanceCompleteness::Incomplete,
            });
        }

        // PUSP-C deliberately does not claim complete whole-scheme coverage until every structural
        // compact transformation has a parallel projection. Individual argument witnesses remain
        // complete when their exact path did not cross a sandwich or the storage budget.
        let scheme_completeness = ProvenanceCompleteness::Incomplete;
        (collector.drafts, scheme_completeness)
    }

    struct LegacyWitnessCollector<'a> {
        machine: &'a ConstraintMachine,
        drafts: Vec<GeneralizedWitnessDraft>,
        visiting: FxHashSet<(TypeVar, bool)>,
        incoming_edges: usize,
        truncated: bool,
    }

    #[derive(Clone, Copy)]
    enum LegacyWitnessParents<'a> {
        Bound(BoundRecordId),
        Selected(&'a [GeneralizationParent]),
    }

    impl<'a> From<BoundRecordId> for LegacyWitnessParents<'a> {
        fn from(record: BoundRecordId) -> Self {
            Self::Bound(record)
        }
    }

    impl<'a> LegacyWitnessCollector<'a> {
        fn new(machine: &'a ConstraintMachine) -> Self {
            Self {
                machine,
                drafts: Vec::new(),
                visiting: FxHashSet::default(),
                incoming_edges: 0,
                truncated: false,
            }
        }

        fn add<'parents>(
            &mut self,
            path: &GeneralizedTypePath,
            role: GeneralizedWitnessRole,
            parents: impl Into<LegacyWitnessParents<'parents>>,
        ) {
            match parents.into() {
                LegacyWitnessParents::Bound(record) => {
                    self.add_parent(path, role, GeneralizationParent::Bound(record));
                }
                LegacyWitnessParents::Selected(parents) => {
                    // An empty qualified selection means the formula proved this lower relation but
                    // no direct support currently contributes provenance. Keep it parentless rather
                    // than fabricating the raw Bound(record) parent used by an unclaimed relation.
                    for parent in parents {
                        self.add_parent(path, role, parent.clone());
                    }
                }
            }
        }

        fn add_parent(
            &mut self,
            path: &GeneralizedTypePath,
            role: GeneralizedWitnessRole,
            parent: GeneralizationParent,
        ) {
            if self.truncated {
                return;
            }
            let edge = GeneralizationDerivation {
                rule: GeneralizationDerivationRule::BoundCollection,
                parents: vec![parent],
            };
            if let Some(draft) = self
                .drafts
                .iter_mut()
                .find(|draft| draft.path == *path && draft.role == role)
            {
                // Keep duplicate candidates until arena insertion so the storage metrics can distinguish
                // considered edges from the canonical deduplicated set. This remains a flat edge list,
                // never a list of transitive proof paths.
                if self.incoming_edges >= MAX_INCOMING_EDGES_PER_SCHEME {
                    draft.completeness = ProvenanceCompleteness::Incomplete;
                    self.truncated = true;
                } else {
                    draft.incoming.push(edge);
                    self.incoming_edges += 1;
                }
                return;
            }
            if self.drafts.len() >= MAX_WITNESSES_PER_SCHEME
                || self.incoming_edges >= MAX_INCOMING_EDGES_PER_SCHEME
            {
                self.truncated = true;
                return;
            }
            self.drafts.push(GeneralizedWitnessDraft {
                path: path.clone(),
                role,
                incoming: vec![edge],
                completeness: ProvenanceCompleteness::Complete,
            });
            self.incoming_edges += 1;
        }

        fn mark_incomplete(&mut self, path: &GeneralizedTypePath, role: GeneralizedWitnessRole) {
            if let Some(draft) = self
                .drafts
                .iter_mut()
                .find(|draft| draft.path == *path && draft.role == role)
            {
                draft.completeness = ProvenanceCompleteness::Incomplete;
                return;
            }
            if self.drafts.len() >= MAX_WITNESSES_PER_SCHEME {
                self.truncated = true;
                return;
            }
            self.drafts.push(GeneralizedWitnessDraft {
                path: path.clone(),
                role,
                incoming: Vec::new(),
                completeness: ProvenanceCompleteness::Incomplete,
            });
        }

        fn collect_var(
            &mut self,
            var: TypeVar,
            positive: bool,
            path: GeneralizedTypePath,
            structural_parent: Option<LegacyWitnessParents<'_>>,
        ) {
            if self.truncated || path.depth() > MAX_GENERALIZED_PATH_DEPTH {
                self.truncated = true;
                return;
            }
            if let Some(parent) = structural_parent {
                self.add(&path, GeneralizedWitnessRole::ConstraintRelation, parent);
            }
            if !self.visiting.insert((var, positive)) {
                return;
            }
            if let Some(bounds) = self.machine.bounds().of(var) {
                if positive {
                    let entries = self
                        .machine
                        .scheme_projectable_lowers(var)
                        .collect::<Vec<_>>();
                    for entry in entries {
                        let endpoint = entry.bound.pos;
                        match entry.reason {
                            SchemeProjectableLowerReason::Unclaimed => {
                                self.add(&path, GeneralizedWitnessRole::LowerBound, entry.record);
                                self.collect_pos(
                                    endpoint,
                                    path.clone(),
                                    LegacyWitnessParents::Bound(entry.record),
                                );
                            }
                            SchemeProjectableLowerReason::Qualified {
                                uncovered_claims: _,
                                independent_supports,
                            } => {
                                let evidence = entry.projection_evidence.expect(
                                    "qualified projection lower must carry its evaluation evidence",
                                );
                                let mut parents = Vec::new();
                                let fail_open = match evidence {
                                    crate::constraints::proof::ProjectionEvidence::DecisiveClaimedArm(
                                        proof,
                                    ) => {
                                        parents.push(
                                            GeneralizationParent::BoundClaimProjectionProof {
                                                bound: entry.record,
                                                coverage_root: proof.coverage_root(),
                                                representative_claim: proof.representative_claim(),
                                                proof: Box::new(proof),
                                            },
                                        );
                                        false
                                    }
                                    crate::constraints::proof::ProjectionEvidence::ExactWithoutClaimedArm => {
                                        false
                                    }
                                    crate::constraints::proof::ProjectionEvidence::FailOpenIncomplete => {
                                        true
                                    }
                                };
                                parents.extend(independent_supports.into_iter().map(|carrier| {
                                    GeneralizationParent::BoundProjectionProof {
                                        bound: entry.record,
                                        carrier,
                                    }
                                }));
                                let parents = LegacyWitnessParents::Selected(&parents);
                                self.add(&path, GeneralizedWitnessRole::LowerBound, parents);
                                if fail_open {
                                    self.mark_incomplete(&path, GeneralizedWitnessRole::LowerBound);
                                }
                                self.collect_pos(endpoint, path.clone(), parents);
                            }
                        }
                    }
                } else {
                    let entries = bounds
                        .generalized_projection_uppers()
                        .map(|(id, bound)| (id, bound.neg))
                        .collect::<Vec<_>>();
                    for (record, endpoint) in entries {
                        self.add(&path, GeneralizedWitnessRole::UpperBound, record);
                        self.collect_neg(endpoint, path.clone(), record);
                    }
                }
            }
            self.visiting.remove(&(var, positive));
        }

        fn collect_pos(
            &mut self,
            id: PosId,
            path: GeneralizedTypePath,
            parent: LegacyWitnessParents<'_>,
        ) {
            match self.machine.types().pos(id).clone() {
                Pos::Var(var) => self.collect_var(var, true, path, Some(parent)),
                Pos::Con(_, args) => self.collect_neu_items(
                    &args,
                    &path,
                    |argument| GeneralizedTypePathStep::ConstructorArgument {
                        alternative: StructuralIndex::from_usize(0),
                        argument,
                    },
                    parent,
                ),
                Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                } => {
                    self.collect_neg(
                        arg,
                        child(&path, GeneralizedTypePathStep::FunctionArgument),
                        parent,
                    );
                    // The shipped PUSP graph exposes only the root function argument. Adding root
                    // return/effect witnesses would change existing bounded-query topology. Nested
                    // function positions are new structural positions and can be captured inertly.
                    if path.depth() != 0 {
                        self.collect_neg(
                            arg_eff,
                            child(&path, GeneralizedTypePathStep::FunctionArgumentEffect),
                            parent,
                        );
                        self.collect_pos(
                            ret_eff,
                            child(&path, GeneralizedTypePathStep::FunctionReturnEffect),
                            parent,
                        );
                        self.collect_pos(
                            ret,
                            child(&path, GeneralizedTypePathStep::FunctionReturn),
                            parent,
                        );
                    }
                }
                Pos::Record(fields)
                | Pos::RecordTailSpread { fields, .. }
                | Pos::RecordHeadSpread { fields, .. } => {
                    for (field, value) in fields.into_iter().enumerate() {
                        self.collect_pos(
                            value.value,
                            child(
                                &path,
                                GeneralizedTypePathStep::RecordField {
                                    alternative: StructuralIndex::from_usize(0),
                                    field: StructuralIndex::from_usize(field),
                                },
                            ),
                            parent,
                        );
                    }
                }
                Pos::PolyVariant(items) => {
                    for (item, (_, payloads)) in items.into_iter().enumerate() {
                        for (payload, value) in payloads.into_iter().enumerate() {
                            self.collect_pos(
                                value,
                                child(
                                    &path,
                                    GeneralizedTypePathStep::VariantPayload {
                                        alternative: StructuralIndex::from_usize(0),
                                        item: StructuralIndex::from_usize(item),
                                        payload: StructuralIndex::from_usize(payload),
                                    },
                                ),
                                parent,
                            );
                        }
                    }
                }
                Pos::Tuple(items) => {
                    for (index, value) in items.into_iter().enumerate() {
                        self.collect_pos(
                            value,
                            child(
                                &path,
                                GeneralizedTypePathStep::TupleElement(StructuralIndex::from_usize(
                                    index,
                                )),
                            ),
                            parent,
                        );
                    }
                }
                Pos::Row(items) => self.collect_pos_row_items(&items, &path, parent),
                Pos::Union(lhs, rhs) => {
                    self.collect_pos(lhs, path.clone(), parent);
                    self.collect_pos(rhs, path, parent);
                }
                Pos::NonSubtract(inner, _) | Pos::Stack { inner, .. } => {
                    self.collect_pos(inner, path, parent)
                }
                _ => {}
            }
        }

        fn collect_neg<'parents>(
            &mut self,
            id: NegId,
            path: GeneralizedTypePath,
            parent: impl Into<LegacyWitnessParents<'parents>>,
        ) {
            let parent = parent.into();
            match self.machine.types().neg(id).clone() {
                Neg::Var(var) => self.collect_var(var, false, path, Some(parent)),
                Neg::Con(_, args) => self.collect_neu_items(
                    &args,
                    &path,
                    |argument| GeneralizedTypePathStep::ConstructorArgument {
                        alternative: StructuralIndex::from_usize(0),
                        argument,
                    },
                    parent,
                ),
                Neg::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                } => {
                    self.collect_pos(
                        arg,
                        child(&path, GeneralizedTypePathStep::FunctionArgument),
                        parent,
                    );
                    if path.depth() != 0 {
                        self.collect_pos(
                            arg_eff,
                            child(&path, GeneralizedTypePathStep::FunctionArgumentEffect),
                            parent,
                        );
                        self.collect_neg(
                            ret_eff,
                            child(&path, GeneralizedTypePathStep::FunctionReturnEffect),
                            parent,
                        );
                        self.collect_neg(
                            ret,
                            child(&path, GeneralizedTypePathStep::FunctionReturn),
                            parent,
                        );
                    }
                }
                Neg::Record(fields) => {
                    for (field, value) in fields.into_iter().enumerate() {
                        self.collect_neg(
                            value.value,
                            child(
                                &path,
                                GeneralizedTypePathStep::RecordField {
                                    alternative: StructuralIndex::from_usize(0),
                                    field: StructuralIndex::from_usize(field),
                                },
                            ),
                            parent,
                        );
                    }
                }
                Neg::PolyVariant(items) => {
                    for (item, (_, payloads)) in items.into_iter().enumerate() {
                        for (payload, value) in payloads.into_iter().enumerate() {
                            self.collect_neg(
                                value,
                                child(
                                    &path,
                                    GeneralizedTypePathStep::VariantPayload {
                                        alternative: StructuralIndex::from_usize(0),
                                        item: StructuralIndex::from_usize(item),
                                        payload: StructuralIndex::from_usize(payload),
                                    },
                                ),
                                parent,
                            );
                        }
                    }
                }
                Neg::Tuple(items) => {
                    for (index, value) in items.into_iter().enumerate() {
                        self.collect_neg(
                            value,
                            child(
                                &path,
                                GeneralizedTypePathStep::TupleElement(StructuralIndex::from_usize(
                                    index,
                                )),
                            ),
                            parent,
                        );
                    }
                }
                Neg::Row(items, tail) => {
                    self.collect_neg_row_items(&items, &path, parent);
                    self.collect_neg(tail, child(&path, GeneralizedTypePathStep::RowTail), parent);
                }
                Neg::Intersection(lhs, rhs) => {
                    self.collect_neg(lhs, path.clone(), parent);
                    self.collect_neg(rhs, path, parent);
                }
                Neg::Stack { inner, .. } => self.collect_neg(inner, path, parent),
                _ => {}
            }
        }

        fn collect_neu(
            &mut self,
            id: NeuId,
            path: GeneralizedTypePath,
            parent: LegacyWitnessParents<'_>,
        ) {
            match self.machine.types().neu(id).clone() {
                Neu::Bounds(lower, upper) => {
                    self.collect_pos(lower, path.clone(), parent);
                    self.collect_neg(upper, path, parent);
                }
                Neu::Con(_, args) => self.collect_neu_items(
                    &args,
                    &path,
                    |argument| GeneralizedTypePathStep::ConstructorArgument {
                        alternative: StructuralIndex::from_usize(0),
                        argument,
                    },
                    parent,
                ),
                Neu::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                } => {
                    self.collect_neu(
                        arg,
                        child(&path, GeneralizedTypePathStep::FunctionArgument),
                        parent,
                    );
                    if path.depth() != 0 {
                        self.collect_neu(
                            arg_eff,
                            child(&path, GeneralizedTypePathStep::FunctionArgumentEffect),
                            parent,
                        );
                        self.collect_neu(
                            ret_eff,
                            child(&path, GeneralizedTypePathStep::FunctionReturnEffect),
                            parent,
                        );
                        self.collect_neu(
                            ret,
                            child(&path, GeneralizedTypePathStep::FunctionReturn),
                            parent,
                        );
                    }
                }
                Neu::Record(fields) => {
                    for (field, value) in fields.into_iter().enumerate() {
                        self.collect_neu(
                            value.value,
                            child(
                                &path,
                                GeneralizedTypePathStep::RecordField {
                                    alternative: StructuralIndex::from_usize(0),
                                    field: StructuralIndex::from_usize(field),
                                },
                            ),
                            parent,
                        );
                    }
                }
                Neu::PolyVariant(items) => {
                    for (item, (_, payloads)) in items.into_iter().enumerate() {
                        for (payload, value) in payloads.into_iter().enumerate() {
                            self.collect_neu(
                                value,
                                child(
                                    &path,
                                    GeneralizedTypePathStep::VariantPayload {
                                        alternative: StructuralIndex::from_usize(0),
                                        item: StructuralIndex::from_usize(item),
                                        payload: StructuralIndex::from_usize(payload),
                                    },
                                ),
                                parent,
                            );
                        }
                    }
                }
                Neu::Tuple(items) => {
                    for (index, value) in items.into_iter().enumerate() {
                        self.collect_neu(
                            value,
                            child(
                                &path,
                                GeneralizedTypePathStep::TupleElement(StructuralIndex::from_usize(
                                    index,
                                )),
                            ),
                            parent,
                        );
                    }
                }
            }
        }

        fn collect_neu_items(
            &mut self,
            items: &[NeuId],
            path: &GeneralizedTypePath,
            step: impl Fn(StructuralIndex) -> GeneralizedTypePathStep,
            parent: LegacyWitnessParents<'_>,
        ) {
            for (index, item) in items.iter().copied().enumerate() {
                self.collect_neu(
                    item,
                    child(path, step(StructuralIndex::from_usize(index))),
                    parent,
                );
            }
        }

        fn collect_pos_row_items(
            &mut self,
            items: &[PosId],
            path: &GeneralizedTypePath,
            parent: LegacyWitnessParents<'_>,
        ) {
            for (item, id) in items.iter().copied().enumerate() {
                if let Pos::Con(_, args) = self.machine.types().pos(id).clone() {
                    for (argument, value) in args.into_iter().enumerate() {
                        self.collect_neu(
                            value,
                            child(
                                path,
                                GeneralizedTypePathStep::RowItemArgument {
                                    item: StructuralIndex::from_usize(item),
                                    argument: StructuralIndex::from_usize(argument),
                                },
                            ),
                            parent,
                        );
                    }
                }
            }
        }

        fn collect_neg_row_items(
            &mut self,
            items: &[NegId],
            path: &GeneralizedTypePath,
            parent: LegacyWitnessParents<'_>,
        ) {
            for (item, id) in items.iter().copied().enumerate() {
                if let Neg::Con(_, args) = self.machine.types().neg(id).clone() {
                    for (argument, value) in args.into_iter().enumerate() {
                        self.collect_neu(
                            value,
                            child(
                                path,
                                GeneralizedTypePathStep::RowItemArgument {
                                    item: StructuralIndex::from_usize(item),
                                    argument: StructuralIndex::from_usize(argument),
                                },
                            ),
                            parent,
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn covered_only_lower_contributes_no_generalized_witness_parent() {
        let (mut machine, endpoint, owner, _) =
            ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(false);
        let record = raw_var_lower_record(&machine, owner, endpoint);

        let drafts = capture(&mut machine, owner);

        assert!(
            drafts
                .iter()
                .flat_map(|draft| &draft.incoming)
                .flat_map(|edge| &edge.parents)
                .all(|parent| !parent_references_bound(parent, record)),
            "a live covered-only relation must not be traversed or retained as a witness parent"
        );
    }

    #[test]
    fn mixed_lower_contributes_only_its_uncovered_claim_parent() {
        let (mut machine, endpoint, owner, _) =
            ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(true);
        let record = raw_var_lower_record(&machine, owner, endpoint);
        let (uncovered, proof) = machine
            .scheme_projectable_lowers(owner)
            .find_map(|entry| {
                (entry.record == record)
                    .then_some((entry.reason, entry.projection_evidence))
                    .and_then(|(reason, evidence)| match reason {
                        SchemeProjectableLowerReason::Qualified {
                            uncovered_claims: claims,
                            ..
                        } => Some((claims, evidence)),
                        SchemeProjectableLowerReason::Unclaimed => None,
                    })
            })
            .expect("mixed record remains projectable through its independent claim");
        assert_eq!(uncovered.len(), 1, "fixture has one uncovered claim");
        let Some(crate::constraints::proof::ProjectionEvidence::DecisiveClaimedArm(proof)) = proof
        else {
            panic!("the claimed fixture must retain its decisive exact certificate");
        };

        let drafts = capture(&mut machine, owner);
        let lower = draft_at_root(&drafts, GeneralizedWitnessRole::LowerBound);
        let expected = GeneralizationParent::BoundClaimProjectionProof {
            bound: record,
            coverage_root: proof.coverage_root(),
            representative_claim: proof.representative_claim(),
            proof: Box::new(proof),
        };
        assert_eq!(proof.coverage_root(), uncovered[0]);

        assert_eq!(
            lower
                .incoming
                .iter()
                .flat_map(|edge| &edge.parents)
                .cloned()
                .collect::<Vec<_>>(),
            vec![expected.clone()],
            "the covered sibling claim and the plain mixed bound must stay out of provenance"
        );
        assert_eq!(
            draft_at_root(&drafts, GeneralizedWitnessRole::ConstraintRelation)
                .incoming
                .iter()
                .flat_map(|edge| &edge.parents)
                .cloned()
                .collect::<Vec<_>>(),
            vec![expected],
            "the selected claim identity must survive traversal through the Var endpoint"
        );
    }

    #[test]
    fn ordinary_lowers_preserve_the_raw_bound_edges_exactly() {
        let (mut machine, owner, direct, transitive) =
            ConstraintMachine::ordinary_no_claim_positive_alias_fixture();
        let owner_record = raw_var_lower_record(&machine, owner, direct);
        let direct_record = raw_var_lower_record(&machine, direct, transitive);
        let expected = vec![bound_edge(owner_record), bound_edge(direct_record)];

        let drafts = capture(&mut machine, owner);
        let lower = draft_at_root(&drafts, GeneralizedWitnessRole::LowerBound);

        assert_eq!(
            lower.incoming, expected,
            "the no-claim path must remain byte-for-byte equivalent to raw lower traversal"
        );
    }

    #[test]
    fn duplicate_bound_claim_paths_deduplicate_with_exact_edge_accounting() {
        let (mut machine, endpoint, owner, _) =
            ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(true);
        let record = raw_var_lower_record(&machine, owner, endpoint);
        let claim = machine
            .scheme_projectable_lowers(owner)
            .find_map(|entry| match entry.reason {
                SchemeProjectableLowerReason::Qualified {
                    uncovered_claims: claims,
                    ..
                } if entry.record == record => claims.first().copied(),
                _ => None,
            })
            .expect("mixed fixture has an uncovered claim");
        let nested = TypeVar(100);
        let nested_pos = machine.alloc_pos(Pos::Var(nested));
        let union = machine.alloc_pos(Pos::Union(nested_pos, nested_pos));
        let parent = GeneralizationParent::BoundClaim {
            bound: record,
            claim,
        };
        let selected = [parent.clone()];
        let mut round_state = machine.new_projection_evaluation_round();
        let (drafts, incoming_edges) = machine
            .with_legacy_projection_query(&mut round_state, |query| {
                let mut collector = WitnessCollector::new(&query);
                collector.collect_pos(
                    union,
                    GeneralizedTypePath::default(),
                    WitnessParents::Selected(&selected),
                )?;
                let incoming_edges = collector.incoming_edges;
                let drafts = std::mem::take(&mut collector.drafts);
                drop(collector);
                Ok(query.complete((drafts, incoming_edges)))
            })
            .expect("duplicate-path witness collection completes");

        let draft = draft_at_root(&drafts, GeneralizedWitnessRole::ConstraintRelation);
        assert_eq!(
            draft.incoming,
            vec![
                GeneralizationDerivation {
                    rule: GeneralizationDerivationRule::BoundCollection,
                    parents: vec![parent.clone()],
                },
                GeneralizationDerivation {
                    rule: GeneralizationDerivationRule::BoundCollection,
                    parents: vec![parent.clone()],
                },
            ],
            "both union traversal paths are considered before canonical insertion"
        );
        assert_eq!(incoming_edges, 2);

        let scheme = machine.alloc_generalized_scheme_record(
            DefId(0),
            0,
            drafts,
            ProvenanceCompleteness::Complete,
        );
        let witness = machine
            .generalized_scheme_record(scheme)
            .expect("stored test scheme")
            .witnesses[0];
        assert_eq!(
            machine
                .generalized_scheme_witness(witness)
                .expect("stored test witness")
                .incoming,
            vec![GeneralizationDerivation {
                rule: GeneralizationDerivationRule::BoundCollection,
                parents: vec![parent],
            }],
            "the canonical witness stores one edge for the duplicate (bound, claim) pair"
        );
        let coverage = machine.timing().generalized_schemes;
        assert_eq!(coverage.incoming_edges_considered, 2);
        assert_eq!(coverage.incoming_edges_inserted, 1);
        assert_eq!(coverage.incoming_edges_deduplicated, 1);
        assert_eq!(
            coverage.incoming_edges_considered,
            coverage.incoming_edges_inserted + coverage.incoming_edges_deduplicated,
            "edge accounting remains exact after claim-qualified deduplication"
        );
    }

    fn capture(machine: &mut ConstraintMachine, root: TypeVar) -> Vec<GeneralizedWitnessDraft> {
        capture_generalized_witnesses(machine, root, &empty_generalized_root()).0
    }

    fn empty_generalized_root() -> GeneralizedCompactRoot {
        GeneralizedCompactRoot {
            compact: CompactRoot::default(),
            role_predicates: Vec::new(),
            quantifiers: Vec::new(),
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        }
    }

    fn raw_var_lower_record(
        machine: &ConstraintMachine,
        owner: TypeVar,
        endpoint: TypeVar,
    ) -> BoundRecordId {
        machine
            .bounds()
            .of(owner)
            .expect("raw lower owner")
            .generalized_projection_lowers()
            .find_map(|(record, bound)| {
                matches!(machine.types().pos(bound.pos), Pos::Var(found) if *found == endpoint)
                    .then_some(record)
            })
            .expect("raw Var lower")
    }

    fn draft_at_root(
        drafts: &[GeneralizedWitnessDraft],
        role: GeneralizedWitnessRole,
    ) -> &GeneralizedWitnessDraft {
        drafts
            .iter()
            .find(|draft| draft.path == GeneralizedTypePath::default() && draft.role == role)
            .expect("root witness draft")
    }

    fn bound_edge(record: BoundRecordId) -> GeneralizationDerivation {
        GeneralizationDerivation {
            rule: GeneralizationDerivationRule::BoundCollection,
            parents: vec![GeneralizationParent::Bound(record)],
        }
    }

    fn parent_references_bound(parent: &GeneralizationParent, record: BoundRecordId) -> bool {
        match parent {
            GeneralizationParent::Bound(found) => *found == record,
            GeneralizationParent::BoundClaim { bound, .. } => *bound == record,
            GeneralizationParent::BoundClaimProjectionProof { bound, .. } => *bound == record,
            GeneralizationParent::BoundProjectionProof { bound, .. } => *bound == record,
            GeneralizationParent::Constraint(_) => false,
        }
    }
}
