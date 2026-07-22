//! Exact canonical-parent projection for finalized same-session structural positions.
//!
//! PUSP-C records only mappings it can prove from canonical bound iteration. This initial capture
//! follows only paths whose already-selected compact structure preserves an exact output position.
//! Unsupported or ambiguous structural transformations remain incomplete; they never receive a
//! whole-definition fallback parent set.

use rustc_hash::FxHashSet;

use super::*;
use crate::constraints::{
    BoundRecordId, GeneralizationDerivation, GeneralizationDerivationRule, GeneralizationParent,
    GeneralizedTypePath, GeneralizedTypePathStep, GeneralizedWitnessDraft, GeneralizedWitnessRole,
    ProvenanceCompleteness, StructuralIndex,
};

const MAX_WITNESSES_PER_SCHEME: usize = 128;
const MAX_INCOMING_EDGES_PER_SCHEME: usize = 256;
const MAX_GENERALIZED_PATH_DEPTH: usize = 16;

pub(crate) fn capture_generalized_witnesses(
    machine: &ConstraintMachine,
    root: TypeVar,
    generalized: &GeneralizedCompactRoot,
) -> (Vec<GeneralizedWitnessDraft>, ProvenanceCompleteness) {
    let mut collector = WitnessCollector::new(machine);
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

struct WitnessCollector<'a> {
    machine: &'a ConstraintMachine,
    drafts: Vec<GeneralizedWitnessDraft>,
    visiting: FxHashSet<(TypeVar, bool)>,
    incoming_edges: usize,
    truncated: bool,
}

impl<'a> WitnessCollector<'a> {
    fn new(machine: &'a ConstraintMachine) -> Self {
        Self {
            machine,
            drafts: Vec::new(),
            visiting: FxHashSet::default(),
            incoming_edges: 0,
            truncated: false,
        }
    }

    fn add(
        &mut self,
        path: &GeneralizedTypePath,
        role: GeneralizedWitnessRole,
        parent: BoundRecordId,
    ) {
        if self.truncated {
            return;
        }
        let edge = GeneralizationDerivation {
            rule: GeneralizationDerivationRule::BoundCollection,
            parents: vec![GeneralizationParent::Bound(parent)],
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

    fn collect_var(
        &mut self,
        var: TypeVar,
        positive: bool,
        path: GeneralizedTypePath,
        structural_parent: Option<BoundRecordId>,
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
                let entries = bounds
                    .generalized_projection_lowers()
                    .map(|(id, bound)| (id, bound.pos))
                    .collect::<Vec<_>>();
                for (record, endpoint) in entries {
                    self.add(&path, GeneralizedWitnessRole::LowerBound, record);
                    self.collect_pos(endpoint, path.clone(), record);
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

    fn collect_pos(&mut self, id: PosId, path: GeneralizedTypePath, parent: BoundRecordId) {
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

    fn collect_neg(&mut self, id: NegId, path: GeneralizedTypePath, parent: BoundRecordId) {
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

    fn collect_neu(&mut self, id: NeuId, path: GeneralizedTypePath, parent: BoundRecordId) {
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
        parent: BoundRecordId,
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
        parent: BoundRecordId,
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
        parent: BoundRecordId,
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
