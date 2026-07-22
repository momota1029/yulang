//! Exact canonical-parent projection for finalized same-session function arguments.
//!
//! PUSP-C records only mappings it can prove from canonical bound iteration. This initial capture
//! follows polarized function-argument positions, including nested function arguments, because
//! those are the positions needed by the parameter-use-site bridge. Other finalized positions make
//! the scheme record incomplete; they never receive a whole-definition fallback parent set.

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
    collector
        .drafts
        .retain(|draft| function_argument_path_survives(&generalized.compact.root, &draft.path));

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
            Pos::Fun { arg, .. } => self.collect_neg(
                arg,
                child(&path, GeneralizedTypePathStep::FunctionArgument),
                parent,
            ),
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
            Neg::Fun { arg, .. } => self.collect_pos(
                arg,
                child(&path, GeneralizedTypePathStep::FunctionArgument),
                parent,
            ),
            Neg::Intersection(lhs, rhs) => {
                self.collect_neg(lhs, path.clone(), parent);
                self.collect_neg(rhs, path, parent);
            }
            Neg::Stack { inner, .. } => self.collect_neg(inner, path, parent),
            _ => {}
        }
    }
}

fn child(path: &GeneralizedTypePath, step: GeneralizedTypePathStep) -> GeneralizedTypePath {
    let mut path = path.clone();
    path.push(step);
    path
}

fn function_argument_path_survives(root: &CompactType, path: &GeneralizedTypePath) -> bool {
    let mut candidates = vec![root];
    for step in &path.0 {
        if *step != GeneralizedTypePathStep::FunctionArgument {
            return false;
        }
        candidates = candidates
            .into_iter()
            .flat_map(|ty| ty.funs.iter().map(|fun| &fun.arg))
            .collect();
        if candidates.is_empty() {
            return false;
        }
    }
    true
}
