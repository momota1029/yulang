use super::*;

use crate::analysis::BodyRequirementDiagnosticKind;
use crate::constraints::explain::{
    ExplanationBudget, ExplanationCompleteness, ExplanationNode, ExplanationTruncationReason,
    PortableProvenanceExportBudget, PortableProvenanceExportRoot,
};
use crate::constraints::{
    DiagnosticExplanationCompleteness, DiagnosticExplanationTruncationReason, DiagnosticTypeCause,
    DiagnosticTypeCauseRole, PortableExplanationBudget, explain_portable_subtype,
};
use crate::lowering::{BodyLowering, lower_loaded_files};
use poly::provenance::{
    PortableByteRange, PortableProvenanceSnapshot, PortableSourceLocation, ProvenanceAnchor,
    SubtypeProvenanceSidecar,
};
use rustc_hash::FxHashSet;

const TUPLE_SOURCE: &str = "my g(x: (int, int)) = x\ng (1, 2, 3)\n";
const GENERIC_SOURCE: &str = "my id x = x\nmy g(x: (int, int)) = x\ng (id (1, 2, 3))\n";

#[test]
fn portable_query_is_cycle_safe_on_the_same_canonical_graph() {
    let mut output = lower(TUPLE_SOURCE);
    let root = ConstraintRecordId(45);
    output.session.infer.constraints_mut().constraint_records[root.0 as usize]
        .structural_derivations
        .push(StructuralDerivation {
            parent: root,
            rule: StructuralDerivationRule::UnionBranch {
                branch: StructuralIndex(0),
            },
        });
    let machine = output.session.infer.constraints();
    let local = machine
        .why_constraint(root, ExplanationBudget::default())
        .expect("cycle query");
    let (snapshot, anchor) = export_constraint(&output, root, true);
    let portable = query_same_endpoint(&snapshot, &[anchor], PortableExplanationBudget::default());

    assert_eq!(local.completeness, ExplanationCompleteness::Complete);
    assert_eq!(
        portable.completeness,
        DiagnosticExplanationCompleteness::Complete
    );
    assert_eq!(portable.lower_sites, located_local_causes(&output, &local));
}

#[test]
fn portable_query_retains_alternate_causes_in_deterministic_order() {
    let output = lower(GENERIC_SOURCE);
    let root = ConstraintRecordId(89);
    let local = output
        .session
        .infer
        .constraints()
        .why_constraint(root, ExplanationBudget::default())
        .expect("alternate-cause query");
    let expected = located_local_causes(&output, &local);
    let (snapshot, anchor) = export_constraint(&output, root, true);
    let first = query_same_endpoint(&snapshot, &[anchor], PortableExplanationBudget::default());
    let second = query_same_endpoint(&snapshot, &[anchor], PortableExplanationBudget::default());

    assert!(
        expected.len() >= 2,
        "fixture must retain alternate located causes"
    );
    assert_eq!(first, second);
    assert_eq!(first.lower_sites, expected);
}

#[test]
fn portable_query_selects_single_or_multiple_roots_without_reexpansion() {
    let output = lower(GENERIC_SOURCE);
    let machine = output.session.infer.constraints();
    let root = ConstraintRecordId(89);
    let local = machine
        .why_constraint(root, ExplanationBudget::default())
        .expect("root query");
    let (bound, owner, direction) = local
        .nodes
        .iter()
        .find_map(|node| match node {
            ExplanationNode::Bound {
                id,
                owner,
                direction,
                ..
            } => Some((*id, *owner, *direction)),
            _ => None,
        })
        .expect("root reaches a bound");
    let bound_local = match direction {
        BoundDirection::Lower => {
            machine.why_lower_bound(owner, bound, ExplanationBudget::default())
        }
        BoundDirection::Upper => {
            machine.why_upper_bound(owner, bound, ExplanationBudget::default())
        }
    }
    .expect("bound query");
    let export = machine
        .export_portable_provenance(
            &[
                PortableProvenanceExportRoot::Constraint(root),
                PortableProvenanceExportRoot::Bound(bound),
            ],
            PortableProvenanceExportBudget::default(),
            |boundary, kind| portable_source_location(&output, boundary, kind),
        )
        .expect("multi-root export");
    let first = export.root_anchors[0].expect("constraint anchor");
    let second = export.root_anchors[1].expect("bound anchor");
    let single = query_same_endpoint(
        &export.snapshot,
        &[first],
        PortableExplanationBudget::default(),
    );
    let multiple = explain_portable_subtype(
        &export.snapshot,
        &[first, second],
        &[first],
        PortableExplanationBudget::default(),
    );

    assert_eq!(single.lower_sites, located_local_causes(&output, &local));
    let mut seen_origins = FxHashSet::default();
    let expected_multiple = local
        .source_leaves
        .iter()
        .chain(&bound_local.source_leaves)
        .filter(|leaf| seen_origins.insert(leaf.origin))
        .filter_map(|leaf| local_cause(&output, leaf))
        .collect::<Vec<_>>();
    assert_eq!(multiple.lower_sites, expected_multiple);
    assert_eq!(multiple.upper_sites, single.upper_sites);
    assert_eq!(
        multiple,
        explain_portable_subtype(
            &export.snapshot,
            &[first, second],
            &[first],
            PortableExplanationBudget::default(),
        )
    );
}

#[test]
fn portable_query_omits_source_sites_without_locations() {
    let output = lower(TUPLE_SOURCE);
    let root = ConstraintRecordId(45);
    let local = output
        .session
        .infer
        .constraints()
        .why_constraint(root, ExplanationBudget::default())
        .expect("local query");
    assert!(!local.source_leaves.is_empty());
    let (snapshot, anchor) = export_constraint(&output, root, false);
    let portable = query_same_endpoint(&snapshot, &[anchor], PortableExplanationBudget::default());

    assert!(portable.lower_sites.is_empty());
    assert!(portable.upper_sites.is_empty());
    assert_eq!(
        portable.completeness,
        DiagnosticExplanationCompleteness::Complete
    );
}

#[test]
fn portable_query_degrades_cleanly_for_an_empty_cache_snapshot() {
    let output = lower(TUPLE_SOURCE);
    let local = output
        .session
        .infer
        .constraints()
        .why_constraint(ConstraintRecordId(45), ExplanationBudget::default())
        .expect("fresh-session control");
    assert!(!local.source_leaves.is_empty());
    let empty = SubtypeProvenanceSidecar::empty();
    let portable = explain_portable_subtype(
        &empty.snapshot,
        &[],
        &[],
        PortableExplanationBudget::default(),
    );

    assert!(portable.lower_sites.is_empty());
    assert!(portable.upper_sites.is_empty());
    assert_eq!(
        portable.completeness,
        DiagnosticExplanationCompleteness::IncompleteProvenance
    );
    assert_eq!(portable.truncation, None);
}

#[test]
fn portable_query_reports_the_same_forced_truncation_shape_as_cprov_h() {
    let output = lower(GENERIC_SOURCE);
    let root = ConstraintRecordId(89);
    let (snapshot, anchor) = export_constraint(&output, root, true);
    let cases = [
        (
            ExplanationBudget {
                max_nodes: 0,
                max_edges: 4,
                max_depth: 4,
            },
            DiagnosticExplanationTruncationReason::NodeBudget { limit: 0 },
        ),
        (
            ExplanationBudget {
                max_nodes: 4,
                max_edges: 0,
                max_depth: 4,
            },
            DiagnosticExplanationTruncationReason::EdgeBudget { limit: 0 },
        ),
        (
            ExplanationBudget {
                max_nodes: 4,
                max_edges: 4,
                max_depth: 0,
            },
            DiagnosticExplanationTruncationReason::DepthBudget { limit: 0 },
        ),
    ];

    for (local_budget, expected_reason) in cases {
        let local = output
            .session
            .infer
            .constraints()
            .why_constraint(root, local_budget)
            .expect("forced local truncation");
        let portable = query_same_endpoint(
            &snapshot,
            &[anchor],
            PortableExplanationBudget {
                max_nodes: local_budget.max_nodes,
                max_edges: local_budget.max_edges,
                max_depth: local_budget.max_depth,
            },
        );
        assert_eq!(
            local.completeness,
            ExplanationCompleteness::TruncatedByBudget
        );
        assert_eq!(
            portable.completeness,
            DiagnosticExplanationCompleteness::TruncatedByBudget
        );
        assert_eq!(portable.truncation, Some(expected_reason));
        assert_eq!(portable_reason(local.truncation), portable.truncation);
    }
}

#[test]
fn portable_query_matches_cprov_h_for_every_subp_a_case() {
    let cases = [
        ("tuple-arity", TUPLE_SOURCE, ConstraintRecordId(45)),
        (
            "tuple-arity-through-generic",
            GENERIC_SOURCE,
            ConstraintRecordId(89),
        ),
        (
            "nested-tuple-arity",
            "my g(x: ((int, int), int)) = x\ng ((1, 2, 3), 4)\n",
            ConstraintRecordId(69),
        ),
        (
            "poly-variant-tag",
            "case :some 1:\n  :none -> 0\n",
            ConstraintRecordId(21),
        ),
    ];

    for (name, source, root) in cases {
        let output = lower(source);
        let local = output
            .session
            .infer
            .constraints()
            .why_constraint(root, ExplanationBudget::default())
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        let (snapshot, anchor) = export_constraint(&output, root, true);
        let portable =
            query_same_endpoint(&snapshot, &[anchor], PortableExplanationBudget::default());
        assert_eq!(
            portable.lower_sites,
            located_local_causes(&output, &local),
            "{name}",
        );
        assert_eq!(
            portable.completeness,
            DiagnosticExplanationCompleteness::Complete,
            "{name}",
        );
    }
}

fn export_constraint(
    output: &BodyLowering,
    root: ConstraintRecordId,
    with_locations: bool,
) -> (PortableProvenanceSnapshot, ProvenanceAnchor) {
    let export = output
        .session
        .infer
        .constraints()
        .export_portable_provenance(
            &[PortableProvenanceExportRoot::Constraint(root)],
            PortableProvenanceExportBudget::default(),
            |boundary, kind| {
                with_locations
                    .then(|| portable_source_location(output, boundary, kind))
                    .flatten()
            },
        )
        .expect("portable export");
    let anchor = export.root_anchors[0].expect("portable root anchor");
    (export.snapshot, anchor)
}

fn query_same_endpoint(
    snapshot: &PortableProvenanceSnapshot,
    roots: &[ProvenanceAnchor],
    budget: PortableExplanationBudget,
) -> crate::constraints::DiagnosticSubtypeExplanation {
    explain_portable_subtype(snapshot, roots, roots, budget)
}

fn located_local_causes(
    output: &BodyLowering,
    result: &crate::constraints::explain::ExplanationQueryResult,
) -> Vec<DiagnosticTypeCause> {
    result
        .source_leaves
        .iter()
        .filter_map(|leaf| local_cause(output, leaf))
        .collect()
}

fn local_cause(
    output: &BodyLowering,
    leaf: &crate::constraints::explain::ExplanationSourceLeaf,
) -> Option<DiagnosticTypeCause> {
    let source_span = match leaf.kind {
        ConstraintOriginKind::ApplicationArgument => output
            .session
            .source_boundary_provenance
            .application_argument(leaf.boundary)
            .map(|provenance| provenance.argument_span.clone()),
        ConstraintOriginKind::Pattern => output
            .session
            .source_boundary_provenance
            .pattern(leaf.boundary)
            .cloned(),
        ConstraintOriginKind::BodyRequirement(_) => output
            .session
            .source_boundary_provenance
            .body_requirement(leaf.boundary)
            .map(|provenance| provenance.use_span.clone()),
        _ => None,
    }?;
    Some(DiagnosticTypeCause {
        role: match leaf.kind {
            ConstraintOriginKind::ApplicationArgument => {
                DiagnosticTypeCauseRole::RequiredByApplication
            }
            ConstraintOriginKind::Pattern => DiagnosticTypeCauseRole::RequiredByPattern,
            ConstraintOriginKind::Annotation => DiagnosticTypeCauseRole::RequiredByAnnotation,
            ConstraintOriginKind::BodyRequirement(kind) => {
                DiagnosticTypeCauseRole::RequiredByBodyUse(match kind {
                    BodyRequirementKind::BooleanCondition => {
                        BodyRequirementDiagnosticKind::BooleanCondition
                    }
                    BodyRequirementKind::OperatorOperand { .. } => {
                        BodyRequirementDiagnosticKind::OperatorOperand
                    }
                    BodyRequirementKind::PatternGuard => {
                        BodyRequirementDiagnosticKind::PatternGuard
                    }
                    BodyRequirementKind::CalleeArgument { .. } => {
                        BodyRequirementDiagnosticKind::CalleeArgument
                    }
                })
            }
            ConstraintOriginKind::Return
            | ConstraintOriginKind::Field
            | ConstraintOriginKind::Assignment => DiagnosticTypeCauseRole::InferredFromExpression,
            ConstraintOriginKind::Internal | ConstraintOriginKind::UnknownInternal => return None,
        },
        source_span,
    })
}

fn portable_source_location(
    output: &BodyLowering,
    boundary: SourceBoundaryId,
    kind: ConstraintOriginKind,
) -> Option<PortableSourceLocation> {
    let span = match kind {
        ConstraintOriginKind::ApplicationArgument => output
            .session
            .source_boundary_provenance
            .application_argument(boundary)
            .map(|provenance| &provenance.argument_span),
        ConstraintOriginKind::BodyRequirement(_) => output
            .session
            .source_boundary_provenance
            .body_requirement(boundary)
            .map(|provenance| &provenance.use_span),
        ConstraintOriginKind::Pattern => output
            .session
            .source_boundary_provenance
            .pattern(boundary),
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
}

fn portable_reason(
    reason: Option<ExplanationTruncationReason>,
) -> Option<DiagnosticExplanationTruncationReason> {
    reason.map(|reason| match reason {
        ExplanationTruncationReason::NodeBudget { limit } => {
            DiagnosticExplanationTruncationReason::NodeBudget { limit }
        }
        ExplanationTruncationReason::EdgeBudget { limit } => {
            DiagnosticExplanationTruncationReason::EdgeBudget { limit }
        }
        ExplanationTruncationReason::DepthBudget { limit } => {
            DiagnosticExplanationTruncationReason::DepthBudget { limit }
        }
    })
}

fn lower(source: &str) -> BodyLowering {
    let loaded = sources::load(vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }]);
    lower_loaded_files(&loaded).expect("lower portable explanation fixture")
}
