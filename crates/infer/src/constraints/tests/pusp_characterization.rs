use super::*;

use std::time::{Duration, Instant};

use crate::constraints::explain::{
    ExplanationBudget, ExplanationCompleteness, ExplanationEdge, ExplanationNode,
    ExplanationNodeId, ExplanationQueryResult,
};
use crate::constraints::ocast_eligibility::OcastEligibilityState;
use crate::lowering::{
    BodyLowering, lower_loaded_files, lower_loaded_files_prefix, lower_loaded_files_with_prefix,
};
use crate::{ModuleOrder, Name};
use poly::expr::{Def, DefId, Expr, Pat};
use poly::types::{Neg, Pos, TypeVar};

const JUNCTION_STD: &str = concat!(
    "mod std:\n",
    "  pub mod control:\n",
    "    pub mod junction:\n",
    "      pub mod junction:\n",
    "        pub junction value = value\n",
);

#[test]
fn pusp_a_characterizes_parameter_and_scheme_provenance_gaps() {
    let cases = [
        Case::same_session(
            "inferred-if-condition",
            concat!(
                "my subject(pusp_param) = if pusp_param:\n",
                "  1\n",
                "else:\n",
                "  2\n",
                "subject(42)\n",
            ),
        ),
        Case::same_session(
            "annotated-parameter-control",
            concat!(
                "my subject(pusp_param: bool) = if pusp_param:\n",
                "  1\n",
                "else:\n",
                "  2\n",
                "subject(42)\n",
            ),
        ),
        Case::same_session(
            "generic-multiple-instantiations",
            concat!(
                "my subject(pusp_param) = pusp_param\n",
                "subject(1)\n",
                "subject(false)\n",
            ),
        ),
        Case::imported(
            "imported-cache-loaded-callee",
            concat!(
                "pub subject(pusp_param) = if pusp_param:\n",
                "  1\n",
                "else:\n",
                "  2\n",
            ),
            "subject(42)\n",
        ),
        Case::same_session(
            "multiple-body-uses",
            concat!(
                "my subject(pusp_param) = if pusp_param:\n",
                "  if pusp_param:\n",
                "    1\n",
                "  else:\n",
                "    2\n",
                "else:\n",
                "  3\n",
                "subject(42)\n",
            ),
        ),
    ];

    let actual = cases.map(Case::capture);
    assert_eq!(actual, expected_baselines());
}

#[test]
fn pusp_c_concrete_argument_witness_points_to_original_parameter_upper_bound() {
    let output = lower(concat!(
        "my subject(pusp_param) = if pusp_param:\n",
        "  1\n",
        "else:\n",
        "  2\n",
        "subject(42)\n",
    ));
    let def = subject_def(&output);
    let parameter = parameter_var(&output, def);
    let machine = output.session.infer.constraints();
    let original = *bool_upper_records(machine, parameter)
        .first()
        .expect("boolean condition creates the parameter upper bound");
    let scheme_id = output
        .session
        .generalized_scheme_record(def)
        .expect("same-session local scheme has an opaque provenance association");
    let scheme = machine
        .generalized_scheme_record(scheme_id)
        .expect("associated generalized scheme record exists");
    assert_eq!(scheme.owner, def);
    assert_eq!(scheme.generation, 0);
    let witness_id = *scheme
        .witnesses
        .iter()
        .find(|id| {
            let witness = machine
                .generalized_scheme_witness(**id)
                .expect("record witness");
            witness.path == GeneralizedTypePath(vec![GeneralizedTypePathStep::FunctionArgument])
                && witness.role == GeneralizedWitnessRole::UpperBound
        })
        .expect("finalized function argument has an upper-bound witness");
    let witness = machine
        .generalized_scheme_witness(witness_id)
        .expect("argument witness");
    assert_eq!(witness.completeness, ProvenanceCompleteness::Complete);
    assert!(
        witness
            .incoming
            .iter()
            .any(|edge| { edge.parents == vec![GeneralizationParent::Bound(original)] })
    );
    let query = machine
        .why_generalized_witness(witness_id, ExplanationBudget::default())
        .expect("query generalized witness");
    assert!(
        query
            .nodes
            .iter()
            .any(|node| { node.id() == ExplanationNodeId::Bound(original) })
    );
    assert!(query.nodes.iter().any(|node| matches!(
        node,
        ExplanationNode::Origin {
            kind: ConstraintOriginKind::BodyRequirement(BodyRequirementKind::BooleanCondition),
            ..
        }
    )));
}

#[test]
fn pusp_c_quantified_argument_witness_is_path_specific_and_deduplicated() {
    let output = lower(concat!(
        "my subject(pusp_param) = pusp_param\n",
        "subject(1)\n",
        "subject(false)\n",
    ));
    let def = subject_def(&output);
    let machine = output.session.infer.constraints();
    let scheme_id = output
        .session
        .generalized_scheme_record(def)
        .expect("generic local scheme association");
    let scheme = machine
        .generalized_scheme_record(scheme_id)
        .expect("generic scheme record");
    let argument = GeneralizedTypePath(vec![GeneralizedTypePathStep::FunctionArgument]);
    let witnesses = scheme
        .witnesses
        .iter()
        .filter_map(|id| {
            let witness = machine.generalized_scheme_witness(*id)?;
            (witness.path == argument).then_some(witness)
        })
        .collect::<Vec<_>>();
    assert!(!witnesses.is_empty());
    for witness in witnesses {
        let unique = witness.incoming.iter().collect::<FxHashSet<_>>();
        assert_eq!(unique.len(), witness.incoming.len());
    }
    let coverage = machine.timing().generalized_schemes;
    assert!(coverage.records >= 1);
    assert!(coverage.witnesses >= 1);
    assert_eq!(
        coverage.incoming_edges_considered,
        coverage.incoming_edges_inserted + coverage.incoming_edges_deduplicated
    );
}

#[test]
fn pusp_b_boolean_condition_is_a_located_nonsemantic_source_leaf() {
    const SOURCE: &str = concat!(
        "my subject(pusp_param) = if pusp_param:\n",
        "  1\n",
        "else:\n",
        "  2\n",
        "subject(42)\n",
    );
    let output = lower(SOURCE);
    let parameter = parameter_var(&output, subject_def(&output));
    let machine = output.session.infer.constraints();
    let upper = *bool_upper_records(machine, parameter)
        .first()
        .expect("parameter has a canonical bool upper bound");
    let upper_query = machine
        .why_upper_bound(parameter, upper, ExplanationBudget::default())
        .expect("query bool upper bound");
    let body_leaf = body_requirement_leaf(&upper_query);

    let condition_start = JUNCTION_STD.len()
        + SOURCE
            .find("if pusp_param")
            .expect("fixture contains if condition")
        + "if ".len();
    let location = output
        .session
        .source_boundary_provenance
        .body_requirement(body_leaf.1)
        .expect("body-requirement leaf has source-only location metadata");
    assert_eq!(location.use_span.file, sources::Path::default());
    assert_eq!(
        location.use_span.range,
        sources::SourceRange {
            start: condition_start,
            end: condition_start + "pusp_param".len(),
        }
    );
    assert_eq!(location.context_span, None);

    let exact_roots = machine
        .constraint_records
        .iter()
        .filter(|record| record.root_origins.contains(&body_leaf.0))
        .map(|record| &record.key)
        .collect::<Vec<_>>();
    assert_eq!(exact_roots.len(), 2);
    assert!(exact_roots.iter().any(|key| {
        matches!(machine.types().pos(key.lower), Pos::Con(path, args) if path == &["bool".to_string()] && args.is_empty())
            && matches!(machine.types().neg(key.upper), Neg::Var(_))
    }));
    assert!(exact_roots.iter().any(|key| {
        matches!(machine.types().pos(key.lower), Pos::Var(_))
            && matches!(machine.types().neg(key.upper), Neg::Con(path, args) if path == &["bool".to_string()] && args.is_empty())
    }));

    let timing = output.session.infer.constraint_timing();
    assert_eq!(timing.body_requirement_origins.boolean_condition, 1);
    assert_eq!(timing.body_requirement_origins.operator_operand, 0);
    assert_eq!(timing.body_requirement_origins.pattern_guard, 0);
    assert_eq!(timing.body_requirement_origins.callee_argument, 0);
    assert_eq!(timing.body_requirement_origins.roots_lacking_location, 0);
    assert_eq!(timing.root_origins.body_requirement, 2);
}

#[test]
fn pusp_b_unmigrated_primitive_pattern_requirement_remains_unknown_internal() {
    let output = lower(concat!(
        "my subject(pusp_param) = case pusp_param:\n",
        "  true -> 1\n",
        "  false -> 2\n",
        "subject(false)\n",
    ));
    let parameter = parameter_var(&output, subject_def(&output));
    let machine = output.session.infer.constraints();
    let upper = *bool_upper_records(machine, parameter)
        .first()
        .expect("bool-pattern matching constrains the parameter");
    let query = machine
        .why_upper_bound(parameter, upper, ExplanationBudget::default())
        .expect("query bool-pattern requirement");
    assert!(query.nodes.iter().any(|node| matches!(
        node,
        ExplanationNode::Origin {
            kind: ConstraintOriginKind::UnknownInternal,
            ..
        }
    )));
    assert!(!query.nodes.iter().any(|node| matches!(
        node,
        ExplanationNode::Origin {
            kind: ConstraintOriginKind::BodyRequirement(_),
            ..
        }
    )));
    assert_eq!(
        output
            .session
            .infer
            .constraint_timing()
            .body_requirement_origins,
        BodyRequirementOriginCoverage::default()
    );
}

#[derive(Clone, Copy)]
enum Case {
    SameSession {
        name: &'static str,
        source: &'static str,
    },
    Imported {
        name: &'static str,
        prefix: &'static str,
        suffix: &'static str,
    },
}

impl Case {
    const fn same_session(name: &'static str, source: &'static str) -> Self {
        Self::SameSession { name, source }
    }

    const fn imported(name: &'static str, prefix: &'static str, suffix: &'static str) -> Self {
        Self::Imported {
            name,
            prefix,
            suffix,
        }
    }

    fn capture(self) -> Baseline {
        match self {
            Self::SameSession { name, source } => {
                let output = lower(source);
                Baseline::capture(name, &output, &output)
            }
            Self::Imported {
                name,
                prefix,
                suffix,
            } => {
                let original = lower(prefix);
                let prefix_loaded =
                    sources::load(vec![source_file(&format!("{JUNCTION_STD}{prefix}"))]);
                let cached = lower_loaded_files_prefix(&prefix_loaded).expect("lower PUSP prefix");
                let suffix_loaded = sources::load(vec![source_file(suffix)]);
                let call = lower_loaded_files_with_prefix(&cached, &suffix_loaded)
                    .expect("lower PUSP cached suffix");
                Baseline::capture(name, &original, &call)
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Baseline {
    name: &'static str,
    parameter_var: String,
    relevant_upper_records: Vec<String>,
    parameter_query: Option<QueryBaseline>,
    call_query: Option<QueryBaseline>,
    scheme: String,
    scheme_fnv1a64: u64,
    scc_instantiate_events: usize,
    semantic: SemanticBaseline,
}

impl Baseline {
    fn capture(name: &'static str, definition: &BodyLowering, call: &BodyLowering) -> Self {
        let def = subject_def(definition);
        let parameter = parameter_var(definition, def);
        let machine = definition.session.infer.constraints();
        let relevant = bool_upper_records(machine, parameter);
        let parameter_query = relevant.first().copied().map(|record| {
            let started = Instant::now();
            let query = machine
                .why_upper_bound(parameter, record, ExplanationBudget::default())
                .expect("query original parameter upper bound");
            let elapsed = started.elapsed();
            assert_query_time(name, "parameter", elapsed);
            QueryBaseline::capture(query, Some(record))
        });

        let call_machine = call.session.infer.constraints();
        let call_query = call
            .session
            .ocast_eligibility_shadow()
            .first()
            .map(|classification| {
                let started = Instant::now();
                let query = call_machine
                    .why_constraint(classification.producer, ExplanationBudget::default())
                    .expect("query call-side nominal cast producer");
                let elapsed = started.elapsed();
                assert_query_time(name, "call", elapsed);
                QueryBaseline::capture(
                    query,
                    if std::ptr::eq(definition, call) {
                        relevant.first().copied()
                    } else {
                        None
                    },
                )
            });

        let scheme = match definition.session.poly.defs.get(def) {
            Some(Def::Let {
                scheme: Some(scheme),
                ..
            }) => poly::dump::format_scheme(&definition.session.poly.typ, scheme),
            _ => panic!("subject must have a finalized scheme"),
        };
        let timing = call.session.infer.constraint_timing();
        let ocast = call.session.ocast_eligibility_metrics();
        let poly_dump = poly::dump::dump_arena_with_labels(&call.session.poly, &call.labels);
        let diagnostics = format!("{:?}", call.errors);
        Self {
            name,
            parameter_var: format!("{parameter:?}"),
            relevant_upper_records: relevant
                .iter()
                .map(|record| format!("{record:?}"))
                .collect(),
            parameter_query,
            call_query,
            scheme_fnv1a64: fnv1a64(scheme.as_bytes()),
            scheme,
            scc_instantiate_events: call.timing.analysis.scc_instantiate_events,
            semantic: SemanticBaseline {
                canonical_constraints: timing.canonical_subtype_constraints,
                lower_bounds: timing.lower_bounds_added,
                upper_bounds: timing.upper_bounds_added,
                replay_edges: timing.replay_derivations.inserted,
                nominal_cast_events: timing.nominal_cast_events,
                ocast: [
                    ocast.eligible_source_boundary,
                    ocast.internal_only,
                    ocast.incomplete,
                ],
                ocast_states: call
                    .session
                    .ocast_eligibility_shadow()
                    .iter()
                    .map(|classification| match classification.state() {
                        OcastEligibilityState::EligibleSourceBoundary => "eligible",
                        OcastEligibilityState::InternalOnly => "internal",
                        OcastEligibilityState::Incomplete => "incomplete",
                    })
                    .collect(),
                poly_dump_fnv1a64: fnv1a64(poly_dump.as_bytes()),
                diagnostics_fnv1a64: fnv1a64(diagnostics.as_bytes()),
                diagnostic_count: call.errors.len(),
            },
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct QueryBaseline {
    nodes: usize,
    edges: usize,
    max_depth: usize,
    completeness: ExplanationCompleteness,
    query_fnv1a64: u64,
    origin_kinds: Vec<&'static str>,
    source_leaves: usize,
    has_unlocated_body_root: bool,
    has_internal_root: bool,
    has_unknown_internal_root: bool,
    reaches_original_parameter_bound: bool,
}

impl QueryBaseline {
    fn capture(
        query: ExplanationQueryResult,
        original_parameter_bound: Option<BoundRecordId>,
    ) -> Self {
        let max_depth = query_depth(&query.edges, query.nodes.first().map(ExplanationNode::id));
        let has_unlocated_body_root = query.nodes.iter().any(|node| {
            matches!(
                node,
                ExplanationNode::Origin {
                    kind: ConstraintOriginKind::UnknownInternal | ConstraintOriginKind::Internal,
                    source_boundary: None,
                    ..
                }
            )
        });
        let has_internal_root = query.nodes.iter().any(|node| {
            matches!(
                node,
                ExplanationNode::Origin {
                    kind: ConstraintOriginKind::Internal,
                    ..
                }
            )
        });
        let has_unknown_internal_root = query.nodes.iter().any(|node| {
            matches!(
                node,
                ExplanationNode::Origin {
                    kind: ConstraintOriginKind::UnknownInternal,
                    ..
                }
            )
        });
        let reaches_original_parameter_bound = original_parameter_bound.is_some_and(|record| {
            query
                .nodes
                .iter()
                .any(|node| node.id() == ExplanationNodeId::Bound(record))
        });
        let rendered = format!("{query:?}");
        let origin_kinds = query
            .nodes
            .iter()
            .filter_map(|node| match node {
                ExplanationNode::Origin { kind, .. } => Some(match kind {
                    ConstraintOriginKind::ApplicationArgument => "application-argument",
                    ConstraintOriginKind::Annotation => "annotation",
                    ConstraintOriginKind::Return => "return",
                    ConstraintOriginKind::Field => "field",
                    ConstraintOriginKind::Assignment => "assignment",
                    ConstraintOriginKind::BodyRequirement(
                        BodyRequirementKind::BooleanCondition,
                    ) => "body-requirement:boolean-condition",
                    ConstraintOriginKind::BodyRequirement(
                        BodyRequirementKind::OperatorOperand { .. },
                    ) => "body-requirement:operator-operand",
                    ConstraintOriginKind::BodyRequirement(BodyRequirementKind::PatternGuard) => {
                        "body-requirement:pattern-guard"
                    }
                    ConstraintOriginKind::BodyRequirement(
                        BodyRequirementKind::CalleeArgument { .. },
                    ) => "body-requirement:callee-argument",
                    ConstraintOriginKind::Internal => "internal",
                    ConstraintOriginKind::UnknownInternal => "unknown-internal",
                }),
                _ => None,
            })
            .collect();
        Self {
            nodes: query.nodes.len(),
            edges: query.edges.len(),
            max_depth,
            completeness: query.completeness,
            query_fnv1a64: fnv1a64(rendered.as_bytes()),
            origin_kinds,
            source_leaves: query.source_leaves.len(),
            has_unlocated_body_root,
            has_internal_root,
            has_unknown_internal_root,
            reaches_original_parameter_bound,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct SemanticBaseline {
    canonical_constraints: usize,
    lower_bounds: usize,
    upper_bounds: usize,
    replay_edges: usize,
    nominal_cast_events: usize,
    ocast: [usize; 3],
    ocast_states: Vec<&'static str>,
    poly_dump_fnv1a64: u64,
    diagnostics_fnv1a64: u64,
    diagnostic_count: usize,
}

fn expected_baselines() -> [Baseline; 5] {
    [
        baseline(
            "inferred-if-condition",
            &["BoundRecordId(99)"],
            Some(query(
                19,
                18,
                9,
                4_470_251_554_592_856_540,
                &["internal", "body-requirement:boolean-condition"],
                1,
                [true, true, false, true],
            )),
            Some(query(
                11,
                9,
                6,
                11_821_486_888_323_386_445,
                &["internal", "application-argument"],
                1,
                [true, true, false, false],
            )),
            "bool -> int",
            2,
            semantic(
                [75, 52, 55, 38, 1],
                [1, 0, 0],
                &["eligible"],
                15_505_251_397_583_533_568,
                7_715_097_740_732_590_881,
                1,
            ),
        ),
        baseline(
            "annotated-parameter-control",
            &["BoundRecordId(17)"],
            Some(query(
                20,
                19,
                9,
                11_713_936_874_666_769_891,
                &[
                    "annotation",
                    "internal",
                    "body-requirement:boolean-condition",
                ],
                2,
                [true, true, false, true],
            )),
            Some(query(
                11,
                9,
                6,
                16_270_637_393_438_123_044,
                &["internal", "application-argument"],
                1,
                [true, true, false, false],
            )),
            "bool -> int",
            2,
            semantic(
                [92, 68, 69, 75, 1],
                [1, 0, 0],
                &["eligible"],
                15_505_251_397_583_533_568,
                15_320_303_960_052_524_694,
                1,
            ),
        ),
        baseline(
            "generic-multiple-instantiations",
            &[],
            None,
            None,
            "'a -> 'a",
            2,
            semantic(
                [52, 38, 35, 17, 0],
                [0, 0, 0],
                &[],
                17_944_016_837_335_882_254,
                675_868_731_199_239_589,
                0,
            ),
        ),
        baseline(
            "imported-cache-loaded-callee",
            &["BoundRecordId(90)"],
            Some(query(
                19,
                18,
                9,
                9_503_474_146_436_603_632,
                &["internal", "body-requirement:boolean-condition"],
                1,
                [true, true, false, true],
            )),
            Some(query(
                12,
                9,
                6,
                18_099_679_749_046_801_422,
                &["internal", "unknown-internal", "application-argument"],
                1,
                [true, true, true, false],
            )),
            "bool -> int",
            1,
            semantic(
                [14, 7, 9, 4, 1],
                [0, 0, 1],
                &["incomplete"],
                14_286_268_343_633_309_087,
                675_868_731_199_239_589,
                0,
            ),
        ),
        baseline(
            "multiple-body-uses",
            &["BoundRecordId(160)"],
            Some(query(
                35,
                35,
                9,
                6_700_188_920_353_996_193,
                &[
                    "internal",
                    "body-requirement:boolean-condition",
                    "body-requirement:boolean-condition",
                ],
                2,
                [true, true, false, true],
            )),
            Some(query(
                11,
                9,
                6,
                15_730_201_711_330_801_637,
                &["internal", "application-argument"],
                1,
                [true, true, false, false],
            )),
            "bool -> int",
            3,
            semantic(
                [117, 87, 93, 88, 1],
                [1, 0, 0],
                &["eligible"],
                1_904_004_085_798_493_171,
                10_393_096_561_695_006_901,
                1,
            ),
        ),
    ]
}

#[allow(clippy::too_many_arguments)]
fn baseline(
    name: &'static str,
    relevant_upper_records: &[&str],
    parameter_query: Option<QueryBaseline>,
    call_query: Option<QueryBaseline>,
    scheme: &str,
    scc_instantiate_events: usize,
    semantic: SemanticBaseline,
) -> Baseline {
    Baseline {
        name,
        parameter_var: "TypeVar(14)".into(),
        relevant_upper_records: relevant_upper_records
            .iter()
            .map(|record| (*record).into())
            .collect(),
        parameter_query,
        call_query,
        scheme: scheme.into(),
        scheme_fnv1a64: fnv1a64(scheme.as_bytes()),
        scc_instantiate_events,
        semantic,
    }
}

fn query(
    nodes: usize,
    edges: usize,
    max_depth: usize,
    query_fnv1a64: u64,
    origin_kinds: &[&'static str],
    source_leaves: usize,
    flags: [bool; 4],
) -> QueryBaseline {
    QueryBaseline {
        nodes,
        edges,
        max_depth,
        completeness: ExplanationCompleteness::Complete,
        query_fnv1a64,
        origin_kinds: origin_kinds.to_vec(),
        source_leaves,
        has_unlocated_body_root: flags[0],
        has_internal_root: flags[1],
        has_unknown_internal_root: flags[2],
        reaches_original_parameter_bound: flags[3],
    }
}

fn semantic(
    counts: [usize; 5],
    ocast: [usize; 3],
    ocast_states: &[&'static str],
    poly_dump_fnv1a64: u64,
    diagnostics_fnv1a64: u64,
    diagnostic_count: usize,
) -> SemanticBaseline {
    SemanticBaseline {
        canonical_constraints: counts[0],
        lower_bounds: counts[1],
        upper_bounds: counts[2],
        replay_edges: counts[3],
        nominal_cast_events: counts[4],
        ocast,
        ocast_states: ocast_states.to_vec(),
        poly_dump_fnv1a64,
        diagnostics_fnv1a64,
        diagnostic_count,
    }
}

fn assert_query_time(case: &str, query: &str, elapsed: Duration) {
    eprintln!("PUSP-A {case} {query} query elapsed: {elapsed:?}");
    assert!(
        elapsed < Duration::from_millis(100),
        "{case} {query} explanation query unexpectedly slow: {elapsed:?}"
    );
}

fn lower(source: &str) -> BodyLowering {
    let loaded = sources::load(vec![source_file(&format!("{JUNCTION_STD}{source}"))]);
    lower_loaded_files(&loaded).expect("lower PUSP characterization source")
}

fn source_file(source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }
}

fn subject_def(output: &BodyLowering) -> DefId {
    output
        .modules
        .value_path_at(
            output.modules.root_id(),
            &[Name("subject".to_string())],
            ModuleOrder::from_index(u32::MAX),
        )
        .expect("subject definition")
}

fn parameter_var(output: &BodyLowering, def: DefId) -> TypeVar {
    let body = match output.session.poly.defs.get(def) {
        Some(Def::Let {
            body: Some(body), ..
        }) => *body,
        _ => panic!("subject body"),
    };
    let parameter = match output.session.poly.expr(body) {
        Expr::Lambda(pat, _) => match output.session.poly.pat(*pat) {
            Pat::Var(def) => *def,
            _ => panic!("subject parameter variable pattern"),
        },
        _ => panic!("subject lambda"),
    };
    output
        .session
        .local_defs
        .get(parameter)
        .expect("parameter local definition")
        .value
}

fn bool_upper_records(machine: &ConstraintMachine, var: TypeVar) -> Vec<BoundRecordId> {
    machine
        .bounds()
        .of(var)
        .into_iter()
        .flat_map(|bounds| bounds.upper_record_ids().iter().copied())
        .filter(|record| {
            let Some(BoundRecord {
                endpoint: BoundEndpoint::Upper(neg),
                ..
            }) = machine.bounds().record(*record)
            else {
                return false;
            };
            matches!(machine.types().neg(*neg), Neg::Con(path, args) if path == &["bool".to_string()] && args.is_empty())
        })
        .collect()
}

fn body_requirement_leaf(query: &ExplanationQueryResult) -> (OriginId, SourceBoundaryId) {
    let leaves = query
        .nodes
        .iter()
        .filter_map(|node| match node {
            ExplanationNode::Origin {
                id,
                kind: ConstraintOriginKind::BodyRequirement(BodyRequirementKind::BooleanCondition),
                source_boundary: Some(boundary),
            } => Some((*id, *boundary)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(leaves.len(), 1, "one BooleanCondition root: {query:#?}");
    leaves[0]
}

fn query_depth(edges: &[ExplanationEdge], root: Option<ExplanationNodeId>) -> usize {
    fn visit(
        node: ExplanationNodeId,
        depth: usize,
        edges: &[ExplanationEdge],
        path: &mut Vec<ExplanationNodeId>,
    ) -> usize {
        if path.contains(&node) {
            return depth;
        }
        path.push(node);
        let result = edges
            .iter()
            .filter(|edge| edge.child == node)
            .flat_map(|edge| edge.parents.iter().copied())
            .map(|parent| visit(parent, depth + 1, edges, path))
            .max()
            .unwrap_or(depth);
        path.pop();
        result
    }
    root.map(|root| visit(root, 0, edges, &mut Vec::new()))
        .unwrap_or(0)
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    const OFFSET: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;
    bytes.iter().fold(OFFSET, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(PRIME)
    })
}
