use super::*;
use rowan::SyntaxNode;
use yulang_parser::sink::YulangLanguage;

fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
where
    T: Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("infer-lib-test".to_string())
        .stack_size(16 * 1024 * 1024)
        .spawn(f)
        .expect("spawn test thread");
    handle.join().expect("test thread panicked")
}

fn parse_and_lower(src: &str) -> LowerState {
    let green = yulang_parser::parse_module_to_green(src);
    let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
    let mut state = LowerState::new();
    lower_root(&mut state, &root);
    state
}

fn assert_expected_edge_solver_constraint(state: &LowerState, edge: &diagnostic::ExpectedEdge) {
    if edge.kind == diagnostic::ExpectedEdgeKind::RepresentationCoerce {
        return;
    }

    let expected_lowers = state.infer.lowers_of(edge.expected_tv);
    assert!(
        expected_lowers
            .iter()
            .any(|pos| matches!(pos, Pos::Var(tv) if *tv == edge.actual_tv)),
        "expected edge should add actual as expected lower: {edge:?}, lowers={expected_lowers:?}",
    );

    let actual_uppers = state.infer.uppers_of(edge.actual_tv);
    assert!(
        actual_uppers
            .iter()
            .any(|neg| matches!(neg, Neg::Var(tv) if *tv == edge.expected_tv)),
        "expected edge should add expected as actual upper: {edge:?}, uppers={actual_uppers:?}",
    );

    if let (Some(actual_eff), Some(expected_eff)) = (edge.actual_eff, edge.expected_eff) {
        let expected_eff_lowers = state.infer.lowers_of(expected_eff);
        assert!(
            expected_eff_lowers
                .iter()
                .any(|pos| matches!(pos, Pos::Var(tv) if *tv == actual_eff)),
            "effect edge should add actual effect as expected lower: {edge:?}, lowers={expected_eff_lowers:?}",
        );

        let actual_eff_uppers = state.infer.uppers_of(actual_eff);
        assert!(
            actual_eff_uppers
                .iter()
                .any(|neg| matches!(neg, Neg::Var(tv) if *tv == expected_eff)),
            "effect edge should add expected effect as actual upper: {edge:?}, uppers={actual_eff_uppers:?}",
        );
    }
}

fn assert_expected_edge_reason_matches_kind(edge: &diagnostic::ExpectedEdge) {
    use crate::diagnostic::ConstraintReason as Reason;
    use crate::diagnostic::ExpectedEdgeKind as Kind;

    let matches_kind = matches!(
        (edge.kind, &edge.cause.reason),
        (Kind::IfCondition, Reason::IfCondition)
            | (Kind::IfBranch, Reason::IfBranch)
            | (Kind::MatchGuard, Reason::MatchGuard)
            | (Kind::MatchBranch, Reason::MatchBranch)
            | (Kind::CatchGuard, Reason::CatchGuard)
            | (Kind::CatchBranch, Reason::CatchBranch)
            | (Kind::ApplicationCallee, Reason::ApplyArg)
            | (Kind::ApplicationArgument, Reason::ApplyArg)
            | (Kind::Annotation, Reason::Annotation)
            | (Kind::AssignmentValue, Reason::AssignmentValue)
            | (Kind::RepresentationCoerce, Reason::RepresentationCoerce)
    );
    assert!(
        matches_kind,
        "expected edge kind and cause reason should match: {edge:?}",
    );
}

#[test]
fn simple_binding() {
    let state = parse_and_lower("my x = 42");
    // x が locals か module に登録されているはず
    let name = symbols::Name("x".to_string());
    let found = state.ctx.resolve_value(&name);
    assert!(found.is_some(), "x should be registered");
}

#[test]
fn path_sep_lookup() {
    let state = parse_and_lower("our foo = 1\nmy y = foo");
    let name = symbols::Name("foo".to_string());
    assert!(
        state.ctx.resolve_value(&name).is_some(),
        "foo should be in module"
    );
}

#[test]
fn function_def_args() {
    // my f x = x は Lam(x_def, Var(x_def)) に lower されるはず
    let state = parse_and_lower("my f x = x");
    let f = symbols::Name("f".to_string());
    assert!(
        state.ctx.resolve_value(&f).is_some(),
        "f should be registered"
    );
}

#[test]
fn with_block_our_defs_scope_over_body_not_module() {
    let state = parse_and_lower("my x = y with:\n  our y = 1\n");
    assert!(
        state
            .ctx
            .resolve_value(&symbols::Name("x".to_string()))
            .is_some(),
        "x should be registered"
    );
    assert!(
        state
            .ctx
            .resolve_value(&symbols::Name("y".to_string()))
            .is_none(),
        "with `our` y should stay local to the synthetic with module"
    );
    assert!(
        !state.ctx.refs.unresolved().iter().any(|(_, unresolved)| {
            unresolved.path.segments == vec![symbols::Name("y".to_string())]
        }),
        "the body should resolve y through the following with `our` binding"
    );
}

#[test]
fn with_block_my_defs_do_not_scope_over_body() {
    let state = parse_and_lower("my x = y with:\n  my y = 1\n");
    assert!(
        state
            .ctx
            .resolve_value(&symbols::Name("x".to_string()))
            .is_some(),
        "x should be registered"
    );
    assert!(
        state
            .ctx
            .resolve_value(&symbols::Name("y".to_string()))
            .is_none(),
        "with `my` y should stay local to the with block"
    );
    assert!(
        state.ctx.refs.unresolved().iter().any(|(_, unresolved)| {
            unresolved.path.segments == vec![symbols::Name("y".to_string())]
        }),
        "the body should not see a following with `my` binding"
    );
}

#[test]
fn annotated_applyc_header_is_treated_as_function_binding() {
    let state = parse_and_lower("my f(x: [_] _) = x");
    let f_def = state
        .ctx
        .resolve_value(&symbols::Name("f".to_string()))
        .unwrap();
    let f_tv = state.def_tvs[&f_def];
    let lowers = state.infer.lowers_of(f_tv);
    assert!(
        lowers.iter().any(|p| matches!(p, Pos::Fun { .. })),
        "annotated ApplyC header should still lower as a function binding",
    );
}

#[test]
fn constraints_emitted() {
    // `my x = 42` で:
    // - 42 の tv に Pos::Con("int") が lower として入る
    // - x の def_tv に 42.tv が lower として入る（body.tv <: def_tv）
    let state = parse_and_lower("my x = 42");
    let x_name = symbols::Name("x".to_string());
    let x_def = state.ctx.resolve_value(&x_name).expect("x should exist");
    let x_tv = state.def_tvs[&x_def];

    // x_tv には lower bound が少なくとも 1 つある（42.tv <: x_tv）
    let lowers = state.infer.lowers_of(x_tv);
    assert!(
        !lowers.is_empty(),
        "x's def_tv should have a lower bound from body"
    );
}

#[test]
fn effectful_value_binding_still_gets_value_lower_bound() {
    let state = parse_and_lower("act undet:\n  our bool: () -> bool\n\nmy y = undet::bool()");
    let y_def = state
        .ctx
        .resolve_value(&symbols::Name("y".to_string()))
        .unwrap();
    let y_tv = state.def_tvs[&y_def];
    let lowers = state.infer.lowers_of(y_tv);
    assert!(
        !lowers.is_empty(),
        "effectful binding should still keep value lower bounds, got {:?}",
        lowers,
    );
}

#[test]
fn binding_type_annotation_mismatch_surfaces_type_error() {
    let state = parse_and_lower("my x: bool = 1");
    let errors = state.infer.type_errors();
    assert_eq!(
        errors.len(),
        1,
        "expected one deduplicated error, got {errors:?}"
    );
    assert!(
        errors.iter().any(|error| {
            error.cause.reason == ConstraintReason::Annotation
                && error.kind == TypeErrorKind::ConstructorMismatch
        }),
        "binding annotation mismatch should surface an annotation error, got {errors:?}",
    );
}

#[test]
fn binding_type_annotation_records_expected_edge() {
    let state = parse_and_lower("my x: int = 1");
    let annotation_edges = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::Annotation)
        .count();
    assert_eq!(annotation_edges, 1);
}

#[test]
fn int_binding_can_widen_to_float_annotation() {
    let state = parse_and_lower("my x: float = 1");
    let errors = state.infer.type_errors();
    assert!(
        errors.is_empty(),
        "int <: float annotation should be accepted, got {errors:?}",
    );
}

#[test]
fn parameter_type_annotation_records_expected_edge() {
    let state = parse_and_lower("my id(x: int) = x");
    let annotation_edges = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::Annotation)
        .count();
    assert_eq!(annotation_edges, 1);
}

#[test]
fn application_argument_records_expected_edge() {
    let state = parse_and_lower("my id x = x\nmy y = id 1");
    let application_edges = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationArgument)
        .count();
    assert_eq!(application_edges, 1);
}

#[test]
fn application_callee_records_expected_edge() {
    let state = parse_and_lower("my id x = x\nmy y = id 1");
    let application_edges = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationCallee)
        .count();
    assert_eq!(application_edges, 1);
}

#[test]
fn application_callee_edge_links_to_apply_evidence() {
    let mut state = parse_and_lower("my id(x: int) = x\nid 1");
    let application_edge_ids = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationCallee)
        .map(|edge| edge.id.0)
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        !application_edge_ids.is_empty(),
        "expected application callee edge"
    );

    let program = export_core_program(&mut state);
    let evidence_source_edges = apply_evidence_callee_source_edges_in_module(&program.program);
    assert!(
        application_edge_ids
            .iter()
            .all(|edge_id| evidence_source_edges.contains(edge_id)),
        "expected every application callee edge to have matching ApplyEvidence source, edges={application_edge_ids:?}, evidence_sources={evidence_source_edges:?}",
    );
}

#[test]
fn application_callee_edge_links_to_expected_callee_evidence() {
    let mut state = parse_and_lower("my id(x: int) = x\nid 1");
    let application_edge_ids = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationCallee)
        .map(|edge| edge.id.0)
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        !application_edge_ids.is_empty(),
        "expected application callee edge"
    );

    let program = export_core_program(&mut state);
    let apply_evidence = apply_evidence_callee_source_expected_callees_in_module(&program.program);
    for edge_id in &application_edge_ids {
        let expected_callee = apply_evidence
            .iter()
            .find_map(|(source_edge, expected_callee)| {
                (*source_edge == *edge_id).then_some(expected_callee)
            })
            .unwrap_or_else(|| panic!("missing apply evidence for callee source edge #{edge_id}"));
        let expected_callee = expected_callee
            .as_ref()
            .unwrap_or_else(|| panic!("missing expected_callee for callee source edge #{edge_id}"));
        assert!(
            expected_callee.lower.is_some() || expected_callee.upper.is_some(),
            "expected ApplyEvidence.expected_callee to expose bounds for source edge #{edge_id}: {expected_callee:?}",
        );
    }
}

#[test]
fn application_argument_edge_links_to_apply_evidence() {
    let mut state = parse_and_lower("my id(x: int) = x\nid 1");
    let application_edge_ids = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationArgument)
        .map(|edge| edge.id.0)
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        !application_edge_ids.is_empty(),
        "expected application argument edge"
    );

    let program = export_core_program(&mut state);
    let evidence_source_edges = apply_evidence_source_edges_in_module(&program.program);
    assert!(
        application_edge_ids
            .iter()
            .all(|edge_id| evidence_source_edges.contains(edge_id)),
        "expected every application argument edge to have matching ApplyEvidence source, edges={application_edge_ids:?}, evidence_sources={evidence_source_edges:?}",
    );
}

#[test]
fn application_argument_edge_links_to_expected_edge_evidence() {
    let mut state = parse_and_lower("my id(x: int) = x\nid 1");
    let application_edge_ids = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationArgument)
        .map(|edge| edge.id.0)
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        !application_edge_ids.is_empty(),
        "expected application argument edge"
    );

    let expected_edge_evidence = collect_expected_edge_evidence(&state);
    for edge_id in &application_edge_ids {
        let evidence = expected_edge_evidence
            .iter()
            .find(|evidence| evidence.id.0 == *edge_id)
            .unwrap_or_else(|| panic!("missing expected edge evidence for #{edge_id}"));
        assert_eq!(
            evidence.kind,
            diagnostic::ExpectedEdgeKind::ApplicationArgument
        );
        assert!(
            evidence.expected.lower.is_some() || evidence.expected.upper.is_some(),
            "expected application argument edge evidence to expose expected bounds: {evidence:?}",
        );
    }

    let program = export_core_program(&mut state);
    let apply_evidence = apply_evidence_source_expected_args_in_module(&program.program);
    for edge_id in &application_edge_ids {
        let expected_arg = apply_evidence
            .iter()
            .find_map(|(source_edge, expected_arg)| {
                (*source_edge == *edge_id).then_some(expected_arg)
            })
            .unwrap_or_else(|| panic!("missing apply evidence for source edge #{edge_id}"));
        let expected_arg = expected_arg
            .as_ref()
            .unwrap_or_else(|| panic!("missing expected_arg for source edge #{edge_id}"));
        assert!(
            expected_arg.lower.is_some() || expected_arg.upper.is_some(),
            "expected ApplyEvidence.expected_arg to expose bounds for source edge #{edge_id}: {expected_arg:?}",
        );
    }
}

#[test]
fn core_program_carries_expected_edge_evidence_table() {
    let mut state = parse_and_lower("my id(x: int) = x\nid 1");
    let application_edge_ids = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationArgument)
        .map(|edge| edge.id.0)
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        !application_edge_ids.is_empty(),
        "expected application argument edge"
    );

    let program = export_core_program(&mut state);
    for edge_id in &application_edge_ids {
        let edge = program
            .evidence
            .expected_edge(*edge_id)
            .unwrap_or_else(|| panic!("missing core principal evidence for edge #{edge_id}"));
        assert_eq!(
            edge.kind,
            yulang_core_ir::ExpectedEdgeKind::ApplicationArgument
        );
        assert!(
            edge.expected.lower.is_some() || edge.expected.upper.is_some(),
            "expected core principal evidence to expose expected bounds: {edge:?}",
        );
    }
}

#[test]
fn effect_operation_application_records_adapter_edge() {
    let mut state = parse_and_lower("pub act out:\n  pub say: str -> ()\n\nout::say \"hi\"\n");
    let adapter_edge = state
        .expected_adapter_edges
        .iter()
        .find(|edge| edge.kind == diagnostic::ExpectedAdapterEdgeKind::EffectOperationArgument)
        .expect("effect operation argument adapter edge");

    assert!(adapter_edge.source_expected_edge.is_some());
    assert!(adapter_edge.actual_value.is_some());
    assert!(adapter_edge.expected_value.is_some());
    assert!(adapter_edge.actual_effect.is_some());
    assert!(adapter_edge.expected_effect.is_some());

    let adapter_edge_id = adapter_edge.id.0;
    let source_expected_edge_id = adapter_edge
        .source_expected_edge
        .expect("adapter should link source expected edge")
        .0;
    let program = export_core_program(&mut state);
    let core_adapter = program
        .evidence
        .expected_adapter_edge(adapter_edge_id)
        .expect("core principal adapter evidence");

    assert_eq!(
        core_adapter.kind,
        yulang_core_ir::ExpectedAdapterEdgeKind::EffectOperationArgument
    );
    assert_eq!(
        core_adapter.source_expected_edge,
        Some(source_expected_edge_id)
    );
    assert!(core_adapter.actual_value.is_some());
    assert!(core_adapter.expected_value.is_some());
    assert!(core_adapter.actual_effect.is_some());
    assert!(core_adapter.expected_effect.is_some());
}

#[test]
fn catch_records_handler_adapter_edges() {
    let mut state = parse_and_lower(
        "pub act out:\n  pub say: str -> ()\n\ncatch out::say \"hi\":\n    out::say msg, k -> k ()\n",
    );

    let residual = state
        .expected_adapter_edges
        .iter()
        .find(|edge| edge.kind == diagnostic::ExpectedAdapterEdgeKind::HandlerResidual)
        .expect("handler residual adapter edge");
    assert!(residual.source_expected_edge.is_none());
    assert!(residual.actual_value.is_some());
    assert!(residual.expected_value.is_some());
    assert!(residual.actual_effect.is_some());
    assert!(residual.expected_effect.is_some());

    let handler_return = state
        .expected_adapter_edges
        .iter()
        .find(|edge| edge.kind == diagnostic::ExpectedAdapterEdgeKind::HandlerReturn)
        .expect("handler return adapter edge");
    assert!(handler_return.source_expected_edge.is_some());
    assert!(handler_return.actual_value.is_some());
    assert!(handler_return.expected_value.is_some());
    assert!(handler_return.actual_effect.is_some());
    assert!(handler_return.expected_effect.is_some());

    let resume_arg = state
        .expected_adapter_edges
        .iter()
        .find(|edge| edge.kind == diagnostic::ExpectedAdapterEdgeKind::ResumeArgument)
        .expect("resume argument adapter edge");
    assert!(resume_arg.source_expected_edge.is_some());
    assert!(resume_arg.actual_value.is_some());
    assert!(resume_arg.expected_value.is_some());
    assert!(resume_arg.actual_effect.is_some());
    assert!(resume_arg.expected_effect.is_some());

    let program = export_core_program(&mut state);
    assert!(
        program
            .evidence
            .expected_adapter_edges
            .iter()
            .any(|edge| edge.kind == yulang_core_ir::ExpectedAdapterEdgeKind::HandlerResidual)
    );
    assert!(
        program
            .evidence
            .expected_adapter_edges
            .iter()
            .any(|edge| edge.kind == yulang_core_ir::ExpectedAdapterEdgeKind::HandlerReturn)
    );
    assert!(
        program
            .evidence
            .expected_adapter_edges
            .iter()
            .any(|edge| edge.kind == yulang_core_ir::ExpectedAdapterEdgeKind::ResumeArgument)
    );
}

#[test]
fn expected_edges_keep_solver_constraints() {
    let state = parse_and_lower("my id(x: int) = x\nmy f(b: bool) = if b { id 1 } else { id 2 }");
    assert!(
        state
            .expected_edges
            .iter()
            .any(|edge| edge.kind == diagnostic::ExpectedEdgeKind::Annotation)
    );
    assert!(
        state
            .expected_edges
            .iter()
            .any(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationArgument)
    );
    assert!(
        state
            .expected_edges
            .iter()
            .any(|edge| edge.kind == diagnostic::ExpectedEdgeKind::IfCondition)
    );
    assert!(
        state
            .expected_edges
            .iter()
            .any(|edge| edge.kind == diagnostic::ExpectedEdgeKind::IfBranch)
    );

    for edge in &state.expected_edges {
        assert_expected_edge_reason_matches_kind(edge);
        assert_expected_edge_solver_constraint(&state, edge);
    }
}

#[test]
fn synthetic_representation_coerce_records_expected_edges() {
    let state = parse_and_lower(
        "struct point { x: int, y: int }\nmy p = point { x: 1, y: 2 }\nmy px = p.x",
    );
    let representation_edges = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::RepresentationCoerce)
        .collect::<Vec<_>>();
    assert!(
        representation_edges.len() >= 2,
        "struct constructor and field projection should record representation edges, got {representation_edges:?}",
    );
    for edge in representation_edges {
        assert_expected_edge_reason_matches_kind(edge);
        let (Some(actual_eff), Some(expected_eff)) = (edge.actual_eff, edge.expected_eff) else {
            panic!("representation edge should record effect flow: {edge:?}");
        };
        let expected_eff_lowers = state.infer.lowers_of(expected_eff);
        assert!(
            expected_eff_lowers
                .iter()
                .any(|pos| matches!(pos, Pos::Var(tv) if *tv == actual_eff)),
            "representation coerce should constrain inner effect into wrapper effect: {edge:?}, lowers={expected_eff_lowers:?}",
        );
    }
}

#[test]
fn synthetic_representation_coerce_edges_have_core_evidence() {
    let mut state = parse_and_lower("struct point { x: int }\nmy p = point { x: 1 }\nmy px = p.x");
    let representation_edge_ids = state
        .expected_edges
        .iter()
        .filter(|edge| edge.kind == diagnostic::ExpectedEdgeKind::RepresentationCoerce)
        .map(|edge| edge.id.0)
        .collect::<std::collections::BTreeSet<_>>();
    let representation_edge_count = representation_edge_ids.len();
    assert!(
        representation_edge_count >= 2,
        "expected representation edges for struct helpers, got {:?}",
        state.expected_edges,
    );

    let program = export_core_program(&mut state);
    let coerce_evidence_count = count_coerce_evidence_in_module(&program.program);
    let concrete_coerce_evidence_count = count_concrete_coerce_evidence_in_module(&program.program);
    assert!(
        coerce_evidence_count >= representation_edge_count,
        "expected core CoerceEvidence for representation edges, edges={representation_edge_count}, evidence={coerce_evidence_count}",
    );
    assert!(
        concrete_coerce_evidence_count > 0,
        "expected at least one concrete CoerceEvidence for representation edges",
    );
    let evidence_source_edges = coerce_evidence_source_edges_in_module(&program.program);
    assert!(
        representation_edge_ids
            .iter()
            .all(|edge_id| evidence_source_edges.contains(edge_id)),
        "expected every representation edge to have matching core CoerceEvidence source, edges={representation_edge_ids:?}, evidence_sources={evidence_source_edges:?}",
    );
}

fn count_coerce_evidence_in_module(module: &yulang_core_ir::PrincipalModule) -> usize {
    module
        .bindings
        .iter()
        .map(|binding| count_coerce_evidence(&binding.body))
        .sum::<usize>()
        + module
            .root_exprs
            .iter()
            .map(count_coerce_evidence)
            .sum::<usize>()
}

fn count_concrete_coerce_evidence_in_module(module: &yulang_core_ir::PrincipalModule) -> usize {
    module
        .bindings
        .iter()
        .map(|binding| count_concrete_coerce_evidence(&binding.body))
        .sum::<usize>()
        + module
            .root_exprs
            .iter()
            .map(count_concrete_coerce_evidence)
            .sum::<usize>()
}

fn apply_evidence_source_edges_in_module(
    module: &yulang_core_ir::PrincipalModule,
) -> std::collections::BTreeSet<u32> {
    let mut source_edges = std::collections::BTreeSet::new();
    for binding in &module.bindings {
        collect_apply_evidence_source_edges(&binding.body, &mut source_edges);
    }
    for expr in &module.root_exprs {
        collect_apply_evidence_source_edges(expr, &mut source_edges);
    }
    source_edges
}

fn apply_evidence_callee_source_edges_in_module(
    module: &yulang_core_ir::PrincipalModule,
) -> std::collections::BTreeSet<u32> {
    let mut source_edges = std::collections::BTreeSet::new();
    for binding in &module.bindings {
        collect_apply_evidence_callee_source_edges(&binding.body, &mut source_edges);
    }
    for expr in &module.root_exprs {
        collect_apply_evidence_callee_source_edges(expr, &mut source_edges);
    }
    source_edges
}

fn collect_apply_evidence_callee_source_edges(
    expr: &yulang_core_ir::Expr,
    source_edges: &mut std::collections::BTreeSet<u32>,
) {
    visit_core_expr(expr, &mut |expr| {
        if let yulang_core_ir::Expr::Apply { evidence, .. } = expr
            && let Some(source_edge) = evidence
                .as_ref()
                .and_then(|evidence| evidence.callee_source_edge)
        {
            source_edges.insert(source_edge);
        }
    });
}

fn collect_apply_evidence_source_edges(
    expr: &yulang_core_ir::Expr,
    source_edges: &mut std::collections::BTreeSet<u32>,
) {
    visit_core_expr(expr, &mut |expr| {
        if let yulang_core_ir::Expr::Apply { evidence, .. } = expr
            && let Some(source_edge) = evidence
                .as_ref()
                .and_then(|evidence| evidence.arg_source_edge)
        {
            source_edges.insert(source_edge);
        }
    });
}

fn apply_evidence_callee_source_expected_callees_in_module(
    module: &yulang_core_ir::PrincipalModule,
) -> Vec<(u32, Option<yulang_core_ir::TypeBounds>)> {
    let mut source_edges = Vec::new();
    for binding in &module.bindings {
        collect_apply_evidence_callee_source_expected_callees(&binding.body, &mut source_edges);
    }
    for expr in &module.root_exprs {
        collect_apply_evidence_callee_source_expected_callees(expr, &mut source_edges);
    }
    source_edges
}

fn collect_apply_evidence_callee_source_expected_callees(
    expr: &yulang_core_ir::Expr,
    source_edges: &mut Vec<(u32, Option<yulang_core_ir::TypeBounds>)>,
) {
    visit_core_expr(expr, &mut |expr| {
        if let yulang_core_ir::Expr::Apply { evidence, .. } = expr
            && let Some(evidence) = evidence
            && let Some(source_edge) = evidence.callee_source_edge
        {
            source_edges.push((source_edge, evidence.expected_callee.clone()));
        }
    });
}

fn apply_evidence_source_expected_args_in_module(
    module: &yulang_core_ir::PrincipalModule,
) -> Vec<(u32, Option<yulang_core_ir::TypeBounds>)> {
    let mut source_edges = Vec::new();
    for binding in &module.bindings {
        collect_apply_evidence_source_expected_args(&binding.body, &mut source_edges);
    }
    for expr in &module.root_exprs {
        collect_apply_evidence_source_expected_args(expr, &mut source_edges);
    }
    source_edges
}

fn collect_apply_evidence_source_expected_args(
    expr: &yulang_core_ir::Expr,
    source_edges: &mut Vec<(u32, Option<yulang_core_ir::TypeBounds>)>,
) {
    visit_core_expr(expr, &mut |expr| {
        if let yulang_core_ir::Expr::Apply { evidence, .. } = expr
            && let Some(evidence) = evidence
            && let Some(source_edge) = evidence.arg_source_edge
        {
            source_edges.push((source_edge, evidence.expected_arg.clone()));
        }
    });
}

fn coerce_evidence_source_edges_in_module(
    module: &yulang_core_ir::PrincipalModule,
) -> std::collections::BTreeSet<u32> {
    let mut source_edges = std::collections::BTreeSet::new();
    for binding in &module.bindings {
        collect_coerce_evidence_source_edges(&binding.body, &mut source_edges);
    }
    for expr in &module.root_exprs {
        collect_coerce_evidence_source_edges(expr, &mut source_edges);
    }
    source_edges
}

fn collect_coerce_evidence_source_edges(
    expr: &yulang_core_ir::Expr,
    source_edges: &mut std::collections::BTreeSet<u32>,
) {
    visit_core_expr(expr, &mut |expr| {
        if let yulang_core_ir::Expr::Coerce { evidence, .. } = expr
            && let Some(source_edge) = evidence.as_ref().and_then(|evidence| evidence.source_edge)
        {
            source_edges.insert(source_edge);
        }
    });
}

fn visit_core_expr(expr: &yulang_core_ir::Expr, visitor: &mut impl FnMut(&yulang_core_ir::Expr)) {
    visitor(expr);
    match expr {
        yulang_core_ir::Expr::Coerce { expr, .. } => visit_core_expr(expr, visitor),
        yulang_core_ir::Expr::Lambda { body, .. }
        | yulang_core_ir::Expr::Pack { expr: body, .. } => visit_core_expr(body, visitor),
        yulang_core_ir::Expr::Apply { callee, arg, .. } => {
            visit_core_expr(callee, visitor);
            visit_core_expr(arg, visitor);
        }
        yulang_core_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            visit_core_expr(cond, visitor);
            visit_core_expr(then_branch, visitor);
            visit_core_expr(else_branch, visitor);
        }
        yulang_core_ir::Expr::Tuple(items) => {
            for item in items {
                visit_core_expr(item, visitor);
            }
        }
        yulang_core_ir::Expr::Record { fields, spread } => {
            for field in fields {
                visit_core_expr(&field.value, visitor);
            }
            if let Some(
                yulang_core_ir::RecordSpreadExpr::Head(expr)
                | yulang_core_ir::RecordSpreadExpr::Tail(expr),
            ) = spread
            {
                visit_core_expr(expr, visitor);
            }
        }
        yulang_core_ir::Expr::Variant { value, .. } => {
            if let Some(value) = value {
                visit_core_expr(value, visitor);
            }
        }
        yulang_core_ir::Expr::Select { base, .. } => {
            visit_core_expr(base, visitor);
        }
        yulang_core_ir::Expr::Match {
            scrutinee, arms, ..
        } => {
            visit_core_expr(scrutinee, visitor);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    visit_core_expr(guard, visitor);
                }
                visit_core_expr(&arm.body, visitor);
            }
        }
        yulang_core_ir::Expr::Block { stmts, tail } => {
            for stmt in stmts {
                match stmt {
                    yulang_core_ir::Stmt::Let { value, .. } | yulang_core_ir::Stmt::Expr(value) => {
                        visit_core_expr(value, visitor);
                    }
                    yulang_core_ir::Stmt::Module { body, .. } => {
                        visit_core_expr(body, visitor);
                    }
                }
            }
            if let Some(tail) = tail {
                visit_core_expr(tail, visitor);
            }
        }
        yulang_core_ir::Expr::Handle { body, arms, .. } => {
            visit_core_expr(body, visitor);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    visit_core_expr(guard, visitor);
                }
                visit_core_expr(&arm.body, visitor);
            }
        }
        yulang_core_ir::Expr::Var(_)
        | yulang_core_ir::Expr::PrimitiveOp(_)
        | yulang_core_ir::Expr::Lit(_) => {}
    }
}

fn count_coerce_evidence(expr: &yulang_core_ir::Expr) -> usize {
    count_coerce_evidence_by(expr, &|_| true)
}

fn count_concrete_coerce_evidence(expr: &yulang_core_ir::Expr) -> usize {
    count_coerce_evidence_by(expr, &coerce_evidence_is_concrete)
}

fn count_coerce_evidence_by(
    expr: &yulang_core_ir::Expr,
    accepts: &impl Fn(&yulang_core_ir::CoerceEvidence) -> bool,
) -> usize {
    match expr {
        yulang_core_ir::Expr::Coerce { evidence, expr } => {
            usize::from(evidence.as_ref().is_some_and(accepts))
                + count_coerce_evidence_by(expr, accepts)
        }
        yulang_core_ir::Expr::Lambda { body, .. }
        | yulang_core_ir::Expr::Pack { expr: body, .. } => count_coerce_evidence_by(body, accepts),
        yulang_core_ir::Expr::Apply { callee, arg, .. } => {
            count_coerce_evidence_by(callee, accepts) + count_coerce_evidence_by(arg, accepts)
        }
        yulang_core_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            count_coerce_evidence_by(cond, accepts)
                + count_coerce_evidence_by(then_branch, accepts)
                + count_coerce_evidence_by(else_branch, accepts)
        }
        yulang_core_ir::Expr::Tuple(items) => items
            .iter()
            .map(|item| count_coerce_evidence_by(item, accepts))
            .sum(),
        yulang_core_ir::Expr::Record { fields, spread } => {
            fields
                .iter()
                .map(|field| count_coerce_evidence_by(&field.value, accepts))
                .sum::<usize>()
                + match spread {
                    Some(yulang_core_ir::RecordSpreadExpr::Head(expr))
                    | Some(yulang_core_ir::RecordSpreadExpr::Tail(expr)) => {
                        count_coerce_evidence_by(expr, accepts)
                    }
                    None => 0,
                }
        }
        yulang_core_ir::Expr::Variant { value, .. } => value
            .as_deref()
            .map(|value| count_coerce_evidence_by(value, accepts))
            .unwrap_or(0),
        yulang_core_ir::Expr::Select { base, .. } => count_coerce_evidence_by(base, accepts),
        yulang_core_ir::Expr::Match {
            scrutinee, arms, ..
        } => {
            count_coerce_evidence_by(scrutinee, accepts)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard
                            .as_ref()
                            .map(|guard| count_coerce_evidence_by(guard, accepts))
                            .unwrap_or(0)
                            + count_coerce_evidence_by(&arm.body, accepts)
                    })
                    .sum::<usize>()
        }
        yulang_core_ir::Expr::Block { stmts, tail } => {
            stmts
                .iter()
                .map(|stmt| match stmt {
                    yulang_core_ir::Stmt::Let { value, .. } | yulang_core_ir::Stmt::Expr(value) => {
                        count_coerce_evidence_by(value, accepts)
                    }
                    yulang_core_ir::Stmt::Module { body, .. } => {
                        count_coerce_evidence_by(body, accepts)
                    }
                })
                .sum::<usize>()
                + tail
                    .as_deref()
                    .map(|tail| count_coerce_evidence_by(tail, accepts))
                    .unwrap_or(0)
        }
        yulang_core_ir::Expr::Handle { body, arms, .. } => {
            count_coerce_evidence_by(body, accepts)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard
                            .as_ref()
                            .map(|guard| count_coerce_evidence_by(guard, accepts))
                            .unwrap_or(0)
                            + count_coerce_evidence_by(&arm.body, accepts)
                    })
                    .sum::<usize>()
        }
        yulang_core_ir::Expr::Var(_)
        | yulang_core_ir::Expr::PrimitiveOp(_)
        | yulang_core_ir::Expr::Lit(_) => 0,
    }
}

fn coerce_evidence_is_concrete(evidence: &yulang_core_ir::CoerceEvidence) -> bool {
    concrete_type_bounds(&evidence.actual) && concrete_type_bounds(&evidence.expected)
}

fn concrete_type_bounds(bounds: &yulang_core_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds.lower.as_deref().is_none_or(concrete_type)
        && bounds.upper.as_deref().is_none_or(concrete_type)
}

fn concrete_type(ty: &yulang_core_ir::Type) -> bool {
    match ty {
        yulang_core_ir::Type::Never | yulang_core_ir::Type::Any => true,
        yulang_core_ir::Type::Var(_) => false,
        yulang_core_ir::Type::Named { args, .. } => args.iter().all(concrete_type_arg),
        yulang_core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            concrete_type(param)
                && concrete_type(param_effect)
                && concrete_type(ret_effect)
                && concrete_type(ret)
        }
        yulang_core_ir::Type::Tuple(items)
        | yulang_core_ir::Type::Union(items)
        | yulang_core_ir::Type::Inter(items) => items.iter().all(concrete_type),
        yulang_core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .all(|field| concrete_type(&field.value))
                && record.spread.as_ref().is_none_or(concrete_record_spread)
        }
        yulang_core_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .all(|case| case.payloads.iter().all(concrete_type))
                && variant.tail.as_deref().is_none_or(concrete_type)
        }
        yulang_core_ir::Type::Row { items, tail } => {
            items.iter().all(concrete_type) && concrete_type(tail)
        }
        yulang_core_ir::Type::Recursive { body, .. } => concrete_type(body),
    }
}

fn concrete_record_spread(spread: &yulang_core_ir::RecordSpread) -> bool {
    match spread {
        yulang_core_ir::RecordSpread::Head(ty) | yulang_core_ir::RecordSpread::Tail(ty) => {
            concrete_type(ty)
        }
    }
}

fn concrete_type_arg(arg: &yulang_core_ir::TypeArg) -> bool {
    match arg {
        yulang_core_ir::TypeArg::Type(ty) => concrete_type(ty),
        yulang_core_ir::TypeArg::Bounds(bounds) => concrete_type_bounds(bounds),
    }
}

#[test]
fn tuple_binding_can_widen_to_float_annotation() {
    let mut state = parse_and_lower("my t: (float, float) = (1, 2)");
    state.finalize_compact_results();
    let exported = export_principal_bindings(&mut state);
    let binding = exported
        .iter()
        .find(|binding| binding.name.segments.last().map(|n| n.0.as_str()) == Some("t"))
        .expect("t binding");
    assert_eq!(
        binding.scheme.body,
        yulang_core_ir::Type::Tuple(vec![
            yulang_core_ir::Type::Named {
                path: yulang_core_ir::Path::from_name(yulang_core_ir::Name("float".to_string(),)),
                args: vec![],
            },
            yulang_core_ir::Type::Named {
                path: yulang_core_ir::Path::from_name(yulang_core_ir::Name("float".to_string(),)),
                args: vec![],
            },
        ]),
    );
}

#[test]
fn record_binding_can_widen_to_float_annotation() {
    let mut state = parse_and_lower("my r: {x: float, y: float} = {x: 1, y: 2}");
    state.finalize_compact_results();
    let exported = export_principal_bindings(&mut state);
    let binding = exported
        .iter()
        .find(|binding| binding.name.segments.last().map(|n| n.0.as_str()) == Some("r"))
        .expect("r binding");
    assert_eq!(
        binding.scheme.body,
        yulang_core_ir::Type::Record(yulang_core_ir::RecordType {
            fields: vec![
                yulang_core_ir::RecordField {
                    name: yulang_core_ir::Name("x".to_string()),
                    value: yulang_core_ir::Type::Named {
                        path: yulang_core_ir::Path::from_name(yulang_core_ir::Name(
                            "float".to_string(),
                        )),
                        args: vec![],
                    },
                    optional: false,
                },
                yulang_core_ir::RecordField {
                    name: yulang_core_ir::Name("y".to_string()),
                    value: yulang_core_ir::Type::Named {
                        path: yulang_core_ir::Path::from_name(yulang_core_ir::Name(
                            "float".to_string(),
                        )),
                        args: vec![],
                    },
                    optional: false,
                },
            ],
            spread: None,
        }),
    );
}

#[test]
fn concrete_role_constraint_without_impl_surfaces_missing_impl() {
    let mut state =
        parse_and_lower("role Display 'a:\n  our a.display: string\n\nmy shown = 1.display\n");
    state.finalize_compact_results();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::MissingImpl { role, args }
                if role == "Display" && args == &vec!["int".to_string()]
        )),
        "expected missing impl error, got {errors:?}",
    );
}

#[test]
fn concrete_role_method_call_without_impl_surfaces_missing_impl_during_selection() {
    let mut state =
        parse_and_lower("role Display 'a:\n  our a.display: string\n\nmy shown = 1.display\n");
    state.refresh_selection_environment();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::MissingImpl { role, args }
                if role == "Display" && args == &vec!["int".to_string()]
        )),
        "expected missing impl error from role method selection, got {errors:?}",
    );
}

#[test]
fn duplicate_impls_surface_ambiguous_impl_error() {
    let mut state = parse_and_lower(
        "role Display 'a:\n  our a.display: string\n\n\
             impl Display int;\n\
             impl Display int;\n\
             my shown = 1.display\n",
    );
    state.finalize_compact_results();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::AmbiguousImpl {
                role,
                args,
                candidates,
                ..
            } if role == "Display" && args == &vec!["int".to_string()] && *candidates == 2
        )),
        "expected ambiguous impl error, got {errors:?}",
    );
}

#[test]
fn duplicate_role_method_impls_surface_ambiguous_impl_during_selection() {
    let mut state = parse_and_lower(
        "role Display 'a:\n  our a.display: string\n\n\
             impl Display int:\n  our x.display = \"a\"\n\
             impl Display int:\n  our x.display = \"b\"\n\
             my shown = 1.display\n",
    );
    state.refresh_selection_environment();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::AmbiguousImpl {
                role,
                args,
                candidates,
                ..
            } if role == "Display" && args == &vec!["int".to_string()] && *candidates == 2
        )),
        "expected ambiguous impl error from role method selection, got {errors:?}",
    );
}

#[test]
fn concrete_multi_arg_role_constraint_without_impl_surfaces_missing_impl() {
    let mut state = parse_and_lower(
        "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             my shown: string = 1.index true\n",
    );
    state.finalize_compact_results();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::MissingImpl { role, args }
                if role == "Index"
                    && args == &vec![
                        "int".to_string(),
                        "bool".to_string(),
                        "value = std::str::str".to_string(),
                    ]
        )),
        "expected missing multi-arg impl error, got {errors:?}",
    );
}

#[test]
fn duplicate_multi_arg_impls_surface_ambiguous_impl_error() {
    let mut state = parse_and_lower(
        "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index int bool:\n  type value = string\n\
             impl Index int bool:\n  type value = string\n\
             my shown: string = 1.index true\n",
    );
    state.finalize_compact_results();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::AmbiguousImpl {
                role,
                args,
                candidates,
                ..
            } if role == "Index"
                && args == &vec![
                    "int".to_string(),
                    "bool".to_string(),
                    "value = std::str::str".to_string(),
                ]
                && *candidates == 2
        )),
        "expected ambiguous multi-arg impl error, got {errors:?}",
    );
}

#[test]
fn where_clause_in_binding_body_adds_role_constraint_from_header_type_scope() {
    let state = parse_and_lower(
        "role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             my twice(x: 'a) =\n  where 'a: Add\n  x.add x\n",
    );
    let twice_def = state
        .ctx
        .resolve_value(&symbols::Name("twice".to_string()))
        .unwrap();
    let constraints = state.infer.role_constraints_of(twice_def);
    assert!(
        constraints.iter().any(|constraint| {
            constraint.role
                == symbols::Path {
                    segments: vec![symbols::Name("Add".to_string())],
                }
                && constraint.args.len() == 1
        }),
        "binding-body where clause should add Add<'a> to the binding owner, got {constraints:?}",
    );
}

#[test]
fn where_clause_in_role_body_is_inherited_by_role_methods() {
    let state = parse_and_lower(
        "role Display 'a:\n  our a.display: string\n\n\
             role Show 'a:\n  where 'a: Display\n  our a.show: string\n",
    );
    let show_def = state
        .ctx
        .resolve_path_value(&symbols::Path {
            segments: vec![
                symbols::Name("Show".to_string()),
                symbols::Name("show".to_string()),
            ],
        })
        .unwrap();
    let constraints = state.infer.role_constraints_of(show_def);
    assert!(
        constraints.iter().any(|constraint| {
            constraint.role
                == symbols::Path {
                    segments: vec![symbols::Name("Display".to_string())],
                }
                && constraint.args.len() == 1
        }),
        "role-body where clause should be inherited by role methods, got {constraints:?}",
    );
    assert!(
        constraints.iter().any(|constraint| {
            constraint.role
                == symbols::Path {
                    segments: vec![symbols::Name("Show".to_string())],
                }
                && constraint.args.len() == 1
        }),
        "role method should still keep its own role constraint, got {constraints:?}",
    );
}

#[test]
fn impl_body_where_enables_candidate_when_prerequisite_impl_exists() {
    let mut state = parse_and_lower(
        "role Display 'a:\n  our a.display: string\n\n\
             role Wrap 'a:\n  our a.wrap: string\n\n\
             impl Display int;\n\
             impl Wrap 'a:\n  where 'a: Display\n\n\
             my shown = 1.wrap\n",
    );
    state.finalize_compact_results();
    let rendered = crate::display::dump::render_compact_results(&mut state);
    let shown = rendered
        .iter()
        .find(|(name, _)| name == "shown")
        .expect("shown should be rendered");
    assert_eq!(shown.1, "std::str::str");
    assert!(
        !state
            .infer
            .type_errors()
            .iter()
            .any(|error| matches!(error.kind, TypeErrorKind::MissingImpl { .. })),
        "prerequisite impl should make Wrap<int> viable, got {:?}",
        state.infer.type_errors(),
    );
}

#[test]
fn impl_body_where_filters_out_candidate_when_prerequisite_impl_is_missing() {
    let mut state = parse_and_lower(
        "role Display 'a:\n  our a.display: string\n\n\
             role Wrap 'a:\n  our a.wrap: string\n\n\
             impl Wrap 'a:\n  where 'a: Display\n\n\
             my shown = 1.wrap\n",
    );
    state.finalize_compact_results();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::MissingImplPrerequisite {
                role,
                args,
                prerequisite_role,
                prerequisite_args,
            }
                if role == "Wrap"
                    && args == &vec!["int".to_string()]
                    && prerequisite_role == "Display"
                    && prerequisite_args == &vec!["int".to_string()]
        )),
        "candidate with unsatisfied prerequisite should be filtered out, got {errors:?}",
    );
}

#[test]
fn impl_body_reports_missing_required_member() {
    let mut state = parse_and_lower(
        "role Pair 'a:\n  our a.first: int\n  our a.second: int\n\n\
             impl Pair int:\n  our x.first = 1\n",
    );
    state.finalize_compact_results();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::MissingImplMember { role, member }
                if role == "Pair" && member == "second"
        )),
        "missing impl member should surface, got {errors:?}",
    );
}

#[test]
fn impl_body_reports_unknown_member() {
    let mut state = parse_and_lower(
        "role Score 'a:\n  our a.score: int\n\n\
             impl Score int:\n  our x.other = 1\n",
    );
    state.finalize_compact_results();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::UnknownImplMember { role, member }
                if role == "Score" && member == "other"
        )),
        "unknown impl member should surface, got {errors:?}",
    );
}

#[test]
fn impl_body_checks_member_body_against_role_signature() {
    let mut state = parse_and_lower(
        "role Show 'a:\n  our a.show: string\n\n\
             impl Show int:\n  our x.show = 1\n",
    );
    state.finalize_compact_results();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| {
            error.cause.reason == ConstraintReason::ImplMember
                && error.kind == TypeErrorKind::ConstructorMismatch
        }),
        "impl member body should be checked against role signature, got {errors:?}",
    );
}

#[test]
fn impl_body_allows_my_helpers_used_by_our_members() {
    let mut state = parse_and_lower(
        "role Score 'a:\n  our a.score: int\n\n\
             impl Score int:\n  my helper = 1\n  our x.score = helper\n\n\
             my shown = 1.score\n",
    );
    state.finalize_compact_results();
    let rendered = crate::display::dump::render_compact_results(&mut state);
    let shown = rendered
        .iter()
        .find(|(name, _)| name == "shown")
        .expect("shown should be rendered");
    assert_eq!(shown.1, "int");
    assert!(
        !state.infer.type_errors().iter().any(|error| {
            matches!(
                error.kind,
                TypeErrorKind::MissingImplMember { .. }
                    | TypeErrorKind::UnknownImplMember { .. }
                    | TypeErrorKind::MissingImpl { .. }
            )
        }),
        "my helper should be usable inside our impl member, got {:?}",
        state.infer.type_errors(),
    );
}

#[test]
fn generic_impl_resolves_associated_output_from_input_substitution() {
    let mut state = parse_and_lower(
        "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index (list 'a) int:\n  type value = 'a\n\
             my get(xs: list bool) = xs.index 0\n",
    );
    state.finalize_compact_results();
    let rendered = crate::display::dump::render_compact_results(&mut state);
    let get = rendered
        .iter()
        .find(|(name, _)| name == "get")
        .expect("get should be rendered");
    assert!(
        get.1.contains("bool") && !get.1.contains("Index"),
        "associated output should resolve through generic impl, got {}",
        get.1,
    );
}

#[test]
fn impl_body_check_resolves_associated_output_in_expected_signature() {
    let mut state = parse_and_lower(
        "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index int bool:\n  type value = str\n  our x.index y = \"ok\"\n\n\
             my shown = 1.index true\n",
    );
    state.finalize_compact_results();
    let rendered = crate::display::dump::render_compact_results(&mut state);
    let shown = rendered
        .iter()
        .find(|(name, _)| name == "shown")
        .expect("shown should be rendered");
    assert_eq!(shown.1, "std::str::str");
    assert!(
        !state
            .infer
            .type_errors()
            .iter()
            .any(|error| error.cause.reason == ConstraintReason::ImplMember),
        "associated output should be substituted before impl member checking, got {:?}",
        state.infer.type_errors(),
    );
}

#[test]
fn concrete_impl_beats_generic_impl_overlap() {
    let mut state = parse_and_lower(
        "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index 'a bool:\n  type value = int\n\
             impl Index int bool:\n  type value = string\n\
             my shown = 1.index true\n",
    );
    state.finalize_compact_results();
    let rendered = crate::display::dump::render_compact_results(&mut state);
    let shown = rendered
        .iter()
        .find(|(name, _)| name == "shown")
        .expect("shown should be rendered");
    assert_eq!(shown.1, "std::str::str");
    assert!(
        !state
            .infer
            .type_errors()
            .iter()
            .any(|error| matches!(error.kind, TypeErrorKind::AmbiguousImpl { .. })),
        "more specific concrete impl should win, got {:?}",
        state.infer.type_errors(),
    );
}

#[test]
fn more_specific_generic_impl_beats_broader_generic_impl() {
    let mut state = parse_and_lower(
        "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index 'a int:\n  type value = bool\n\
             impl Index (list 'a) int:\n  type value = 'a\n\
             my get(xs: list string) = xs.index 0\n",
    );
    state.finalize_compact_results();
    let rendered = crate::display::dump::render_compact_results(&mut state);
    let get = rendered
        .iter()
        .find(|(name, _)| name == "get")
        .expect("get should be rendered");
    assert!(
        get.1.contains("std::str::str") && !get.1.contains("bool"),
        "more specific generic impl should win, got {}",
        get.1,
    );
}

#[test]
fn incomparable_overlapping_impls_stay_ambiguous() {
    let mut state = parse_and_lower(
        "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index int 'a:\n  type value = string\n\
             impl Index 'a bool:\n  type value = int\n\
             my shown = 1.index true\n",
    );
    state.finalize_compact_results();
    let errors = state.infer.type_errors();
    assert!(
        errors.iter().any(|error| matches!(
            &error.kind,
            TypeErrorKind::AmbiguousImpl {
                role,
                candidates,
                ..
            } if role == "Index"
                && *candidates == 2
        )),
        "incomparable overlaps should stay ambiguous, got {errors:?}",
    );
}

#[test]
fn debug_effectful_value_binding_compact_scheme() {
    let mut state = parse_and_lower("act undet:\n  our bool: () -> bool\n\nmy y = undet::bool()");
    let y_def = state
        .ctx
        .resolve_value(&symbols::Name("y".to_string()))
        .unwrap();
    state.finalize_compact_results();
    assert!(
        state.compact_scheme_of(y_def).is_some(),
        "effectful binding should compact"
    );
}

#[test]
fn top_level_bindings_do_not_compact_during_lowering() {
    let state = parse_and_lower("my x = 42\nmy y = x");
    let x_def = state
        .ctx
        .resolve_value(&symbols::Name("x".to_string()))
        .unwrap();
    let y_def = state
        .ctx
        .resolve_value(&symbols::Name("y".to_string()))
        .unwrap();

    assert!(
        state.infer.compact_schemes.borrow().get(&x_def).is_none(),
        "top-level x should stay un-compacted until finalize"
    );
    assert!(
        state.infer.compact_schemes.borrow().get(&y_def).is_none(),
        "top-level y should stay un-compacted until finalize"
    );
}

#[test]
fn act_operation_signature_creates_fun_lower_bound() {
    let state = parse_and_lower("act undet:\n  our bool: () -> bool");
    let op_def = state
        .ctx
        .resolve_path_value(&symbols::Path {
            segments: vec![
                symbols::Name("undet".to_string()),
                symbols::Name("bool".to_string()),
            ],
        })
        .unwrap();
    let op_tv = state.def_tvs[&op_def];
    let lowers = state.infer.lowers_of(op_tv);
    assert!(
        lowers.iter().any(|p| matches!(p, Pos::Fun { .. })),
        "operation should have Fun lower bound, got {:?}",
        lowers,
    );
}

#[test]
fn lambda_creates_fun_constraint() {
    // `my f x = x` で f の def_tv に Fun 型の lower bound が入るはず
    let state = parse_and_lower("my f x = x");
    let f_def = state
        .ctx
        .resolve_value(&symbols::Name("f".to_string()))
        .unwrap();
    let f_tv = state.def_tvs[&f_def];
    let lowers = state.infer.lowers_of(f_tv);
    let has_fun = lowers.iter().any(|p| matches!(p, Pos::Fun { .. }));
    assert!(has_fun, "f's def_tv should have a Fun lower bound");
}

// ── 「まだ SCC 辺がない」テスト ───────────────────────────────────────────

#[test]
fn frozen_references_record_dependency_edges() {
    // provisional frozen scheme を参照した binding は finalize 順を守るため
    // lowering 時点で component edge を持つ。
    let state = parse_and_lower("my x = 1\nmy y = x");
    let x_def = state
        .ctx
        .resolve_value(&symbols::Name("x".to_string()))
        .unwrap();
    let y_def = state
        .ctx
        .resolve_value(&symbols::Name("y".to_string()))
        .unwrap();
    let x_component = state.infer.def_to_component[&x_def];
    let y_component = state.infer.def_to_component[&y_def];

    assert!(
        state.infer.component_edges[y_component]
            .borrow()
            .contains(&x_component),
        "y should depend on x via component edge",
    );
}

#[test]
fn same_owner_param_refs_do_not_enter_ref_table() {
    let state = parse_and_lower("my id x = x");
    assert!(
        state.ctx.refs.resolved().is_empty(),
        "same-owner param refs should alias directly without resolved ref tracking",
    );
}

// ── ブロックエフェクト伝播テスト ──────────────────────────────────────────

#[test]
fn block_eff_collects_stmt_effs() {
    // `our foo =\n  my x = 1\n  x`
    // → block の eff に `my x = 1` の eff と tail `x` の eff が合流するはず
    let src = "our foo =\n  my x = 1\n  x";
    let state = parse_and_lower(src);

    // foo の body は IndentBlock として lower される
    let foo_def = state
        .ctx
        .resolve_value(&symbols::Name("foo".to_string()))
        .unwrap();
    let foo_tv = state.def_tvs[&foo_def];

    // foo_tv に lower bound が入っている（body.tv <: foo_tv）
    let lowers = state.infer.lowers_of(foo_tv);
    assert!(
        !lowers.is_empty(),
        "foo should have lower bounds from its body"
    );
}

// ── Lambda がエフェクトを封じるテスト ────────────────────────────────────

#[test]
fn lambda_seals_effects() {
    // `my f x = x` を lower する。
    // f の Lam 式自体の eff には `[] <: eff_lam` が入るはず（生成は純粋）。
    // 一方で f の def_tv の Fun lower bound の ret_eff は body.eff を指す Var。
    let state = parse_and_lower("my f x = x");
    let f_def = state
        .ctx
        .resolve_value(&symbols::Name("f".to_string()))
        .unwrap();
    let f_tv = state.def_tvs[&f_def];

    // Fun lower bound を探す
    let lowers = state.infer.lowers_of(f_tv);
    let fun = lowers
        .iter()
        .find(|p| matches!(p, Pos::Fun { .. }))
        .expect("f should have Fun lower bound");

    // Fun の ret_eff は Var（body.eff を指す）であり、Atom 等の具体的エフェクトではない
    if let Pos::Fun { ret_eff, .. } = fun {
        assert!(
            matches!(state.infer.arena.get_pos(*ret_eff), Pos::Var(_)),
            "ret_eff should be a TypeVar (effect of body), not a concrete effect: {:?}",
            ret_eff
        );
    }

    // f の def_tv 自体は body_expr.tv を経由して保持するので、Var lower が混ざってよい。
    // 少なくとも raw effect row を直接持たないことだけを確認する。
    let has_raw_row = lowers.iter().any(|p| matches!(p, Pos::Row(..)));
    assert!(
        !has_raw_row,
        "f's def_tv should not have raw effect-row lower bounds"
    );
}

#[test]
fn wildcard_effect_annotation_does_not_mark_arg_effect_through() {
    let state = parse_and_lower("my f(x: [_] _) = x");
    let f_def = state
        .ctx
        .resolve_value(&symbols::Name("f".to_string()))
        .unwrap();
    let f_tv = state.def_tvs[&f_def];
    let lowers = state.infer.lowers_of(f_tv);
    let fun = lowers
        .iter()
        .find(|p| matches!(p, Pos::Fun { .. }))
        .expect("f should have Fun lower bound");

    let arg_eff_tv = match fun {
        Pos::Fun { arg_eff, .. } => match state.infer.arena.get_neg(*arg_eff) {
            Neg::Var(tv) => tv,
            other => panic!("expected arg_eff var, got {:?}", other),
        },
        _ => unreachable!(),
    };

    assert!(
        !state.infer.is_through(arg_eff_tv),
        "[_] should not mark the function argument effect slot as through",
    );
}

#[test]
fn row_effect_annotation_marks_only_tail_var_through() {
    let state = parse_and_lower("my g(x: [io; e] _) = x");
    let g_def = state
        .ctx
        .resolve_value(&symbols::Name("g".to_string()))
        .unwrap();
    let g_tv = state.def_tvs[&g_def];
    let lowers = state.infer.lowers_of(g_tv);
    let fun = lowers
        .iter()
        .find(|p| matches!(p, Pos::Fun { .. }))
        .expect("g should have Fun lower bound");

    let arg_eff_tv = match fun {
        Pos::Fun { arg_eff, .. } => match state.infer.arena.get_neg(*arg_eff) {
            Neg::Var(tv) => tv,
            other => panic!("expected arg_eff var, got {:?}", other),
        },
        _ => unreachable!(),
    };

    assert!(
        !state.infer.is_through(arg_eff_tv),
        "[io; e] should constrain the argument effect slot rather than mark it through",
    );

    let has_tail_var = state
        .infer
        .lowers_of(arg_eff_tv)
        .into_iter()
        .find_map(|bound| match bound {
            Pos::Row(_, tail) => match state.infer.arena.get_pos(tail) {
                Pos::Var(_) => Some(()),
                _ => None,
            },
            _ => None,
        })
        .is_some();

    assert!(
        has_tail_var,
        "row annotation should contribute a row lower bound with a tail var",
    );
}

#[test]
fn non_through_lower_clears_through_on_var_propagation() {
    let infer = solve::Infer::new();
    let a = fresh_type_var();
    let b = fresh_type_var();

    infer.register_level(a, 0);
    infer.register_level(b, 0);
    infer.mark_through(b);

    infer.constrain(Pos::Var(a), Neg::Var(b));

    assert!(
        !infer.is_through(b),
        "through should be cleared by a non-through lower bound"
    );
}

#[test]
fn pure_function_passes_argument_effect_to_return_effect() {
    let infer = solve::Infer::new();
    let arg_l = fresh_type_var();
    let arg_r = fresh_type_var();
    let ret_l = fresh_type_var();
    let ret_r = fresh_type_var();
    let body_eff = fresh_type_var();
    let arg_eff = fresh_type_var();
    let ret_eff = fresh_type_var();

    for tv in [arg_l, arg_r, ret_l, ret_r, body_eff, arg_eff, ret_eff] {
        infer.register_level(tv, 0);
    }

    infer.constrain(
        Pos::Fun {
            arg: infer.alloc_neg(Neg::Var(arg_l)),
            arg_eff: infer.alloc_neg(Neg::Row(vec![], infer.arena.top)),
            ret_eff: infer.alloc_pos(Pos::Var(body_eff)),
            ret: infer.alloc_pos(Pos::Var(ret_l)),
        },
        Neg::Fun {
            arg: infer.alloc_pos(Pos::Var(arg_r)),
            arg_eff: infer.alloc_pos(Pos::Var(arg_eff)),
            ret_eff: infer.alloc_neg(Neg::Var(ret_eff)),
            ret: infer.alloc_neg(Neg::Var(ret_r)),
        },
    );

    let ret_eff_lowers = infer.lowers_of(ret_eff);
    assert!(
        ret_eff_lowers.contains(&Pos::Var(body_eff)),
        "body effect should flow into return effect"
    );
    assert!(
        ret_eff_lowers.contains(&Pos::Var(arg_eff)),
        "argument effect should also flow into return effect for pure functions"
    );
}

#[test]
fn resolve_pending_refs_builds_refid_to_defid_map() {
    let mut ctx = lower::ctx::LowerCtx::new();
    let module = ctx.enter_module(symbols::Name("foo".to_string()));
    let def = fresh_def_id();
    ctx.modules
        .insert_value(ctx.current_module, symbols::Name("bar".to_string()), def);
    ctx.leave_module(module);

    let ref_id = fresh_ref_id();
    ctx.refs.push_unresolved(
        ref_id,
        ref_table::UnresolvedRef {
            path: symbols::Path {
                segments: vec![
                    symbols::Name("foo".to_string()),
                    symbols::Name("bar".to_string()),
                ],
            },
            module: ctx.current_module,
            use_paths: ctx.current_use_paths(),
            ref_tv: fresh_type_var(),
            owner: None,
        },
    );

    ctx.resolve_pending_refs();

    assert_eq!(ctx.refs.get(ref_id), Some(def));
    assert!(
        ctx.refs.unresolved().is_empty(),
        "resolved refs should be removed from unresolved"
    );
}

#[test]
fn resolve_value_candidates_keep_shadowing_order() {
    let mut ctx = lower::ctx::LowerCtx::new();
    let root_def = fresh_def_id();
    let local_def = fresh_def_id();
    let name = symbols::Name("x".to_string());
    ctx.modules
        .insert_value(ctx.current_module, name.clone(), root_def);
    ctx.push_local();
    ctx.bind_local(name.clone(), local_def);

    assert_eq!(
        ctx.resolve_value_candidates(&name),
        vec![local_def, root_def],
        "candidate resolver should keep local before module binding",
    );
    assert_eq!(ctx.resolve_value(&name), Some(local_def));
}

#[test]
fn resolve_path_value_candidates_keep_use_order() {
    let mut ctx = lower::ctx::LowerCtx::new();
    let left_parent = ctx.enter_module(symbols::Name("left".to_string()));
    let left_mod = ctx.current_module;
    ctx.enter_module(symbols::Name("ops".to_string()));
    let left_ops = ctx.current_module;
    let left_def = fresh_def_id();
    ctx.modules
        .insert_value(left_ops, symbols::Name("target".to_string()), left_def);
    ctx.leave_module(left_mod);
    ctx.leave_module(left_parent);

    let right_parent = ctx.enter_module(symbols::Name("right".to_string()));
    let right_mod = ctx.current_module;
    ctx.enter_module(symbols::Name("ops".to_string()));
    let right_ops = ctx.current_module;
    let right_def = fresh_def_id();
    ctx.modules
        .insert_value(right_ops, symbols::Name("target".to_string()), right_def);
    ctx.leave_module(right_mod);
    ctx.leave_module(right_parent);

    ctx.add_use(&symbols::Path {
        segments: vec![symbols::Name("left".to_string())],
    })
    .unwrap();
    ctx.add_use(&symbols::Path {
        segments: vec![symbols::Name("right".to_string())],
    })
    .unwrap();

    let candidates = ctx.resolve_path_value_candidates(&symbols::Path {
        segments: vec![
            symbols::Name("ops".to_string()),
            symbols::Name("target".to_string()),
        ],
    });
    assert_eq!(candidates, vec![left_def, right_def]);
    assert_eq!(
        ctx.resolve_path_value(&symbols::Path {
            segments: vec![
                symbols::Name("ops".to_string()),
                symbols::Name("target".to_string()),
            ],
        }),
        Some(left_def)
    );
}

#[test]
fn resolve_value_candidates_skip_inaccessible_private_parent_binding() {
    let mut ctx = lower::ctx::LowerCtx::new();
    let private_def = fresh_def_id();
    let public_def = fresh_def_id();
    let name = symbols::Name("x".to_string());
    ctx.modules.insert_value_with_visibility(
        ctx.current_module,
        name.clone(),
        private_def,
        symbols::Visibility::My,
    );
    ctx.modules.insert_value(
        ctx.current_module,
        symbols::Name("y".to_string()),
        public_def,
    );

    let root = ctx.current_module;
    ctx.enter_module(symbols::Name("child".to_string()));
    assert_eq!(
        ctx.resolve_value_candidates(&name),
        Vec::<DefId>::new(),
        "child module should not see parent's private binding",
    );
    assert_eq!(ctx.resolve_value(&name), None);
    ctx.leave_module(root);
}

#[test]
fn resolve_value_candidates_keep_accessible_our_parent_binding() {
    let mut ctx = lower::ctx::LowerCtx::new();
    let shared_def = fresh_def_id();
    let name = symbols::Name("x".to_string());
    ctx.modules.insert_value_with_visibility(
        ctx.current_module,
        name.clone(),
        shared_def,
        symbols::Visibility::Our,
    );

    let root = ctx.current_module;
    ctx.enter_module(symbols::Name("child".to_string()));
    assert_eq!(ctx.resolve_value_candidates(&name), vec![shared_def]);
    assert_eq!(ctx.resolve_value(&name), Some(shared_def));
    ctx.leave_module(root);
}

#[test]
fn deferred_selection_resolves_from_type_lower_bound() {
    let mut infer = solve::Infer::new();
    let mut modules = symbols::ModuleTable::default();
    let root = modules.new_module();
    let owner_def = fresh_def_id();
    let point_type = fresh_def_id();
    let x_method = fresh_def_id();
    let recv_tv = fresh_type_var();
    let recv_eff = fresh_type_var();
    let result_tv = fresh_type_var();
    let result_eff = fresh_type_var();
    let method_tv = fresh_type_var();

    infer.register_def(owner_def);
    infer.register_def(x_method);
    infer.register_level(recv_tv, 0);
    infer.register_level(recv_eff, 0);
    infer.register_level(result_tv, 0);
    infer.register_level(result_eff, 0);
    infer.register_level(method_tv, 0);

    modules.insert_type(root, symbols::Name("point".to_string()), point_type);
    let point_companion = modules.new_module();
    modules.insert_module(root, symbols::Name("point".to_string()), point_companion);
    modules.insert_value(point_companion, symbols::Name("x".to_string()), x_method);

    infer.register_def_tv(x_method, method_tv);

    infer.add_lower(
        recv_tv,
        Pos::Con(
            symbols::Path {
                segments: vec![symbols::Name("point".to_string())],
            },
            vec![],
        ),
    );
    infer
        .deferred_selections
        .borrow_mut()
        .entry(recv_tv)
        .or_default()
        .push(solve::DeferredSelection {
            name: symbols::Name("x".to_string()),
            module: root,
            recv_eff,
            result_tv,
            result_eff,
            owner: Some(owner_def),
            cause: ConstraintCause::unknown(),
        });
    infer.increment_pending_selection(owner_def);

    infer.rebuild_type_methods(&modules);
    infer.resolve_deferred_selections();

    assert!(
        infer
            .uppers_of(method_tv)
            .iter()
            .any(|upper| matches!(upper, Neg::Fun { .. })),
        "resolved method def should be applied to receiver and selection result",
    );
    assert!(
        infer.deferred_selections.borrow().get(&recv_tv).is_none(),
        "resolved selection should be removed from deferred queue",
    );
    assert_eq!(
        *infer.component_pending_selections[infer.def_to_component[&owner_def]].borrow(),
        0,
        "resolved selection should decrement pending count",
    );
    assert!(
        infer.component_edges[infer.def_to_component[&owner_def]]
            .borrow()
            .contains(&infer.def_to_component[&x_method]),
        "resolved selection should add an SCC edge to the selected method",
    );
}

#[test]
fn constrain_immediately_resolves_deferred_selection_when_type_is_known() {
    let mut infer = solve::Infer::new();
    let mut modules = symbols::ModuleTable::default();
    let root = modules.new_module();
    let owner_def = fresh_def_id();
    let point_type = fresh_def_id();
    let x_method = fresh_def_id();
    let recv_tv = fresh_type_var();
    let recv_eff = fresh_type_var();
    let result_tv = fresh_type_var();
    let result_eff = fresh_type_var();
    let method_tv = fresh_type_var();

    infer.register_def(owner_def);
    infer.register_def(x_method);
    infer.register_level(recv_tv, 0);
    infer.register_level(recv_eff, 0);
    infer.register_level(result_tv, 0);
    infer.register_level(result_eff, 0);
    infer.register_level(method_tv, 0);
    infer.register_def_tv(x_method, method_tv);

    modules.insert_type(root, symbols::Name("point".to_string()), point_type);
    let point_companion = modules.new_module();
    modules.insert_module(root, symbols::Name("point".to_string()), point_companion);
    modules.insert_value(point_companion, symbols::Name("x".to_string()), x_method);

    infer.rebuild_type_methods(&modules);
    infer
        .deferred_selections
        .borrow_mut()
        .entry(recv_tv)
        .or_default()
        .push(solve::DeferredSelection {
            name: symbols::Name("x".to_string()),
            module: root,
            recv_eff,
            result_tv,
            result_eff,
            owner: Some(owner_def),
            cause: ConstraintCause::unknown(),
        });
    infer.increment_pending_selection(owner_def);

    infer.constrain(
        Pos::Con(
            symbols::Path {
                segments: vec![symbols::Name("point".to_string())],
            },
            vec![],
        ),
        Neg::Var(recv_tv),
    );

    assert!(
        infer
            .uppers_of(method_tv)
            .iter()
            .any(|upper| matches!(upper, Neg::Fun { .. })),
        "selection should apply method when constrain adds a concrete receiver lower bound",
    );
    assert!(infer.deferred_selections.borrow().get(&recv_tv).is_none());
    assert_eq!(
        *infer.component_pending_selections[infer.def_to_component[&owner_def]].borrow(),
        0,
    );
    assert!(
        infer.component_edges[infer.def_to_component[&owner_def]]
            .borrow()
            .contains(&infer.def_to_component[&x_method]),
    );
}

#[test]
fn deferred_selection_resolves_from_global_extension_method_fallback() {
    let mut infer = solve::Infer::new();
    let root = symbols::ModuleId(0);
    let owner_def = fresh_def_id();
    let list_method = fresh_def_id();
    let recv_tv = fresh_type_var();
    let recv_eff = fresh_type_var();
    let result_tv = fresh_type_var();
    let result_eff = fresh_type_var();
    let method_tv = fresh_type_var();

    infer.register_def(owner_def);
    infer.register_def(list_method);
    infer.register_level(recv_tv, 0);
    infer.register_level(recv_eff, 0);
    infer.register_level(result_tv, 0);
    infer.register_level(result_eff, 0);
    infer.register_level(method_tv, 0);
    infer.register_def_tv(list_method, method_tv);
    infer.register_extension_method(ExtensionMethodInfo {
        name: symbols::Name("list".to_string()),
        def: list_method,
        module: root,
        visibility: symbols::Visibility::Pub,
        receiver_expects_computation: false,
    });

    infer
        .deferred_selections
        .borrow_mut()
        .entry(recv_tv)
        .or_default()
        .push(solve::DeferredSelection {
            name: symbols::Name("list".to_string()),
            module: root,
            recv_eff,
            result_tv,
            result_eff,
            owner: Some(owner_def),
            cause: ConstraintCause::unknown(),
        });
    infer.increment_pending_selection(owner_def);
    infer.resolve_deferred_selections();

    assert!(
        infer
            .uppers_of(method_tv)
            .iter()
            .any(|upper| matches!(upper, Neg::Fun { .. })),
        "global extension method should be applied to receiver and selection result",
    );
    assert!(infer.deferred_selections.borrow().get(&recv_tv).is_none());
}

#[test]
fn finalize_compact_results_stores_observable_scheme() {
    let mut state = parse_and_lower("my x = 42");
    let x_def = state
        .ctx
        .resolve_value(&symbols::Name("x".to_string()))
        .unwrap();

    let finalized = state.finalize_compact_results();
    let scheme = state.compact_scheme_of(x_def);

    assert!(finalized.contains(&x_def));
    assert!(
        scheme.is_some(),
        "finalize should store a compact scheme for ready defs"
    );
}

#[test]
fn constrained_function_reference_keeps_owner_role_constraint() {
    run_with_large_stack(|| {
        let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my pick xs = xs.fold 0 (\\_ x -> x)\n\
                 my a = pick\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .expect("source should lower");
        let state = &mut lowered.state;
        let pick_def = state
            .ctx
            .resolve_value(&symbols::Name("pick".to_string()))
            .expect("pick should resolve");
        let a_def = state
            .ctx
            .resolve_value(&symbols::Name("a".to_string()))
            .expect("a should resolve");

        let pick_constraints = state.infer.role_constraints_of(pick_def);
        let a_constraints = state.infer.role_constraints_of(a_def);
        assert!(
            !pick_constraints.is_empty(),
            "pick should carry Fold constraint, got {pick_constraints:?}",
        );
        assert!(
            !a_constraints.is_empty(),
            "a should inherit role constraint from pick ref, got {a_constraints:?}",
        );

        state.finalize_compact_results();
        assert!(
            state.compact_scheme_of(a_def).is_some(),
            "a should compact after inheriting pick constraint",
        );
    });
}

#[test]
fn global_extension_method_hidden_def_keeps_opaque_receiver_effect() {
    run_with_large_stack(|| {
        let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "use std::undet::*\n\
                 pub (x: [_] _).collect_list = undet::list x\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .expect("source should lower");
        let state = &mut lowered.state;
        state.finalize_compact_results();
        let ext_def = state
            .infer
            .resolve_extension_method_def(&symbols::Name("collect_list".to_string()))
            .expect("collect_list extension method should resolve");
        let scheme = state.compact_scheme_of(ext_def).unwrap_or_else(|| {
            crate::scheme::freeze_type_var_with_non_generic(
                &state.infer,
                state.def_tvs[&ext_def],
                &state.infer.non_generic_vars_of(ext_def),
            )
            .compact
            .clone()
        });
        assert_eq!(
            crate::display::format::format_coalesced_scheme(&scheme),
            "α [std::undet::undet; β] -> [β] std::list::list<α>"
        );
    });
}

#[test]
fn effect_method_selection_resolves_from_receiver_effect_in_source_lowering() {
    run_with_large_stack(|| {
        let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let lowered = lower_virtual_source_with_options(
            "use std::undet::*\n\
                 my collect(x: [undet; _] _) = x.list\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .expect("source should lower");
        assert!(
            lowered.state.infer.deferred_selections.borrow().is_empty(),
            "effect method selections should resolve during source lowering, got {:?}",
            lowered.state.infer.deferred_selections.borrow(),
        );
    });
}
