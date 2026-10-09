//! Test-only bounded characterization of existing scalar deferred-call constraints.
//!
//! Enabled as a child of the crate's test module under `shadow-f5`, these five
//! checks exercise the actual `InferenceSession` on finite fixed graphs and two
//! Name/Int/Group/Apply/Lambda HIR fixtures. The fixture walker only constructs
//! scalar ports and accumulates constraints before solver execution; it is not
//! a source-directed acceptance decider or a duplicate solver.
//!
//! Residual tokens and retained whole documentary sources are identity/pointer
//! observations, not full residual, dependent-schema, formation, or reduction
//! certificates. No production source acceptance or `SolvedModule` is asserted.
//! Effect observations cover symbolic rows and bottom propagation only, without
//! nonempty effect-label or handler-protection meaning. Extrusion characterizes
//! only current flexible-row aging. These checks assert neither complete Call
//! or Generalize implementation nor complete semantic conformance.
use super::*;

fn bridge_session() -> InferenceSession {
    let source: Arc<yu_syntax::SourceText> = Arc::from("1");
    let parsed = yu_syntax::parse_file(
        source.clone(),
        Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    );
    let hir = yu_hir::lower_module(
        yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
            "research",
            "deferred-call-bridge",
        ))),
        &parsed,
        yu_hir::SemanticImports::empty(),
    )
    .unwrap();
    InferenceSession::new(ConstraintBatch::collect(Arc::new(hir)).unwrap())
}

fn bridge_value(session: &mut InferenceSession, lower: ValueEndpointKey, upper: ValueEndpointKey) {
    let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 240);
    let cause = CauseId::for_occurrence(occurrence.clone());
    session
        .constrain_live_value(CanonicalValuePairKey { lower, upper }, &occurrence, &cause)
        .unwrap();
}

fn bridge_effect(
    session: &mut InferenceSession,
    lower: EffectEndpointKey,
    upper: EffectEndpointKey,
) {
    let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 241);
    let cause = CauseId::for_occurrence(occurrence.clone());
    session
        .constrain_live_effect(lower, upper, &occurrence, &cause)
        .unwrap();
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct BridgeCall {
    // These are research tokens, NOT semantic certificates. An opaque complete
    // predicate is represented by its external identity only in this probe.
    // The probe proves identity/port retention, not authenticity/completeness.
    residual_identity: u32,
    external_complete_contract: u32,
    formal: u32,
    argument_effect: u32,
    result_effect: u32,
    result: u32,
    demand: Term,
}

fn bridge_call(
    session: &mut InferenceSession,
    formal: u32,
    identity: u32,
    level: u32,
) -> BridgeCall {
    let argument_effect = session.fresh_effect_at_level(level).unwrap();
    let result_effect = session.fresh_effect_at_level(level).unwrap();
    let result = session.fresh_value_at_level(level).unwrap();
    let argument = session.batch.collected_leaf_term(Leaf::IntPositive);
    let ae = session
        .live_effect_term(Polarity::Positive, argument_effect)
        .unwrap();
    let re = session
        .live_effect_term(Polarity::Negative, result_effect)
        .unwrap();
    let r = session.live_value_term(Polarity::Negative, result).unwrap();
    let demand = session.negative_function_term(argument, ae, re, r).unwrap();
    BridgeCall {
        residual_identity: identity,
        external_complete_contract: 700,
        formal,
        argument_effect,
        result_effect,
        result,
        demand,
    }
}

fn bridge_install_call(session: &mut InferenceSession, call: &BridgeCall) {
    bridge_value(
        session,
        ValueEndpointKey::ValueRow(call.formal),
        ValueEndpointKey::NegativeFunction(call.demand),
    );
}

struct BridgeProvider {
    term: Term,
    argument: u32,
    argument_effect: u32,
    result_effect: u32,
    result: u32,
}

fn bridge_provider(session: &mut InferenceSession, level: u32) -> BridgeProvider {
    let argument = session.fresh_value_at_level(level).unwrap();
    let argument_effect = session.fresh_effect_at_level(level).unwrap();
    let result_effect = session.fresh_effect_at_level(level).unwrap();
    let result = session.fresh_value_at_level(level).unwrap();
    let a = session
        .live_value_term(Polarity::Negative, argument)
        .unwrap();
    let ae = session
        .live_effect_term(Polarity::Negative, argument_effect)
        .unwrap();
    let re = session
        .live_effect_term(Polarity::Positive, result_effect)
        .unwrap();
    let r = session.live_value_term(Polarity::Positive, result).unwrap();
    let term = session.positive_function_term(a, ae, re, r).unwrap();
    BridgeProvider {
        term,
        argument,
        argument_effect,
        result_effect,
        result,
    }
}

#[test]
fn deferred_call_constraints_actual_worklist_retains_symbolic_shared_constraints() {
    // Two call sites, two arrival orders; fixed graph, no source acceptance.
    for provider_first in [false, true] {
        let mut session = bridge_session();
        let formal = session.fresh_value_at_level(1).unwrap();
        let calls = [
            bridge_call(&mut session, formal, 10, 1),
            bridge_call(&mut session, formal, 11, 1),
        ];
        let frozen_residuals = calls.clone();
        let provider = bridge_provider(&mut session, 1);
        if provider_first {
            bridge_value(
                &mut session,
                ValueEndpointKey::PositiveFunction(provider.term),
                ValueEndpointKey::ValueRow(formal),
            );
        }
        for call in &calls {
            bridge_install_call(&mut session, call);
        }
        if !provider_first {
            // Formal collection has not chosen a provider or solved a result.
            assert!(
                session.bounds[formal as usize]
                    .exact_non_variable_lowers
                    .is_empty()
            );
            for call in &calls {
                assert!(
                    session.bounds[call.result as usize]
                        .exact_non_variable_lowers
                        .is_empty()
                );
                assert!(!session.effect_bounds[call.result_effect as usize].has_empty_upper);
            }
            bridge_value(
                &mut session,
                ValueEndpointKey::PositiveFunction(provider.term),
                ValueEndpointKey::ValueRow(formal),
            );
        }
        assert!(session.bounds[provider.argument as usize].has_int_positive_lower);
        for call in &calls {
            assert!(
                session.effect_bounds[call.argument_effect as usize]
                    .direct_upper_rows
                    .contains(&provider.argument_effect)
            );
            assert!(
                session.effect_bounds[provider.result_effect as usize]
                    .direct_upper_rows
                    .contains(&call.result_effect)
            );
            assert!(
                session.bounds[provider.result as usize]
                    .direct_upper_rows
                    .contains(&call.result)
            );
            assert!(!session.effect_bounds[call.result_effect as usize].has_empty_upper);
        }
        // A later lower at shared provider result reaches both site results.
        bridge_value(
            &mut session,
            ValueEndpointKey::IntPositive,
            ValueEndpointKey::ValueRow(provider.result),
        );
        bridge_effect(
            &mut session,
            EffectEndpointKey::BottomPositive,
            EffectEndpointKey::EffectRow(provider.result_effect),
        );
        for call in &calls {
            assert!(session.bounds[call.result as usize].has_int_positive_lower);
            assert!(session.effect_bounds[call.result_effect as usize].has_bottom_lower);
            assert!(!session.effect_bounds[call.result_effect as usize].has_empty_upper);
        }
        assert_eq!(calls, frozen_residuals);
        assert_ne!(calls[0].residual_identity, calls[1].residual_identity);
        assert_eq!(calls[0].formal, calls[1].formal);
        assert!(session.errors.is_empty());
        assert!(session.typed_worklist.is_empty());
        let pairs = session.typed_pairs.len();
        let value_bounds = session.bounds.clone();
        let effect_bounds = session.effect_bounds.clone();
        for call in &calls {
            bridge_install_call(&mut session, call);
        }
        assert_eq!(session.typed_pairs.len(), pairs);
        assert_eq!(session.bounds, value_bounds);
        assert_eq!(session.effect_bounds, effect_bounds);
    }
}

#[test]
fn deferred_call_constraints_generation_can_precede_late_contradiction() {
    let mut session = bridge_session();
    let formal = session.fresh_value_at_level(1).unwrap();
    let call = bridge_call(&mut session, formal, 12, 1);
    bridge_install_call(&mut session, &call);
    assert!(session.errors.is_empty());
    assert!(
        session.bounds[formal as usize]
            .exact_non_variable_lowers
            .is_empty()
    );
    bridge_value(
        &mut session,
        ValueEndpointKey::IntPositive,
        ValueEndpointKey::ValueRow(formal),
    );
    assert!(session.errors.iter().any(|error| matches!(
        error.kind(),
        SolverErrorKind::IncompatibleValue {
            lower: ValueShape::Int,
            upper: ValueShape::Function
        }
    )));
    assert_eq!(call.residual_identity, 12);
}

#[test]
fn deferred_call_constraints_sharing_propagates_a_late_result_conflict() {
    let mut session = bridge_session();
    let formal = session.fresh_value_at_level(1).unwrap();
    let first = bridge_call(&mut session, formal, 13, 1);
    let second = bridge_call(&mut session, formal, 14, 1);
    bridge_install_call(&mut session, &first);
    bridge_install_call(&mut session, &second);
    let provider = bridge_provider(&mut session, 1);
    bridge_value(
        &mut session,
        ValueEndpointKey::PositiveFunction(provider.term),
        ValueEndpointKey::ValueRow(formal),
    );
    bridge_value(
        &mut session,
        ValueEndpointKey::ValueRow(first.result),
        ValueEndpointKey::IntNegative,
    );
    bridge_value(
        &mut session,
        ValueEndpointKey::PositiveFunction(provider.term),
        ValueEndpointKey::ValueRow(provider.result),
    );
    assert!(session.errors.iter().any(|error| matches!(
        error.kind(),
        SolverErrorKind::IncompatibleValue {
            lower: ValueShape::Function,
            upper: ValueShape::Int
        }
    )));
    // The unobserved second result still sees the same provider lower.
    assert!(
        session.bounds[second.result as usize]
            .exact_non_variable_lowers
            .contains(&ValueEndpointKey::PositiveFunction(provider.term))
    );
}

#[test]
fn deferred_call_constraints_extrudes_new_children_without_resolving_effects() {
    let mut session = bridge_session();
    let formal = session.fresh_value_at_level(1).unwrap();
    let call = bridge_call(&mut session, formal, 15, 2);
    assert_eq!(session.value_levels[call.result as usize], 2);
    bridge_install_call(&mut session, &call);
    assert_eq!(session.value_levels[call.result as usize], 1);
    assert_eq!(session.effect_levels[call.argument_effect as usize], 1);
    assert_eq!(session.effect_levels[call.result_effect as usize], 1);
    assert!(!session.effect_bounds[call.result_effect as usize].has_empty_upper);
}

// Documentary dependencies are retained whole. These references are not
// executable dependent schemas, formation evidence or reduction licenses.
#[cfg(feature = "shadow-f5")]
#[derive(Clone, Debug)]
struct UnelaboratedCompleteDependency {
    contract_sources: &'static [&'static str],
    site: HirOccurrenceId,
    callee: HirOccurrenceId,
    argument: HirOccurrenceId,
    scope: Vec<HirParameterId>,
    argument_effect: u32,
    result_effect: u32,
    result: u32,
}

#[cfg(feature = "shadow-f5")]
struct SourceCallPlan {
    lower: Term,
    upper: Term,
    dependency: UnelaboratedCompleteDependency,
}

#[cfg(feature = "shadow-f5")]
fn bridge_source_hir(text: &str) -> Arc<HirModule> {
    let source: Arc<yu_syntax::SourceText> = Arc::from(text);
    let header = Arc::new(yu_syntax::scan_header(source.clone()));
    let parsed = yu_syntax::parse_file(
        source,
        header,
        Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    );
    Arc::new(
        yu_hir::shadow::lower_module_with_shadow_applications(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "research",
                "source-call-plan",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        )
        .unwrap(),
    )
}

#[cfg(feature = "shadow-f5")]
fn bridge_plan_expression(
    session: &mut InferenceSession,
    expression: &ResolvedExpr,
    scope: &mut Vec<HirParameterId>,
    binders: &mut HashMap<HirParameterId, u32>,
    calls: &mut Vec<SourceCallPlan>,
    contract_sources: &'static [&'static str],
) -> Term {
    match expression {
        ResolvedExpr::Integer { .. } => session.batch.collected_leaf_term(Leaf::IntPositive),
        ResolvedExpr::Name {
            resolution: NameResolution::Parameter(parameter),
            ..
        } => {
            assert!(scope.contains(parameter));
            session
                .live_value_term(Polarity::Positive, binders[parameter])
                .unwrap()
        }
        ResolvedExpr::Group { inner, .. } => {
            bridge_plan_expression(session, inner, scope, binders, calls, contract_sources)
        }
        ResolvedExpr::Lambda {
            parameter, body, ..
        } => {
            let row = session.fresh_value_at_level(1).unwrap();
            assert!(binders.insert(parameter.clone(), row).is_none());
            scope.push(parameter.clone());
            let body =
                bridge_plan_expression(session, body, scope, binders, calls, contract_sources);
            scope.pop();
            // This returns a scalar body port for inspection; it does not
            // construct/publish an enclosing Lambda's complete Result.
            body
        }
        ResolvedExpr::Apply {
            occurrence,
            callee,
            argument,
            ..
        } => {
            let lower =
                bridge_plan_expression(session, callee, scope, binders, calls, contract_sources);
            let a =
                bridge_plan_expression(session, argument, scope, binders, calls, contract_sources);
            let argument_effect = session.fresh_effect_at_level(1).unwrap();
            let result_effect = session.fresh_effect_at_level(1).unwrap();
            let result = session.fresh_value_at_level(1).unwrap();
            let ae = session
                .live_effect_term(Polarity::Positive, argument_effect)
                .unwrap();
            let re = session
                .live_effect_term(Polarity::Negative, result_effect)
                .unwrap();
            let rn = session.live_value_term(Polarity::Negative, result).unwrap();
            let upper = session.negative_function_term(a, ae, re, rn).unwrap();
            calls.push(SourceCallPlan {
                lower,
                upper,
                dependency: UnelaboratedCompleteDependency {
                    contract_sources,
                    site: occurrence.clone(),
                    callee: callee.occurrence().clone(),
                    argument: argument.occurrence().clone(),
                    scope: scope.clone(),
                    argument_effect,
                    result_effect,
                    result,
                },
            });
            session.live_value_term(Polarity::Positive, result).unwrap()
        }
        _ => panic!("outside this research Name/Int/Group/Apply/Lambda source envelope"),
    }
}

#[cfg(feature = "shadow-f5")]
#[test]
fn deferred_call_constraints_collect_actual_hir_before_any_scalar_execution() {
    // Changing names and the integer changes no algorithmic branch.
    static CONTRACTS: &[&str] = &[
        include_str!("../../../../notes/design/2026-10-08-call-source-interface-definition.md"),
        include_str!(
            "../../../../notes/design/2026-10-07-complete-call-contribution-definition.md"
        ),
        include_str!(
            "../../../../notes/design/2026-10-08-contextual-function-membership-definition.md"
        ),
        include_str!(
            "../../../../notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md"
        ),
    ];
    for (source, expected_call_count) in [("my invoke f = f 1", 1), ("my relay g = g (g 7)", 2)] {
        let hir = bridge_source_hir(source);
        let mut session = InferenceSession::new(ConstraintBatch::collect(hir.clone()).unwrap());
        let mut binders = HashMap::new();
        let mut calls = Vec::new();
        let mut source_children = HashMap::new();
        for item in hir.items() {
            let HirItem::Binding(binding) = item else {
                panic!("source binding");
            };
            let mut source_nodes = vec![binding.value()];
            while let Some(expression) = source_nodes.pop() {
                match expression {
                    ResolvedExpr::Apply {
                        occurrence,
                        callee,
                        argument,
                        ..
                    } => {
                        assert!(
                            source_children
                                .insert(
                                    occurrence.clone(),
                                    (callee.occurrence().clone(), argument.occurrence().clone()),
                                )
                                .is_none()
                        );
                        source_nodes.push(callee);
                        source_nodes.push(argument);
                    }
                    ResolvedExpr::Lambda { body, .. } => source_nodes.push(body),
                    ResolvedExpr::Group { inner, .. } => source_nodes.push(inner),
                    _ => {}
                }
            }
            bridge_plan_expression(
                &mut session,
                binding.value(),
                &mut Vec::new(),
                &mut binders,
                &mut calls,
                CONTRACTS,
            );
        }
        // All calls are accumulated before the first actual solver operation.
        assert!(session.typed_pairs.is_empty());
        assert!(session.typed_worklist.is_empty());
        assert_eq!(binders.len(), 1);
        assert_eq!(calls.len(), expected_call_count);
        assert_eq!(source_children.len(), calls.len());
        if calls.len() == 2 {
            // The source walker emits inner calls before their enclosing call.
            // This distinguishes genuine nesting from two independent demands
            // that happen to share a formal and receive the same later lower.
            let TermView::NegativeFunction { argument, .. } =
                session.store.term_view(calls[1].upper).unwrap()
            else {
                panic!("outer Function demand");
            };
            assert_eq!(
                session.value_endpoint(argument, Polarity::Positive),
                ValueEndpointKey::ValueRow(calls[0].dependency.result)
            );
        }
        let formal = *binders.values().next().unwrap();
        let source_sites: Vec<_> = calls
            .iter()
            .map(|call| call.dependency.site.clone())
            .collect();
        for call in &calls {
            assert_eq!(
                session.value_endpoint(call.lower, Polarity::Positive),
                ValueEndpointKey::ValueRow(formal)
            );
            assert_ne!(call.dependency.site, call.dependency.callee);
            assert_ne!(call.dependency.site, call.dependency.argument);
            assert_eq!(
                source_children.get(&call.dependency.site),
                Some(&(
                    call.dependency.callee.clone(),
                    call.dependency.argument.clone()
                ))
            );
            assert_eq!(call.dependency.scope.len(), 1);
            assert!(std::ptr::eq(call.dependency.contract_sources, CONTRACTS));
            let occurrence = ConstraintOccurrenceId::new(call.dependency.site.clone(), 0);
            let cause = CauseId::for_occurrence(occurrence.clone());
            let key = CanonicalValuePairKey {
                lower: session.value_endpoint(call.lower, Polarity::Positive),
                upper: session.value_endpoint(call.upper, Polarity::Negative),
            };
            session
                .constrain_live_value(key, &occurrence, &cause)
                .unwrap();
        }
        let provider = bridge_provider(&mut session, 1);
        bridge_value(
            &mut session,
            ValueEndpointKey::PositiveFunction(provider.term),
            ValueEndpointKey::ValueRow(formal),
        );
        bridge_value(
            &mut session,
            ValueEndpointKey::IntPositive,
            ValueEndpointKey::ValueRow(provider.result),
        );
        for call in &calls {
            assert!(session.bounds[call.dependency.result as usize].has_int_positive_lower);
            assert!(
                session.effect_bounds[call.dependency.argument_effect as usize]
                    .direct_upper_rows
                    .contains(&provider.argument_effect)
            );
            assert!(
                session.effect_bounds[provider.result_effect as usize]
                    .direct_upper_rows
                    .contains(&call.dependency.result_effect)
            );
            assert!(!session.effect_bounds[call.dependency.result_effect as usize].has_empty_upper);
        }
        assert_eq!(
            calls
                .iter()
                .map(|call| call.dependency.site.clone())
                .collect::<Vec<_>>(),
            source_sites
        );
        if calls.len() == 2 {
            assert_ne!(calls[0].dependency.site, calls[1].dependency.site);
        }
        // All complete-contract obligations are still unelaborated. The HIR's
        // source pending errors remain present, and no SolvedModule is created.
        assert!(!hir.errors().is_empty());
        assert!(session.errors.is_empty());
    }
}
