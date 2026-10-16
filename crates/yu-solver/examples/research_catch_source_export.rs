//! Observational parse/HIR/candidate trace for the exact Catch research specimen.
//!
//! A successful run shows that these source-owned records reached the ordinary
//! candidate solver and its borrowed export APIs. It does not establish handler
//! adequacy, complete source typing, detached export, or execution.

use std::sync::Arc;

use yu_hir::{
    HirErrorKind, HirItem, ModuleIdentity, SemanticImports, SourceCarrierOutcome, SourceRootId, shadow::{
        LocalSourceCatchPattern, LocalSourceForm, LocalSourceResolution,
        SourceOperationResolution, lower_module_with_local_source,
    },
    FileId, FileKey,
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const SPECIMEN: &str = "act signal:\n    our ping: () -> (int -> int)\n\nmy id x = x; my result:int = catch (signal::ping())(1) { signal::ping(), k -> k id, v -> v }";

fn main() {
    if SPECIMEN.len() != 138 {
        stop("specimen-length", format!("expected 138 bytes, found {}", SPECIMEN.len()));
    }
    println!("source.bytes={} source.literal={SPECIMEN:?}", SPECIMEN.len());

    let source: Arc<SourceText> = Arc::from(SPECIMEN);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let recoveries = parsed.structural_recoveries();
    println!("parse.structural_recoveries={recoveries:?}");
    if !recoveries.is_empty() {
        stop("parse-structural-recovery", "refusing source/HIR attribution after structural recovery");
    }

    let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
        "catch-source-export-research",
        "source.yu",
    )));
    let hir = match lower_module_with_local_source(identity, &parsed, SemanticImports::empty()) {
        Ok(hir) => Arc::new(hir),
        Err(error) => stop("hir-lowering", error),
    };
    println!("hir.source_revision={:?} hir.errors={:?}", hir.source_revision(), hir.errors());
    let unsupported_items: Vec<_> = hir.errors().iter()
        .filter(|error| error.kind() == HirErrorKind::UnsupportedItem)
        .collect();
    let unsupported_expressions: Vec<_> = hir.errors().iter()
        .filter(|error| error.kind() == HirErrorKind::UnsupportedExpression)
        .collect();
    println!("hir.unsupported_item_errors={unsupported_items:?}");
    println!("hir.unsupported_expression_errors={unsupported_expressions:?}");
    if unsupported_items.is_empty() || unsupported_expressions.is_empty() {
        stop("partial-hir-diagnostic-boundary", "expected prior UnsupportedItem and UnsupportedExpression diagnostics are absent");
    }

    let id = binding(&hir, "id");
    let result = binding(&hir, "result");
    let id_root = id.definition_root();
    let result_root = result.definition_root();
    let id_key = source_key(&hir, id_root, "id-definition-source-key");
    let result_key = source_key(&hir, result_root, "result-definition-source-key");
    println!("hir.id.id={:?} root={id_root:?} source_key={id_key:?} parse_owns_key={}",
        id.id(), parsed.owns_source_key(id_key));
    println!("hir.result.id={:?} root={result_root:?} source_key={result_key:?} parse_owns_key={}",
        result.id(), parsed.owns_source_key(result_key));
    if !hir.owns_definition_root(id_root) || !hir.owns_definition_root(result_root)
        || !parsed.owns_source_key(id_key) || !parsed.owns_source_key(result_key)
    {
        stop("definition-root-authentication", "id/result roots or source keys are not owned by this HIR/parse pair");
    }

    let declarations = hir.source_effect_declarations();
    let signal = declarations.iter().find(|declaration| declaration.spelling.as_ref() == "signal")
        .unwrap_or_else(|| stop("signal-declaration", "missing source effect family signal"));
    let ping = signal.operations.iter().find(|operation| operation.spelling.as_ref() == "ping")
        .unwrap_or_else(|| stop("ping-declaration", "missing signal::ping declaration"));
    for (label, key) in [
        ("signal-family", &signal.id.declaration),
        ("ping-declaration", &ping.id.declaration),
        ("ping-name", &ping.name_position),
        ("ping-signature", &ping.signature_position),
    ] {
        println!("parse.owns_{label}_key={}", parsed.owns_source_key(key));
        if !parsed.owns_source_key(key) { stop("ping-declaration-source-key", label); }
    }
    println!("hir.signal.family_id={:?} family_key={:?} ping.id={:?} declaration_key={:?} name_key={:?} signature_key={:?}",
        signal.id, signal.id.declaration, ping.id, ping.id.declaration, ping.name_position, ping.signature_position);

    let id_source = local_source(&hir, id_root, "id-local-source");
    let result_source = local_source(&hir, result_root, "result-local-source");
    let id_parameter = match &id_source.expression(id_source.body()).unwrap().form {
        LocalSourceForm::Lambda { parameter, .. } => parameter,
        other => stop("id-parameter", format!("expected id's lambda parameter, found {other:?}")),
    };
    if id.parameters().len() != 1 || id.parameters()[0].id() != &id_parameter.id {
        stop("id-binder-link", "LocalSource x binder differs from the HIR id formal");
    }
    println!("hir.id.formal={:?} binder_source={:?} range={:?}",
        id_parameter.id, id_parameter.source, id_parameter.range);
    let parameter_use = id_source.expressions().iter().find(|expression| matches!(
        &expression.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(parameter) }
            if spelling.as_ref() == "x" && parameter == &id_parameter.id
    )).unwrap_or_else(|| stop("id-parameter-use", "no x use linked to id's actual parameter"));
    report_occurrence(&hir, &parsed, "id-x-use", parameter_use);

    let catch_expr = result_source.expressions().iter().find(|expression|
        matches!(&expression.form, LocalSourceForm::Catch { .. }))
        .unwrap_or_else(|| stop("result-catch", "no retained Catch expression in result"));
    report_occurrence(&hir, &parsed, "result-catch", catch_expr);
    let LocalSourceForm::Catch { scrutinee, arms } = &catch_expr.form else { unreachable!() };
    let scrutinee_source = result_source.expression(scrutinee)
        .unwrap_or_else(|| stop("catch-scrutinee", "scrutinee index is not owned by result LocalSource"));
    let LocalSourceForm::Apply { callee: grouped_callee, .. } = &scrutinee_source.form else {
        stop("scrutinee-outer-apply", format!("expected outer Apply in (signal::ping())(1), found {:?}", scrutinee_source.form));
    };
    let grouped_callee = result_source.expression(grouped_callee)
        .unwrap_or_else(|| stop("scrutinee-callee-group", "outer Apply callee index is not owned by result LocalSource"));
    let LocalSourceForm::Group { inner: operation_apply } = &grouped_callee.form else {
        stop("scrutinee-callee-group", format!("expected Group around signal::ping(), found {:?}", grouped_callee.form));
    };
    let operation_apply = result_source.expression(operation_apply)
        .unwrap_or_else(|| stop("scrutinee-operation-apply", "Group inner index is not owned by result LocalSource"));
    let LocalSourceForm::Apply { callee: operation_callee, .. } = &operation_apply.form else {
        stop("scrutinee-operation-apply", format!("expected inner Apply for signal::ping(), found {:?}", operation_apply.form));
    };
    let operation_callee = result_source.expression(operation_callee)
        .unwrap_or_else(|| stop("scrutinee-ping", "inner Apply callee index is not owned by result LocalSource"));
    let scrutinee_ping = match &operation_callee.form {
        LocalSourceForm::Operation { resolution: SourceOperationResolution::Resolved(operation) }
            if std::ptr::eq(operation.as_ref(), ping.as_ref()) => operation_callee,
        other => stop("scrutinee-ping", format!("scrutinee callee spine does not end at the declared ping operation: {other:?}")),
    };
    report_occurrence(&hir, &parsed, "scrutinee-outer-apply", scrutinee_source);
    report_occurrence(&hir, &parsed, "scrutinee-grouped-callee", grouped_callee);
    report_occurrence(&hir, &parsed, "scrutinee-operation-apply", operation_apply);
    report_occurrence(&hir, &parsed, "scrutinee-signal-ping", scrutinee_ping);

    let (operation_arm, value_arm) = {
        let mut operation_arm = None;
        let mut value_arm = None;
        for arm in arms {
            match &arm.pattern {
                LocalSourceCatchPattern::Operation { resolution: SourceOperationResolution::Resolved(operation), .. }
                    if std::ptr::eq(operation.as_ref(), ping.as_ref()) => operation_arm = Some(arm),
                LocalSourceCatchPattern::Value(_) => value_arm = Some(arm),
                _ => {}
            }
        }
        (operation_arm.unwrap_or_else(|| stop("catch-ping-arm", "no Catch operation arm resolved to declared ping")),
         value_arm.unwrap_or_else(|| stop("catch-value-arm", "no Catch normal-value arm")))
    };
    let LocalSourceCatchPattern::Operation { operation_source, payloads, continuation, .. } = &operation_arm.pattern else { unreachable!() };
    let continuation_binder = match continuation {
        yu_hir::shadow::LocalSourceCatchValuePattern::Binder(binder) => binder,
        yu_hir::shadow::LocalSourceCatchValuePattern::Wildcard => stop("continuation-binder", "selected operation arm continuation is a wildcard"),
    };
    println!("hir.ping.scrutinee_occurrence={:?} source_key={:?}", scrutinee_ping.occurrence, scrutinee_ping.source);
    println!("hir.ping.catch_occurrence_source={operation_source:?} payloads={payloads:?} continuation={continuation:?}");
    if !parsed.owns_source_key(operation_source) || operation_arm.source != continuation_source(continuation, &operation_arm.source) {
        stop("catch-ping-source-ownership", "operation pattern key is not parse-owned or continuation arm ownership differs");
    }
    println!("parse.owns_ping_pattern_key={}", parsed.owns_source_key(operation_source));

    let k_use = result_source.expressions().iter().find(|expression| matches!(
        &expression.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::CatchBinder(binder) }
            if spelling.as_ref() == "k" && binder == &continuation_binder.id
    )).unwrap_or_else(|| stop("callback-continuation-use", "no k use linked to the actual continuation binder"));
    report_occurrence(&hir, &parsed, "callback-k-use", k_use);
    let id_use = result_source.expressions().iter().find(|expression| matches!(
        &expression.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::ModuleDef(definition) }
            if spelling.as_ref() == "id" && definition == id.id()
    )).unwrap_or_else(|| stop("callback-id-use", "no source use of id linked to its actual module definition"));
    report_occurrence(&hir, &parsed, "callback-id-use", id_use);
    println!("hir.catch.continuation_binder={:?} callback_body={:?} callback_k_use={:?}",
        continuation_binder.id, result_source.expression(&operation_arm.body).unwrap().occurrence, k_use.occurrence);

    let LocalSourceCatchPattern::Value(value_pattern) = &value_arm.pattern else { unreachable!() };
    let value_binder = match value_pattern {
        yu_hir::shadow::LocalSourceCatchValuePattern::Binder(binder) => binder,
        yu_hir::shadow::LocalSourceCatchValuePattern::Wildcard => stop("normal-value-binder", "normal arm is not the v binder arm"),
    };
    let value_use = result_source.expressions().iter().find(|expression| matches!(
        &expression.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::CatchBinder(binder) }
            if spelling.as_ref() == "v" && binder == &value_binder.id
    )).unwrap_or_else(|| stop("normal-value-use", "no v use linked to the normal arm binder"));
    report_occurrence(&hir, &parsed, "normal-v-use", value_use);
    println!("hir.catch.normal_value_pattern={value_pattern:?} normal_arm_source={:?} normal_arm_body={:?}",
        value_arm.source, result_source.expression(&value_arm.body).unwrap().occurrence);

    let applies: Vec<_> = result_source.expressions().iter().filter(|expression|
        matches!(&expression.form, LocalSourceForm::Apply { .. })).collect();
    println!("hir.result.apply_count={}", applies.len());
    if applies.len() != 3 { stop("apply-inventory", format!("expected 3 retained Apply sites in result, found {}", applies.len())); }
    for (index, apply) in applies.iter().enumerate() {
        report_occurrence(&hir, &parsed, &format!("apply-{index}"), apply);
    }

    let mut supported_sources: Vec<(SourceRootId, &yu_hir::shadow::LocalSource)> = Vec::new();
    for (owner, outcome) in hir.source_carrier_outcomes() {
        let SourceCarrierOutcome::Supported(source) = outcome else { continue };
        if source.source_root() != owner || !hir.owns_source_root(owner) {
            stop("source-carrier-owner", format!("source carrier root is not owned by this HIR: {owner:?}"));
        }
        let owned_source = hir.local_source_for(owner)
            .unwrap_or_else(|error| stop("source-carrier-lookup", error))
            .unwrap_or_else(|| stop("source-carrier-lookup", format!("supported carrier disappeared for {owner:?}")));
        if !std::ptr::eq(source, owned_source) {
            stop("source-carrier-identity", format!("carrier lookup changed the source object for {owner:?}"));
        }
        supported_sources.push((owner.clone(), source));
    }
    // The opt-in binding adapter stores supported LocalSource values in the
    // definition-root map, outside source_carrier_outcomes(). Enumerate all
    // binding roots through HIR ownership and join them with expression
    // carriers by authentic root, checking duplicate views for identity.
    for item in hir.items() {
        let HirItem::Binding(binding) = item else { continue };
        let owner = SourceRootId::Definition(binding.definition_root().clone());
        if !hir.owns_source_root(&owner) {
            stop("binding-source-owner", format!("binding root is not owned by this HIR: {owner:?}"));
        }
        let Some(source) = hir.local_source(binding.definition_root())
            .unwrap_or_else(|error| stop("binding-source-lookup", error)) else { continue };
        if source.source_root() != &owner {
            stop("binding-source-owner", format!("binding LocalSource has a different owner: {owner:?}"));
        }
        if let Some((_, existing)) = supported_sources.iter().find(|(root, _)| root == &owner) {
            if !std::ptr::eq(*existing, source) {
                stop("source-carrier-identity", format!("duplicate owner resolves to different LocalSource objects: {owner:?}"));
            }
        } else {
            supported_sources.push((owner, source));
        }
    }

    let mut authentic_applies = Vec::new();
    for (owner, source) in &supported_sources {
        for expression in source.expressions() {
            let source_key = hir.occurrence_source_key(&expression.occurrence)
                .unwrap_or_else(|error| stop("apply-inventory-source-key", error))
                .unwrap_or_else(|| stop("apply-inventory-source-key", format!("no source key for {:?}", expression.occurrence)));
            if source_key != &expression.source || !parsed.owns_source_key(source_key) {
                stop("apply-inventory-source-key", format!("source key is not exact and parse-owned for {:?}", expression.occurrence));
            }
            let LocalSourceForm::Apply { callee, argument, .. } = &expression.form else { continue };
            let callee = source.expression(callee)
                .unwrap_or_else(|| stop("apply-inventory-callee", format!("Apply callee index is not owned by {owner:?}")));
            let argument = source.expression(argument)
                .unwrap_or_else(|| stop("apply-inventory-argument", format!("Apply argument index is not owned by {owner:?}")));
            authentic_applies.push((owner.clone(), expression, callee, argument));
        }
    }
    println!("hir.authentic_apply_count={}", authentic_applies.len());
    if authentic_applies.len() != applies.len() {
        stop("apply-inventory", format!("result-local Apply count {} differs from all supported HIR LocalSource Apply count {}", applies.len(), authentic_applies.len()));
    }

    println!("candidate.solve=begin entry=CandidateInference::solve");
    let candidate = match CandidateInference::solve(hir.clone()) {
        Ok(candidate) => candidate,
        Err(error) => stop("candidate-solve", error),
    };
    let observes_hir = candidate.observes_hir(&hir);
    let conflicts = candidate.candidate_conflicts();
    println!("candidate.observes_hir={observes_hir} candidate.conflict_count={} candidate.conflicts={conflicts:?}", conflicts.len());
    if !observes_hir { stop("candidate-hir-owner", "candidate result does not observe this exact HIR artifact"); }
    if !conflicts.is_empty() { stop("candidate-conflicts", "ordinary solve returned conflicts; withholding exports and fresh-use observation"); }

    let mut matched_calls = vec![0usize; authentic_applies.len()];
    for index in 0..candidate.source_call_count() {
        let call = candidate.source_call(index)
            .unwrap_or_else(|error| stop("source-call-observation", error));
        let occurrence = &call.source().occurrence;
        let occurrence_key = hir.occurrence_source_key(occurrence)
            .unwrap_or_else(|error| stop("source-call-occurrence-key", error))
            .unwrap_or_else(|| stop("source-call-occurrence-key", "HIR has no key for source_call occurrence"));
        if call.source().source != *occurrence_key || !parsed.owns_source_key(occurrence_key) {
            stop("source-call-source-key", format!("source_call {index} key is not exact and parse-owned"));
        }
        if !hir.owns_source_root(call.owner()) {
            stop("source-call-owner", format!("source_call {index} has a foreign owner {:?}", call.owner()));
        }
        let matches: Vec<_> = authentic_applies.iter().enumerate().filter(|(_, (owner, expression, _, _))|
            owner == call.owner()
                && expression.occurrence == *occurrence
                && expression.source == *occurrence_key
        ).collect();
        if matches.len() != 1 {
            stop("source-call-bijection", format!("source_call {index} matched {} authentic Apply occurrences", matches.len()));
        }
        let apply_index = matches[0].0;
        let (owner, apply, callee, argument) = &authentic_applies[apply_index];
        let (apply, callee, argument) = (*apply, *callee, *argument);
        let source_exact = std::ptr::eq(call.source(), apply)
            && call.source().occurrence == apply.occurrence
            && call.source().source == apply.source;
        let callee_exact = std::ptr::eq(call.callee_source(), callee)
            && call.callee_source().occurrence == callee.occurrence
            && call.callee_source().source == callee.source;
        let argument_exact = std::ptr::eq(call.argument_source(), argument)
            && call.argument_source().occurrence == argument.occurrence
            && call.argument_source().source == argument.source;
        let checking_matches_apply = call.checking_occurrence().occurrence() == &apply.occurrence;
        let cause_matches_checking = call.checking_cause().occurrence() == call.checking_occurrence();
        println!("candidate.source_call[{index}].owner={:?} apply={:?}/{:?} callee={:?}/{:?} argument={:?}/{:?} source_exact={source_exact} callee_exact={callee_exact} argument_exact={argument_exact} checking_occurrence={:?} checking_matches_apply={checking_matches_apply} checking_cause={:?} cause_matches_checking={cause_matches_checking}",
            call.owner(), occurrence, occurrence_key,
            call.callee_source().occurrence, call.callee_source().source,
            call.argument_source().occurrence, call.argument_source().source,
            call.checking_occurrence(), call.checking_cause());
        if !source_exact || !callee_exact || !argument_exact || !checking_matches_apply || !cause_matches_checking {
            stop("source-call-bijection", format!("source_call {index} disagrees with authentic Apply owner/source/operands/checking provenance"));
        }
        matched_calls[apply_index] += 1;
    }
    println!("candidate.source_call_count={} authentic_apply_count={} per_apply_matches={matched_calls:?}", candidate.source_call_count(), authentic_applies.len());
    if candidate.source_call_count() != authentic_applies.len() || matched_calls.iter().any(|count| *count != 1) {
        stop("source-call-bijection", "CandidateSourceCall records are missing, duplicated, or extra relative to authentic Apply occurrences");
    }

    match candidate.fresh_use(&id_use.occurrence) {
        Some(fresh_use) => {
            let exact_occurrence = fresh_use.occurrence() == &id_use.occurrence;
            println!("candidate.fresh_use.id_occurrence={:?} exact_occurrence={exact_occurrence} fresh_rows={}",
                fresh_use.occurrence(), fresh_use.rows().count());
            if !exact_occurrence { stop("fresh-use-occurrence", "public fresh_use returned a different source occurrence"); }
        }
        None => println!("candidate.fresh_use.id_occurrence={:?} result=None", id_use.occurrence),
    }

    for (label, root) in [("id", id_root), ("result", result_root)] {
        let export = candidate.export(root)
            .unwrap_or_else(|error| stop("candidate-export", format!("{label} root {root:?}: {error:?}")));
        println!("candidate.export.{label}.definition_root={root:?} graph_root_leaf={:?} graph_root_polarity={:?} node_count={} rows={}",
            export.root().leaf(), export.root().polarity(), export.node_count(), export.rows().count());
    }

    println!("boundary=CATCH-SPECIMEN-TYPED-INCIDENCE remains open; this is source/HIR/candidate observation only, not handler adequacy, full source typing, detached export, runtime execution, or parent closure");
}

fn binding<'a>(hir: &'a yu_hir::HirModule, spelling: &str) -> &'a yu_hir::HirBinding {
    hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == spelling => Some(binding),
        _ => None,
    }).unwrap_or_else(|| stop("binding", format!("missing binding {spelling}")))
}

fn source_key<'a>(
    hir: &'a yu_hir::HirModule,
    root: &yu_hir::DefinitionRootId,
    stage: &str,
) -> &'a yu_syntax::SourceNodeKey {
    hir.definition_source_key(root)
        .unwrap_or_else(|error| stop(stage, error))
        .unwrap_or_else(|| stop(stage, "no definition source key"))
}

fn local_source<'a>(
    hir: &'a yu_hir::HirModule,
    root: &yu_hir::DefinitionRootId,
    stage: &str,
) -> &'a yu_hir::shadow::LocalSource {
    hir.local_source(root)
        .unwrap_or_else(|error| stop(stage, error))
        .unwrap_or_else(|| stop(stage, "no HIR-owned LocalSource"))
}

fn report_occurrence(
    hir: &yu_hir::HirModule,
    parsed: &yu_syntax::ParsedFile,
    label: &str,
    expression: &yu_hir::shadow::LocalSourceExpr,
) {
    let key = hir.occurrence_source_key(&expression.occurrence)
        .unwrap_or_else(|error| stop("occurrence-source-key", error))
        .unwrap_or_else(|| stop("occurrence-source-key", format!("{label} has no HIR source key")));
    let agrees = key == &expression.source;
    let parse_owns = parsed.owns_source_key(key);
    println!("hir.{label}.occurrence={:?} local_source_key={:?} hir_source_key={key:?} range={:?} exact_key_agreement={agrees} parse_owns_key={parse_owns}",
        expression.occurrence, expression.source, expression.range);
    if !agrees || !parse_owns { stop("occurrence-source-correspondence", label); }
}

fn continuation_source(
    continuation: &yu_hir::shadow::LocalSourceCatchValuePattern,
    arm_source: &yu_syntax::SourceNodeKey,
) -> yu_syntax::SourceNodeKey {
    match continuation {
        yu_hir::shadow::LocalSourceCatchValuePattern::Binder(binder) => {
            if binder.id.arm_source() != arm_source {
                stop("continuation-owner", "continuation binder is not owned by its actual Catch arm");
            }
            arm_source.clone()
        }
        yu_hir::shadow::LocalSourceCatchValuePattern::Wildcard => {
            stop("continuation-binder", "selected operation arm continuation is a wildcard")
        }
    }
}

fn stop(stage: &str, error: impl std::fmt::Debug) -> ! {
    eprintln!("STOPPED at {stage}: {error:?}");
    std::process::exit(2)
}
