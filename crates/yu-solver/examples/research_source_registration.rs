//! Source identity inventory for the applied companion receive/choose fixture.
//!
//! This only records this fixture's own parser, HIR, and candidate identities.
//! It does not identify a historical CST or infer the mathematical phase root.

use std::{
    fs,
    path::PathBuf,
    sync::Arc,
};

use yu_hir::{
    FileId, FileKey, HirItem, ModuleIdentity, SemanticImports, SourceRootId,
    shadow::{
        LocalSourceForm, LocalSourceScope, SourceOperationResolution,
        lower_module_with_local_source,
    },
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{
    SourceText, SyntaxEnvironment, parse_file, scan_header,
};

const FIXTURE: &str = include_str!("../../../tasks/agent-loop/fixtures/20261018-receive-choose-applied.yu");

fn main() {
    let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tasks/agent-loop/fixtures/20261018-receive-choose-applied.yu");
    let disk = match fs::read_to_string(&fixture_path) {
        Ok(source) => source,
        Err(error) => stop("fixture-read", error),
    };
    if disk != FIXTURE {
        stop("fixture-bytes", "include_str! bytes differ from the fixture on disk");
    }

    let source: Arc<SourceText> = Arc::from(FIXTURE);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let recoveries = parsed.structural_recoveries();
    println!("source.bytes={} source.revision={:?}", FIXTURE.len(), parsed.revision());
    println!("parse.structural_recoveries={recoveries:?}");
    if !recoveries.is_empty() {
        stop("parse-structural-recovery", "fixture has structural recovery; refusing HIR/candidate attribution");
    }

    let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
        "yulang-research",
        "tasks/agent-loop/fixtures/20261018-receive-choose-applied.yu",
    )));
    println!("hir.module_identity={identity:?}");
    let hir = match lower_module_with_local_source(identity, &parsed, SemanticImports::empty()) {
        Ok(hir) => Arc::new(hir),
        Err(error) => stop("hir-lowering", error),
    };
    println!("hir.source_revision={:?} hir.errors={:?}", hir.source_revision(), hir.errors());

    let f0 = binding(&hir, "f0");
    let receive = binding(&hir, "receive");
    let f0_root = f0.definition_root();
    let f0_key = match hir.definition_source_key(f0_root) {
        Ok(Some(key)) => key,
        other => stop("f0-source-key", format!("expected exact definition key, got {other:?}")),
    };
    println!("hir.f0.id={:?} root={f0_root:?} source_key={f0_key:?} parse_owns_key={}",
        f0.id(), parsed.owns_source_key(f0_key));
    println!("hir.receive.id={:?} root={:?} source_key={:?}",
        receive.id(), receive.definition_root(), hir.definition_source_key(receive.definition_root()));

    let declarations = hir.source_effect_declarations();
    let family = declarations.iter().find(|declaration| declaration.spelling.as_ref() == "ctrl")
        .unwrap_or_else(|| stop("ctrl-family", "no lowered ctrl family declaration"));
    let choose = family.operations.iter().find(|operation| operation.spelling.as_ref() == "choose")
        .unwrap_or_else(|| stop("choose-declaration", "no lowered choose declaration"));
    println!("hir.ctrl.family_id={:?} family_source={:?} family_range={:?}",
        family.id, family.id.declaration, family.range);
    println!("hir.choose.id={:?} declaration_key={:?} name_key={:?} signature_key={:?} range={:?}",
        choose.id, choose.id.declaration, choose.name_position, choose.signature_position, choose.range);
    for key in [&family.id.declaration, &choose.id.declaration, &choose.name_position, &choose.signature_position] {
        println!("parse.owns_declaration_key={}", parsed.owns_source_key(key));
    }
    println!("source_key.equalities family_member={} member_name={} member_signature={} name_signature={}",
        family.id.declaration == choose.id.declaration,
        choose.id.declaration == choose.name_position,
        choose.id.declaration == choose.signature_position,
        choose.name_position == choose.signature_position);

    let f0_source = match hir.local_source(f0_root) {
        Ok(Some(source)) => source,
        other => stop("f0-local-source", format!("expected HIR-owned LocalSource, got {other:?}")),
    };
    if f0_source.definition_root() != Some(f0_root) {
        stop("f0-local-source-owner", "LocalSource owner differs from f0 definition root");
    }
    let operation_uses: Vec<_> = f0_source.expressions().iter().filter_map(|expression| {
        matches!(&expression.form, LocalSourceForm::Operation { .. }).then_some(expression)
    }).collect();
    if operation_uses.len() != 1 {
        stop("f0-operation-inventory", format!("expected one operation occurrence, found {}", operation_uses.len()));
    }
    let use_expr = operation_uses[0];
    let LocalSourceForm::Operation { resolution: SourceOperationResolution::Resolved(resolved) } = &use_expr.form else {
        stop("choose-resolution", format!("operation resolution is not Resolved: {:?}", use_expr.form));
    };
    let use_key = match hir.occurrence_source_key(&use_expr.occurrence) {
        Ok(Some(key)) => key,
        Ok(None) => stop("choose-use-source-key", "HIR occurrence has no source-key record"),
        Err(error) => stop("choose-use-source-key", error),
    };
    println!("hir.choose_use.occurrence={:?} local_source_key={:?} occurrence_key={use_key:?} range={:?} scope={:?}",
        use_expr.occurrence, use_expr.source, use_expr.range, use_expr.scope);
    println!("parse.owns_choose_use_key={} resolved_id={:?} same_declaration_arc={}",
        parsed.owns_source_key(use_key), resolved.id, Arc::ptr_eq(resolved, choose));
    println!("source_key.equalities choose_use_member={} choose_use_name={} f0_definition_choose_use={}",
        use_expr.source == choose.id.declaration,
        use_expr.source == choose.name_position,
        f0_key == use_key);
    if !parsed.owns_source_key(use_key) || !Arc::ptr_eq(resolved, choose) || &use_expr.source != use_key {
        stop("choose-use-correspondence", "LocalSource use, HIR occurrence key, parse owner, and resolved declaration do not coincide");
    }

    let receive_source = match hir.local_source(receive.definition_root()) {
        Ok(Some(source)) => source,
        other => stop("receive-local-source", format!("expected HIR-owned LocalSource, got {other:?}")),
    };
    println!("hir.receive.expressions={}", receive_source.expressions().len());
    for expression in receive_source.expressions() {
        println!("hir.receive.expr occurrence={:?} source={:?} range={:?} form={:?}",
            expression.occurrence, expression.source, expression.range, expression.form);
    }

    let received = binding(&hir, "received");
    let received_root = received.definition_root();
    let received_owner = SourceRootId::Definition(received_root.clone());
    let received_source = match hir.local_source(received_root) {
        Ok(Some(source)) => source,
        other => stop("received-local-source", format!("expected HIR-owned LocalSource, got {other:?}")),
    };
    if received_source.definition_root() != Some(received_root)
        || received_source.source_root() != &received_owner
        || !hir.owns_source_root(&received_owner)
    {
        stop("received-source-owner", "received LocalSource does not belong to its exact HIR definition owner");
    }
    if std::env::var_os("YU_SCOPED_COLLECTION_DIAGNOSTIC").is_some() {
        for (index, expression) in received_source.expressions().iter().enumerate() {
            println!("hir.received.expr[{index}] occurrence={:?} source={:?} range={:?} scope={:?} form={:?}",
                expression.occurrence, expression.source, expression.range, expression.scope, expression.form);
        }
    }
    let applies: Vec<_> = received_source.expressions().iter().filter_map(|expression| {
        let LocalSourceForm::Apply { callee, argument, .. } = &expression.form else { return None };
        let callee = received_source.expression(callee)
            .unwrap_or_else(|| stop("received-apply-callee", "Apply callee index is not owned by received LocalSource"));
        let argument = received_source.expression(argument)
            .unwrap_or_else(|| stop("received-apply-argument", "Apply argument index is not owned by received LocalSource"));
        let key = hir.occurrence_source_key(&expression.occurrence)
            .unwrap_or_else(|error| stop("received-apply-key", error))
            .unwrap_or_else(|| stop("received-apply-key", "Apply occurrence has no HIR source key"));
        let callee_key = hir.occurrence_source_key(&callee.occurrence)
            .unwrap_or_else(|error| stop("received-callee-key", error))
            .unwrap_or_else(|| stop("received-callee-key", "callee occurrence has no HIR source key"));
        let argument_key = hir.occurrence_source_key(&argument.occurrence)
            .unwrap_or_else(|error| stop("received-argument-key", error))
            .unwrap_or_else(|| stop("received-argument-key", "argument occurrence has no HIR source key"));
        if expression.source != *key || !parsed.owns_source_key(key)
            || callee.source != *callee_key || !parsed.owns_source_key(callee_key)
            || argument.source != *argument_key || !parsed.owns_source_key(argument_key)
            || !hir.owns_occurrence(&expression.occurrence)
            || !hir.owns_occurrence(&callee.occurrence)
            || !hir.owns_occurrence(&argument.occurrence)
        {
            stop("received-apply-ownership", "Apply or operand occurrence/source key is not owned by this HIR/parse pair");
        }
        Some((expression, callee, argument, key, callee_key, argument_key))
    }).collect();
    if applies.len() != 1 {
        stop("received-apply-inventory", format!("expected one authentic Apply in received, found {}", applies.len()));
    }
    let (apply, apply_callee, apply_argument, apply_key, apply_callee_key, apply_argument_key) = applies[0];
    let LocalSourceForm::Name { resolution: yu_hir::shadow::LocalSourceResolution::ModuleDef(receive_def), .. } = &apply_callee.form else {
        stop("received-apply-callee-definition", format!("received Apply callee is not a ModuleDef: {:?}", apply_callee.form));
    };
    let LocalSourceForm::Name { resolution: yu_hir::shadow::LocalSourceResolution::ModuleDef(f0_def), .. } = &apply_argument.form else {
        stop("received-apply-argument-definition", format!("received Apply argument is not a ModuleDef: {:?}", apply_argument.form));
    };
    if receive_def != receive.id() || f0_def != f0.id() {
        stop("received-apply-operands", format!("expected ModuleDef(receive)/ModuleDef(f0), found {receive_def:?}/{f0_def:?}"));
    }
    println!("hir.received.operands=ModuleDef(receive:{receive_def:?}) ModuleDef(f0:{f0_def:?})");
    println!("hir.received.owner={received_owner:?} root={received_root:?} source_key={:?} parse_owns_key={} apply={:?}/{apply_key:?} callee={:?}/{apply_callee_key:?} argument={:?}/{apply_argument_key:?} scopes=({:?},{:?},{:?})",
        hir.definition_source_key(received_root), parsed.owns_source_key(apply_key),
        apply.occurrence, apply_callee.occurrence,
        apply_argument.occurrence,
        apply.scope, apply_callee.scope, apply_argument.scope);

    println!("candidate.solve=begin entry=CandidateInference::solve_scoped_experiment");
    let candidate = match CandidateInference::solve_scoped_experiment(hir.clone()) {
        Ok(candidate) => candidate,
        Err(error) => stop("candidate-solve", error),
    };
    let observes_hir = candidate.observes_hir(&hir);
    println!("candidate.observes_hir={observes_hir} candidate.conflicts={:?}", candidate.candidate_conflicts());
    if !observes_hir {
        stop("candidate-hir-owner", "candidate result does not observe the exact HIR artifact");
    }
    if !candidate.candidate_conflicts().is_empty() {
        stop("candidate-conflicts", "candidate solve returned conflicts; export is withheld");
    }

    let mut received_matches = 0usize;
    for index in 0..candidate.source_call_count() {
        let call = candidate.source_call(index)
            .unwrap_or_else(|error| stop("source-call-observation", error));
        if call.owner() != &received_owner { continue; }
        received_matches += 1;
        let source = call.source();
        let callee = call.callee_source();
        let argument = call.argument_source();
        let source_key = hir.occurrence_source_key(&source.occurrence)
            .unwrap_or_else(|error| stop("source-call-key", error))
            .unwrap_or_else(|| stop("source-call-key", "source_call Apply has no HIR source key"));
        let callee_key = hir.occurrence_source_key(&callee.occurrence)
            .unwrap_or_else(|error| stop("source-call-callee-key", error))
            .unwrap_or_else(|| stop("source-call-callee-key", "source_call callee has no HIR source key"));
        let argument_key = hir.occurrence_source_key(&argument.occurrence)
            .unwrap_or_else(|error| stop("source-call-argument-key", error))
            .unwrap_or_else(|| stop("source-call-argument-key", "source_call argument has no HIR source key"));
        let source_exact = std::ptr::eq(source, apply)
            && source.occurrence == apply.occurrence
            && source.source == apply.source
            && source.source == *source_key
            && source.source == *apply_key
            && parsed.owns_source_key(source_key);
        let callee_exact = std::ptr::eq(callee, apply_callee)
            && callee.occurrence == apply_callee.occurrence
            && callee.source == apply_callee.source
            && callee.source == *callee_key
            && callee.source == *apply_callee_key
            && parsed.owns_source_key(callee_key)
            && same_scope(&callee.scope, &apply_callee.scope);
        let argument_exact = std::ptr::eq(argument, apply_argument)
            && argument.occurrence == apply_argument.occurrence
            && argument.source == apply_argument.source
            && argument.source == *argument_key
            && argument.source == *apply_argument_key
            && parsed.owns_source_key(argument_key)
            && same_scope(&argument.scope, &apply_argument.scope);
        let source_scope_exact = same_scope(&source.scope, &apply.scope);
        let call_source_root_exact = hir.owns_source_root(call.owner())
            && received_source.source_root() == call.owner();
        let source_call_module_operands_exact = matches!(
            &callee.form,
            LocalSourceForm::Name { resolution: yu_hir::shadow::LocalSourceResolution::ModuleDef(definition), .. }
                if definition == receive.id()
        ) && matches!(
            &argument.form,
            LocalSourceForm::Name { resolution: yu_hir::shadow::LocalSourceResolution::ModuleDef(definition), .. }
                if definition == f0.id()
        );
        let checking_matches_apply = call.checking_occurrence().occurrence() == &apply.occurrence;
        let cause_matches_checking = call.checking_cause().occurrence() == call.checking_occurrence();
        let demand = call.native_demand();
        let demand_argument = call.native_argument();
        let demand_argument_effect = call.native_argument_evaluation_effect();
        let demand_invocation_effect = call.native_invocation_effect();
        let demand_result = call.native_result();
        println!("candidate.source_call[{index}].owner={:?} apply={:?}/{source_key:?} callee={:?}/{callee_key:?} argument={:?}/{argument_key:?} exact=(owner:{call_source_root_exact},apply:{source_exact},callee:{callee_exact},argument:{argument_exact},scope:{source_scope_exact},module_operands:{source_call_module_operands_exact},checking:{checking_matches_apply},cause:{cause_matches_checking})",
            call.owner(), source.occurrence, callee.occurrence, argument.occurrence);
        println!("candidate.source_call[{index}].validated_native_demand={demand:?} native_demand_children=(native_argument:{demand_argument:?}, native_argument_evaluation_effect:{demand_argument_effect:?}, native_invocation_effect:{demand_invocation_effect:?}, native_result:{demand_result:?})");
        if !call_source_root_exact || !source_exact || !callee_exact || !argument_exact
            || !source_scope_exact || !source_call_module_operands_exact
            || !checking_matches_apply || !cause_matches_checking
        {
            stop("source-call-correspondence", "validated source_call differs from the exact received Apply owner/occurrence/operands/source keys/scopes");
        }
    }
    if received_matches != 1 {
        stop("source-call-correspondence", format!("expected one source_call for received's exact Apply, found {received_matches}"));
    }
    let dependencies: Vec<_> = candidate.scoped_dependencies().map(|dependency| format!("{dependency:?}")).collect();
    let flows: Vec<_> = candidate.scoped_relation_flows().map(|(index, pair, flow, active)|
        format!("relation={index} pair={pair:?} flow={flow:?} active={active}")).collect();
    println!("candidate.aggregate_scoped_dependencies={dependencies:?}");
    println!("candidate.aggregate_relation_flows={flows:?}");
    if std::env::var_os("YU_CALL_REPLAY_OBSERVER").is_some() {
        println!("candidate.call_replay_observer=enabled (typed rows above identify original_call and ordered Replay endpoints; this is structural observation only)");
    } else {
        println!("candidate.received_call_replay_flow_linkage=UNOBSERVED (set YU_CALL_REPLAY_OBSERVER to stream typed internal Replay joins)");
    }
}

fn same_scope(left: &LocalSourceScope, right: &LocalSourceScope) -> bool {
    match (left, right) {
        (LocalSourceScope::Definition(left), LocalSourceScope::Definition(right)) => left == right,
        (LocalSourceScope::ModuleExpression(left), LocalSourceScope::ModuleExpression(right)) => left == right,
        (LocalSourceScope::Expression(left), LocalSourceScope::Expression(right)) => left == right,
        (LocalSourceScope::Parameter(left), LocalSourceScope::Parameter(right)) => left == right,
        (LocalSourceScope::LocalInitializer(left), LocalSourceScope::LocalInitializer(right)) => left == right,
        (LocalSourceScope::CatchArm { catch: left_catch, arm: left_arm },
            LocalSourceScope::CatchArm { catch: right_catch, arm: right_arm }) =>
            left_catch == right_catch && left_arm == right_arm,
        _ => false,
    }
}

fn binding<'a>(hir: &'a yu_hir::HirModule, spelling: &str) -> &'a yu_hir::HirBinding {
    hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == spelling => Some(binding),
        _ => None,
    }).unwrap_or_else(|| stop("binding", format!("missing module binding {spelling}")))
}

fn stop(stage: &str, error: impl std::fmt::Debug) -> ! {
    eprintln!("STOPPED at {stage}: {error:?}");
    std::process::exit(2)
}
