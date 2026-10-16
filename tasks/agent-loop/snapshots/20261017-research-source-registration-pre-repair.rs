//! Source identity inventory for the newly authored receive/choose fixture.
//!
//! This only records this fixture's own parser, HIR, and candidate identities.
//! It does not identify a historical CST or infer the mathematical phase root.

use std::{
    fs,
    path::PathBuf,
    sync::Arc,
};

use yu_hir::{
    FileId, FileKey, HirItem, ModuleIdentity, SemanticImports,
    shadow::{
        LocalSourceForm, SourceOperationResolution, lower_module_with_local_source,
    },
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{
    SourceText, SyntaxEnvironment, parse_file, scan_header,
};

const FIXTURE: &str = include_str!("../../../tasks/agent-loop/fixtures/20261017-receive-choose.yu");

fn main() {
    let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tasks/agent-loop/fixtures/20261017-receive-choose.yu");
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
        "tasks/agent-loop/fixtures/20261017-receive-choose.yu",
    )));
    println!("hir.module_identity={identity:?}");
    let hir = match lower_module_with_local_source(&identity, &parsed, SemanticImports::empty()) {
        Ok(hir) => Arc::new(hir),
        Err(error) => stop("hir-lowering", error),
    };
    println!("hir.source_revision={:?} hir.errors={:?}", hir.source_revision(), hir.errors());
    if !hir.errors().is_empty() {
        stop("hir-errors", "lowered HIR carries errors; candidate attribution is withheld");
    }

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

    println!("candidate.solve=begin entry=CandidateInference::solve");
    let candidate = match CandidateInference::solve(hir.clone()) {
        Ok(candidate) => candidate,
        Err(error) => stop("candidate-solve", error),
    };
    println!("candidate.observes_hir={} candidate.conflicts={:?}",
        candidate.observes_hir(&hir), candidate.candidate_conflicts());
    if !candidate.observes_hir(&hir) {
        stop("candidate-hir-owner", "candidate result does not observe the exact HIR artifact");
    }
    if !candidate.candidate_conflicts().is_empty() {
        stop("candidate-conflicts", "candidate solve returned conflicts; export is withheld");
    }

    // Only f0's source-owned definition root is exported. The selected graph
    // root is an implementation result, not the mathematical phase root R_e.
    let export = match candidate.export(f0_root) {
        Ok(export) => export,
        Err(error) => stop("candidate-export-f0", error),
    };
    let graph_root = export.root();
    println!("candidate.exported_definition_root={f0_root:?} graph_root_leaf={:?} graph_root_polarity={:?} graph_root_has_function_children={} node_count={}",
        graph_root.leaf(), graph_root.polarity(), graph_root.children().is_some(), export.node_count());
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
