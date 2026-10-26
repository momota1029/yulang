// Observation-only client for a privately patched solver snapshot.
// Build this file as an external binary; do not add the patch to production.
use std::sync::Arc;
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, HirItem, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, SourceRevision, SyntaxDependencyProvenance,
    SyntaxDependencySlot, SyntaxEnvironmentKey, parse_file, scan_header};

#[path = "../../../tools/inference-playground/src/pinned_stdlib.rs"]
mod pinned_stdlib;

// Same syntax constructor as the unchanged CLI, using its exact pinned bytes.
fn syntax_environment() -> Result<SyntaxEnvironment, String> {
    let resolved = pinned_stdlib::resolve_implicit_stdlib().map_err(|e| format!("stdlib: {e:?}"))?;
    let source = resolved.iter().find(|s| s.path == "lib/std/core/ops.yu").ok_or("missing ops")?;
    let fingerprint = pinned_stdlib::fingerprint(&source.git_blob);
    let text: Arc<SourceText> = Arc::from(source.text);
    let header = scan_header(text);
    let dependency = SyntaxDependencySlot::from_index(0).ok_or("dependency slot")?;
    let provenance = Arc::from([SyntaxDependencyProvenance::new(
        Arc::from(source.path), SourceRevision::from_fingerprint(fingerprint))]);
    SyntaxEnvironment::from_imported_headers(SyntaxEnvironmentKey::from_fingerprint(fingerprint),
        [(dependency, &header)], provenance).map_err(|e| format!("syntax: {e:?}"))
}

fn main() -> Result<(), String> {
    let path = std::env::args().nth(1).ok_or("one source file required")?;
    let text = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
    let source: Arc<SourceText> = Arc::from(text.as_str());
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(syntax_environment()?),
    );
    let diagnostics = parsed.syntax_diagnostics().map_err(|e| format!("syntax availability: {e:?}"))?;
    if !diagnostics.is_empty() { return Err(format!("syntax: {diagnostics:?}")); }
    let hir = Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("original-proof-r3", path))),
        &parsed,
        SemanticImports::empty(),
    ).map_err(|e| format!("lowering: {e:?}"))?);
    // The unchanged CLI delegates support to the resolved local-source solver;
    // the older general HIR may retain UnsupportedExpression diagnostics.
    println!("general_hir_diagnostics={}", hir.errors().len());
    let candidate = CandidateInference::solve(hir.clone()).map_err(|e| format!("solver: {e:?}"))?;
    println!("same_hir={} conflicts={} source_calls={}", candidate.observes_hir(&hir),
        candidate.candidate_conflicts().len(), candidate.source_call_count());
    for conflict in candidate.candidate_conflicts().iter().take(20) { println!("conflict={conflict:?}"); }
    Ok(())
}
