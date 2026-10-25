//! Provisional source/native evidence, not a binder/cell correspondence proof.
//! Run `machine` and `public` separately; each mode performs at most one execution.
use std::sync::Arc;

use yu_hir::shadow::{LocalSourceForm, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, HirItem, ModuleIdentity, SemanticImports};
use yu_playground::runtime::{RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeValueKind};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const NAME: &str = "source-generated-interaction-20261025.yu";
const STEP_BUDGET: usize = 30_000;
const SOURCE: &str = r#"act io:
    our tick: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(p), k -> {
    my first = k 11;
    my second = k 23;
    builtin_op::int_add first second
} }
my main = relay {
    my seed = 42;
    my result = io::tick 7;
    my loop again = if again: loop false else: builtin_op::int_add seed result;
    loop true
}
"#;

fn main() -> Result<(), String> {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "machine".into());
    if mode != "machine" && mode != "public" {
        return Err("mode must be machine or public".into());
    }
    println!("probe=SOURCE-GENERATED-INTERACTION-20261025 mode={mode}");
    println!("source_bytes={} step_budget={STEP_BUDGET}\n{SOURCE}", SOURCE.len());
    println!("provisional: candidate observation and execution do not certify typing, principality, or native correspondence");
    if mode == "public" {
        // This independently uses the ordinary world/candidate execution route.
        // Its public return value does not expose a transition count.
        let result = yu_playground::execute(SOURCE, NAME, "main", STEP_BUDGET, false);
        println!("public_execute={result:?} steps=NOT_EXPOSED");
        return match result {
            Ok(rendered) if rendered == "118\n" => Ok(()),
            Ok(rendered) => Err(format!("public result differs from source arithmetic 118: {rendered:?}")),
            Err(error) => Err(error),
        };
    }

    let text: Arc<SourceText> = Arc::from(SOURCE);
    let parsed = parse_file(
        text.clone(),
        Arc::new(scan_header(text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let diagnostics = parsed.syntax_diagnostics().map_err(|error| format!("syntax unavailable: {error:?}"))?;
    println!("syntax_diagnostics={diagnostics:?} structural_recoveries={:?}", parsed.structural_recoveries());
    if !diagnostics.is_empty() || !parsed.structural_recoveries().is_empty() {
        return Err("source parsing failed; no dependent execution".into());
    }
    let hir = Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("source-generated-interaction", NAME))),
        &parsed,
        SemanticImports::empty(),
    ).map_err(|error| format!("HIR unavailable: {error:?}"))?);
    for family in hir.source_effect_declarations() {
        for operation in &family.operations {
            println!("operation spelling={} id={:?}", operation.spelling, operation.id);
        }
    }
    for item in hir.items() {
        let HirItem::Binding(binding) = item else { continue };
        println!("definition={} root={:?}", binding.name().spelling(), binding.definition_root());
        let local = hir.local_source(binding.definition_root())
            .map_err(|error| format!("source unavailable: {error:?}"))?
            .ok_or_else(|| "missing local source".to_owned())?;
        for binder in local.bindings() {
            println!("local spelling={} id={:?} range={:?} initializer={:?}",
                binder.spelling, binder.id, binder.range, binder.initializer);
        }
        for expression in local.expressions() {
            if matches!(&expression.form,
                LocalSourceForm::Name { .. } | LocalSourceForm::Apply { .. }
                | LocalSourceForm::Lambda { .. } | LocalSourceForm::Catch { .. }
                | LocalSourceForm::Block { .. } | LocalSourceForm::StatementBlock { .. })
            {
                println!("source occurrence={:?} range={:?} text={:?} form={:?}",
                    expression.occurrence, expression.range,
                    SOURCE.get(expression.range.clone()), expression.form);
            }
        }
    }
    let candidate = CandidateInference::solve(hir.clone())
        .map_err(|error| format!("candidate unavailable: {error:?}"))?;
    println!("candidate observes_hir={} conflicts={}",
        candidate.observes_hir(&hir), candidate.candidate_conflicts().len());
    for conflict in candidate.candidate_conflicts().iter().take(8) {
        println!("candidate_conflict={conflict:?}");
    }
    if !candidate.observes_hir(&hir) || !candidate.candidate_conflicts().is_empty() {
        return Err("candidate route failed; no dependent execution".into());
    }
    // Same direct source-machine route as runtime_resume.rs. No forged frames,
    // cells, continuations, or hand-supplied name-consumption entries.
    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default())
        .map_err(|error| format!("runtime program unavailable: {error:?}"))?;
    let roots = program.execution_roots().map_err(|error| format!("roots: {error:?}"))?;
    let definition = program.definition_named("main").map_err(|error| format!("main: {error:?}"))?;
    let mut machine = program.start(definition, &roots).map_err(|error| format!("start: {error:?}"))?;
    let outcome = machine.run(STEP_BUDGET);
    println!("machine_outcome={outcome:?} steps={}", machine.steps());
    let RuntimeOutcome::Completed(handle) = outcome else {
        return Err("machine did not complete; retain outcome, stop dependent claims".into());
    };
    let value = machine.value(handle).ok_or_else(|| "completed handle unavailable".to_owned())?;
    println!("completed_value={value:?}");
    println!("internal_cells_environments_frames=NOT_EXPOSED; no identity claim from final value");
    match &value.kind {
        RuntimeValueKind::Integer(value) if value.as_ref() == "118" => Ok(()),
        other => Err(format!("machine result differs from source arithmetic 118: {other:?}")),
    }
}
