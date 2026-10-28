//! Provisional source/native witness; no private store or owner trace is exposed.
//! Remove this example to remove all its cost. It adds no production hot-path work.
use std::{sync::Arc, time::{Duration, Instant}};
use yu_hir::shadow::{LocalSourceForm, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, HirItem, ModuleIdentity, SemanticImports};
use yu_playground::runtime::{RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeValueKind};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const STEP_LIMIT: usize = 30_000;
const ROW_LIMIT: usize = 8;

fn main() -> Result<(), String> {
    // Optional selectors allow the primary to enforce a separate process timeout
    // on each of the four executions without rebuilding the example.
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() > 2
        || args.first().is_some_and(|arg| !matches!(arg.as_str(), "immediate" | "escaping" | "all"))
        || args.get(1).is_some_and(|arg| !matches!(arg.as_str(), "low" | "public" | "all"))
    {
        return Err("usage: source_generated_interaction_20261025 [immediate|escaping|all] [low|public|all]".into());
    }
    let mut failed = false;
    for case in ["immediate", "escaping"] {
        if args.first().is_some_and(|arg| arg != "all" && arg != case) { continue; }
        let expected = "44";
        let source = source(case == "escaping");
        println!("CASE={case} independent_capture_target={expected} derivation=(11+5)+(23+5) shared_last_response_discriminator=56\n{source}");
        if !args.get(1).is_some_and(|arg| arg == "public") {
            if let Err(error) = run_low(case, &source, expected) {
                println!("CASE={case} low_status=FAILED detail={error}");
                failed = true;
            }
        }
        if !args.get(1).is_some_and(|arg| arg == "low") {
            // Ordinary execution prepares its own world and source schedule.
            // An unavailable public route is evidence of a boundary, not permission
            // to treat RuntimeEvidence::default() as a production certificate.
            match yu_playground::execute(&source, &format!("{case}.yu"), "main", STEP_LIMIT, false) {
                Ok(actual) if actual == format!("{expected}\n") => {
                    println!("CASE={case} public_status=MATCH result={actual:?} steps=NOT_EXPOSED");
                }
                Ok(actual) => {
                    println!("CASE={case} public_status=BRIDGE_TARGET_MISMATCH expected={expected:?} actual={actual:?}; this alone does not adjudicate compiler semantics");
                    failed = true;
                }
                Err(error) => {
                    println!("CASE={case} public_status=REJECTED detail={error}");
                    failed = true;
                }
            }
        }
    }
    println!("SCOPE=provisional source/native evidence; private cell/owner correspondence and original A/B remain OPEN");
    if failed { Err("source witness failed; retain the printed failure and stop dependent claims".into()) }
    else { Ok(()) }
}

fn source(escaping: bool) -> String {
    // old is allocated before the request; recur is allocated in its suspended
    // suffix. Each invocation takes the self edge once before reading both captures.
    // The escaping case calls the first returned closure only after the second
    // resume has completed. 56 is the shared-last-response prediction;
    // it cannot alone identify private cell state or adjudicate a compiler bug.
    let thunk = if escaping { "[io] (bool -> int)" } else { "[io] int" };
    let combine = if escaping {
        "builtin_op::int_add (first true) (second true)"
    } else {
        "builtin_op::int_add first second"
    };
    let suffix_result = if escaping { "recur" } else { "recur true" };
    format!(r#"act io:
    our tick: int -> int
my relay (thunk:{thunk}) = catch thunk {{ io::tick(p), k -> {{ my first = k 11; my second = k 23; {combine} }} }}
my main = relay {{ my old = 5; my response = io::tick 7; my recur again = if again: recur false else: builtin_op::int_add response old; {suffix_result} }}
"#)
}

fn run_low(case: &str, source: &str, expected: &str) -> Result<(), String> {
    let text: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(text.clone(), Arc::new(scan_header(text)), Arc::new(SyntaxEnvironment::empty()));
    let diagnostics = parsed.syntax_diagnostics().map_err(|error| format!("syntax unavailable: {error:?}"))?;
    if !diagnostics.is_empty() || !parsed.structural_recoveries().is_empty() {
        return Err(format!("syntax diagnostics={diagnostics:?} recoveries={:?}", parsed.structural_recoveries()));
    }
    let hir = Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new(case, "source-generated-interaction.yu"))),
        &parsed, SemanticImports::empty(),
    ).map_err(|error| format!("lowering unavailable: {error:?}"))?);
    println!("CASE={case} hir_errors={} (candidate-mode placeholders are reported, not erased)", hir.errors().len());
    for error in hir.errors().iter().take(16) {
        println!("HIR_ERROR id={:?} origin={:?} kind={:?} attachment={:?} range={:?}",
            error.id(), error.origin(), error.kind(), error.attachment(), error.range());
    }
    if hir.errors().len() > 16 { return Err("HIR diagnostic presentation limit exceeded".into()); }
    let candidate = CandidateInference::solve(hir.clone()).map_err(|error| format!("candidate unavailable: {error:?}"))?;
    println!("CASE={case} same_hir={} candidate_conflicts={:?}", candidate.observes_hir(&hir), candidate.candidate_conflicts());
    if !candidate.observes_hir(&hir) || !candidate.candidate_conflicts().is_empty() {
        return Err("candidate observation unavailable/conflicting; this is not a source rejection theorem".into());
    }
    for family in hir.source_effect_declarations() {
        for operation in &family.operations {
            println!("OPERATION spelling={} id={:?}", operation.spelling, operation.id);
        }
    }
    for item in hir.items() {
        let HirItem::Binding(binding) = item else { continue; };
        let carrier = hir.local_source(binding.definition_root())
            .map_err(|error| format!("carrier unavailable: {error:?}"))?
            .ok_or_else(|| "source carrier missing".to_owned())?;
        println!("ROOT name={} id={:?}", binding.name().spelling(), binding.definition_root());
        if carrier.expressions().len() > 128 || carrier.bindings().len() > 16 {
            return Err("source observation presentation limit exceeded".into());
        }
        for local in carrier.bindings() {
            println!("BINDER name={} id={:?} initializer={:?} source={:?} range={:?}",
                local.spelling, local.id, local.initializer, local.binder_source, local.range);
        }
        for expression in carrier.expressions() {
            // These are retained typed constructors and source identities, not
            // fabricated execution states or spelling-based resolution guesses.
            println!("EXPR occurrence={:?} source={:?} range={:?} form={:?}",
                expression.occurrence, expression.source, expression.range, expression.form);
            if !matches!(&expression.form, LocalSourceForm::Apply { .. }) { continue; }
            match candidate.source_occurrence_observation(&expression.occurrence, ROW_LIMIT) {
                Ok(observation) => {
                    println!("FACTS occurrence={:?} facts_complete={} origins_complete={}",
                        expression.occurrence, observation.facts_complete(), observation.origins_complete());
                    for fact in observation.facts() {
                        println!("FACT source={:?} cause={:?} fact={:?}", fact.occurrence, fact.cause, fact.fact);
                    }
                    for origin in observation.origins() {
                        println!("ORIGIN graph={} source={:?} slot={} relation={} attribution={:?}",
                            origin.graph_index, origin.occurrence, origin.local_slot, origin.relation, origin.attribution);
                    }
                }
                Err(error) => println!("FACTS occurrence={:?} unavailable={error:?}", expression.occurrence),
            }
            match candidate.local_source_provider_observation(&expression.occurrence, ROW_LIMIT) {
                Ok(observation) => println!("LOCAL_APPLY apply={:?} callee={:?} target={:?} native_callee={:?} native_demand={:?} routes={} facts_complete={} origins_complete={} captures_truncated={} replay_child_receipt={} preservation_complete={}",
                    observation.apply, observation.callee, observation.target, observation.native_callee,
                    observation.native_demand, observation.routes.len(), observation.facts_complete,
                    observation.origins_complete, observation.captures_truncated,
                    observation.replay_child_completion_receipt_available, observation.preservation_complete),
                Err(error) => println!("LOCAL_APPLY occurrence={:?} unavailable={error:?}", expression.occurrence),
            }
        }
    }
    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default())
        .map_err(|error| format!("low-level program unavailable: {error:?}"))?;
    let roots = program.execution_roots().map_err(|error| format!("roots unavailable: {error:?}"))?;
    println!("CASE={case} execution_roots={roots:?} evidence=DEFAULT_RESEARCH_ROUTE");
    let main = program.definition_named("main").map_err(|error| format!("main unavailable: {error:?}"))?;
    let mut machine = program.start(main, &roots).map_err(|error| format!("start unavailable: {error:?}"))?;
    let started = Instant::now();
    for _ in 0..STEP_LIMIT {
        if started.elapsed() >= Duration::from_secs(30) {
            return Err(format!("wall budget exhausted; steps={}", machine.steps()));
        }
        match machine.step() {
            RuntimeOutcome::Running => {}
            RuntimeOutcome::Completed(handle) => {
                let value = machine.value(handle).ok_or_else(|| "completed handle unavailable".to_owned())?;
                println!("CASE={case} low_status=COMPLETED steps={} handle={handle:?} value={value:?}", machine.steps());
                return match &value.kind {
                    RuntimeValueKind::Integer(actual) if actual.as_ref() == expected => Ok(()),
                    _ => Err(format!("bridge-target mismatch: independent-capture target {expected}, observed {value:?}; 56 distinguishes shared last-response capture; this alone does not adjudicate compiler semantics")),
                };
            }
            outcome => return Err(format!("steps={} outcome={outcome:?}", machine.steps())),
        }
    }
    Err(format!("transition budget exhausted; steps={}", machine.steps()))
}
