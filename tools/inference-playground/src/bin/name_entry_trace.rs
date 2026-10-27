use std::{fmt::Write as _, fs, sync::Arc};

use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports, shadow::lower_module_with_local_source};
use yu_playground::runtime::{RuntimeEvidence, RuntimeOutcome, RuntimeProgram};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const SCRATCH_OUTPUT: &str = "/tmp/yulang-name-entry-correspondence-20261028/source/name-entry-trace.txt";
const CASES: &[(&str, &str)] = &[
    ("direct_positive", "my main = (\\x -> (\\y -> y) x) 41"),
    ("condition_local_z", "my main = (\\x -> { my z = x; (\\y -> y) (if x: z else: z) }) true"),
    ("sequence_local_z", "my main = (\\x -> { my z = x; (\\y -> y) {x; z} }) true"),
];

fn run_case(label: &str, input: &str) -> Result<String, Box<dyn std::error::Error>> {
    let text: Arc<SourceText> = Arc::from(input);
    let parsed = parse_file(text.clone(), Arc::new(scan_header(text)), Arc::new(SyntaxEnvironment::empty()));
    if !parsed.syntax_diagnostics().map_err(|e| std::io::Error::other(format!("{e:?}")))?.is_empty() {
        return Ok(format!("case={label}\ninput={input:?}\nstatus=UNRESOLVED unsupported-syntax\n"));
    }
    let hir = match lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("name-entry-target", format!("{label}.yu")))),
        &parsed,
        SemanticImports::empty(),
    ) {
        Ok(hir) => Arc::new(hir),
        Err(error) => return Ok(format!("case={label}\ninput={input:?}\nstatus=UNRESOLVED lowering-{error:?}\n")),
    };
    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default())
        .map_err(|e| std::io::Error::other(format!("{e:?}")))?;
    let selected = program.definition_named("main").map_err(|e| std::io::Error::other(format!("{e:?}")))?;
    let roots = program.execution_roots().map_err(|e| std::io::Error::other(format!("{e:?}")))?;
    let mut machine = program.start(selected, &roots).map_err(|e| std::io::Error::other(format!("{e:?}")))?;
    let outcome = machine.run(10_000);
    let mut out = String::new();
    writeln!(out, "case={label}")?;
    writeln!(out, "input={input:?}")?;
    writeln!(out, "outcome={outcome:?}")?;
    if !matches!(outcome, RuntimeOutcome::Completed(_)) {
        writeln!(out, "status=UNRESOLVED runtime-outcome")?;
        return Ok(out);
    }
    writeln!(out, "historical_trace_present={}", machine.name_entry_correspondence().is_some())?;
    let attempts = machine.name_entry_value_entry_attempts();
    let target: Vec<_> = attempts.iter().filter(|event| event.contains("entry_parameter=1 ")).collect();
    writeln!(out, "target_query=actual_ValueEntry_entry_parameter_ordinal_1")?;
    writeln!(out, "target_attempt_count={}", target.len())?;
    for event in &target { writeln!(out, "target_attempt={event}")?; }
    writeln!(out, "target_token_accepted={}", target.iter().any(|event| event.contains("token_accepted=true")))?;
    writeln!(out, "return_observations:")?;
    for event in machine.name_entry_return_observations() { writeln!(out, "  {event}")?; }
    writeln!(out, "name_return_observations:")?;
    for event in machine.name_entry_name_return_observations() { writeln!(out, "  {event}")?; }
    let status = if target.len() != 1 {
        "UNRESOLVED target-not-uniquely-executed"
    } else if label == "direct_positive" {
        if target[0].contains("token_accepted=true") { "POSITIVE target-token-accepted" }
        else { "INCOMPLETE positive-token-not-accepted" }
    } else if target[0].contains("token_accepted=false") && !target[0].contains("token_receipt=Some") {
        "NO-TOKEN at actual target ValueEntry; inspect source/return observations for equivalence"
    } else {
        "INCOMPLETE unexpected-target-token"
    };
    writeln!(out, "status={status}")?;
    Ok(out)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut out = String::from("targeted Name-entry causality observations; research only\n");
    for (label, input) in CASES {
        out.push_str(&run_case(label, input)?);
    }
    fs::write(SCRATCH_OUTPUT, &out)?;
    print!("{out}");
    Ok(())
}
