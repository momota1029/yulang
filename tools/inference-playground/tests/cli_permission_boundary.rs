use std::{
    io::Write,
    process::{Command, Stdio},
    sync::Arc,
};
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_playground::runtime::{
    Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeUnavailable,
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

#[test]
fn wrong_family_permission_withholds_runtime_and_cli_result() {
    let source = "act signal:\n    our ping: bool -> bool\nact other:\n    our unrelated: int -> int\nmy receive (input:[other] bool) = catch input { signal::ping(p), _ -> false }\nmy main = receive (signal::ping true)";
    assert_eq!(source.len(), 195);

    let text: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        text.clone(),
        Arc::new(scan_header(text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "inference-playground",
                "-",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty(), "{source}");

    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).unwrap();
    let selected = program.definition_named("main").unwrap();
    let mut machine = program.start_source_schedule(selected).unwrap();
    let direct_error = match machine.run(10_000) {
        RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(site)) => {
            RuntimeUnavailable::HandlerEvidence(site)
        }
        outcome => panic!("expected HandlerEvidence, got {outcome:?}"),
    };

    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", "10000", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(source.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert_eq!(
        output.stderr,
        format!("runtime unavailable: {direct_error:?}\n").as_bytes()
    );
}
