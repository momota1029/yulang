use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

#[test]
fn compatible_run_accepts_explicit_std_root() {
    let (entry, std_root) = write_fixture("run-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
}

#[test]
fn compatible_run_suppresses_roots_without_print_roots() {
    let (entry, std_root) = write_fixture("run-suppress-roots", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("run")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "");
}

#[test]
fn compatible_run_prints_console_stdout_without_roots() {
    let entry = write_entry("run-console-stdout", "say \"Hello, World\"\nsay: 1 + 2\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("run")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "Hello, World\n3\n");
}

#[test]
fn compatible_run_accepts_eval_source() {
    let output = yulang_command()
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg("-e")
        .arg("1")
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
}

#[test]
fn compatible_run_reads_piped_stdin_without_path() {
    let output = yulang_command_with_stdin(["--no-prelude", "run", "--print-roots"], "1\n");

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
}

#[test]
fn compatible_run_reads_explicit_stdin_path() {
    let output = yulang_command_with_stdin(["--no-prelude", "run", "--print-roots", "-"], "1\n");

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
}

#[test]
fn compatible_run_print_roots_keeps_console_stdout_before_roots() {
    let entry = write_entry("run-console-stdout-roots", "say \"Hello\"\n1 + 2\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "Hello\nrun roots [(), 3]\n");
}

#[test]
fn compatible_check_accepts_explicit_std_root() {
    let (entry, std_root) = write_fixture("check-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("check")
        .arg("--std-root")
        .arg(&std_root)
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("check-poly-std\n"), "{stdout}");
    assert!(stdout.contains("files: 3\n"), "{stdout}");
    assert!(stdout.contains("lowering errors: 0\n"), "{stdout}");
}

#[test]
fn compatible_check_no_prelude_uses_local_source_only() {
    let entry = write_entry("check-no-prelude", "1\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("check-poly\n"), "{stdout}");
    assert!(stdout.contains("files: 1\n"), "{stdout}");
}

#[test]
fn public_diagnostics_check_reports_type_annotation_mismatch() {
    let entry = repo_yulang_fixture("regressions/diagnostics/type_annotation_mismatch.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.type-mismatch]: x: type mismatch: bool is not int\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains("  x: type mismatch: bool is not int\n"),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_unresolved_value_name() {
    let entry = repo_yulang_fixture("regressions/diagnostics/unresolved_value_name.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.unresolved-value]: result: unresolved value name: missing\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains("  result: unresolved value name: missing\n"),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_unresolved_type_name() {
    let entry = repo_yulang_fixture("regressions/diagnostics/unresolved_type_name.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.unresolved-type]: x: unresolved type name: missing_type\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains("  x: unresolved type name: missing_type\n"),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_unsupported_type_syntax() {
    let entry =
        repo_yulang_fixture("regressions/diagnostics/unsupported_record_type_annotation.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.unsupported-type-syntax]: x: unsupported type annotation syntax: TypeRecord\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains("  x: unsupported type annotation syntax: TypeRecord\n"),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_top_level_mutable_binding() {
    let entry = repo_yulang_fixture("regressions/diagnostics/top_level_mutable_binding.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.top-level-mutable-binding]: $x: top-level mutable binding $x is not supported; move it into a block or function body\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains(
            "  $x: top-level mutable binding $x is not supported; move it into a block or function body\n"
        ),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_rule_lazy_quantifier() {
    let entry = repo_yulang_fixture("regressions/diagnostics/rule_lazy_quantifier.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.unsupported-rule-lazy-quantifier]: p: rule lazy quantifier `*?` is not supported; rule uses PEG-style greedy repetition\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains(
            "  p: rule lazy quantifier `*?` is not supported; rule uses PEG-style greedy repetition\n"
        ),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_recovers_unclosed_paren_without_panic() {
    let entry = repo_yulang_fixture("regressions/diagnostics/unclosed_paren.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("check-poly\n"), "{stdout}");
    assert!(stdout.contains("lowering errors: 0\n"), "{stdout}");
    assert_eq!(stderr(&output), "");
}

#[test]
fn compatible_global_cst_and_timing_flags_are_accepted() {
    let entry = write_entry("global-cst", "1\n");

    let output = yulang_command()
        .arg("check")
        .arg("--cst")
        .arg("--infer-phase-timings")
        .arg("--no-cache")
        .arg("--no-prelude")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("Root\n"), "{stdout}");
    assert!(stdout.contains("check-poly\n"), "{stdout}");
}

#[test]
fn compatible_build_writes_control_vm_artifact_and_run_loads_it() {
    let entry = write_entry("build-artifact", "1\n");
    let artifact = entry.with_extension("yuir");

    let build_output = yulang_command()
        .arg("--no-prelude")
        .arg("build")
        .arg("--out")
        .arg(&artifact)
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&build_output);
    assert_eq!(
        stdout(&build_output),
        format!("build: {}\n", artifact.display())
    );
    let artifact_source = fs::read_to_string(&artifact).unwrap();
    assert!(
        artifact_source.starts_with("YULANG-CONTROL-VM 1\n"),
        "{artifact_source}"
    );

    let run_output = yulang_command()
        .arg("run")
        .arg("--print-roots")
        .arg(&artifact)
        .output()
        .unwrap();
    assert_success(&run_output);
    assert_eq!(stdout(&run_output), "run roots [1]\n");

    let debug_output = yulang_command()
        .arg("debug")
        .arg("control-vm-load")
        .arg("--print-roots")
        .arg(&artifact)
        .output()
        .unwrap();
    assert_success(&debug_output);
    assert_eq!(stdout(&debug_output), "run roots [1]\n");
}

#[test]
fn compatible_dump_core_ir_accepts_explicit_std_root() {
    let (entry, std_root) = write_fixture("dump-core-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("dump")
        .arg("--core-ir")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("roots d0:std\n"), "{stdout}");
    assert!(stdout.contains("root exprs e0:1\n"), "{stdout}");
}

#[test]
fn compatible_dump_runtime_ir_maps_to_mono_dump() {
    let (entry, std_root) = write_fixture("dump-runtime-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("dump")
        .arg("--runtime-ir")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "mono roots [1]\n");
}

#[test]
fn compatible_dump_control_evidence_accepts_explicit_std_root() {
    let (entry, std_root) = write_fixture("dump-control-evidence-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("dump")
        .arg("--control-evidence")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("control evidence roots ["), "{stdout}");
    assert!(stdout.contains("runtime evidence tasks ["), "{stdout}");
    assert!(stdout.contains("  graph slots "), "{stdout}");
}

#[test]
fn compatible_dump_control_evidence_prints_runtime_source_sites() {
    let (entry, std_root) = write_fixture(
        "dump-control-evidence-runtime-sites",
        "act out:\n  our say: int -> unit\n\n\
         my handle(action: [out] _) = catch action:\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n\n\
         handle(out::say(1))\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("dump")
        .arg("--control-evidence")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("  nodes "), "{stdout}");
    assert!(stdout.contains("  sites "), "{stdout}");
    assert!(
        stdout.contains("operation-call callee"),
        "operation call site should be visible in dump:\n{stdout}"
    );
    assert!(
        stdout.contains("catch body"),
        "catch site should be visible in dump:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_bench_prints_timing_and_size_metrics() {
    let entry = write_entry(
        "debug-runtime-evidence-bench",
        "act out:\n  our say: int -> unit\n\n\
         my handle(action: [out] _) = catch action:\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n\n\
         handle(out::say(1))\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-bench")
        .arg("--repeat")
        .arg("1")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("runtime evidence bench:"), "{stdout}");
    assert!(stdout.contains("iteration 1:"), "{stdout}");
    assert!(stdout.contains("bench.cache: disabled"), "{stdout}");
    assert!(stdout.contains("bench.specialize:"), "{stdout}");
    assert!(stdout.contains("bench.control_lower:"), "{stdout}");
    assert!(stdout.contains("evidence.tasks:"), "{stdout}");
    assert!(stdout.contains("evidence.nodes:"), "{stdout}");
    assert!(stdout.contains("evidence.node_evidence_refs:"), "{stdout}");
    assert!(stdout.contains("evidence.type_stack_weights:"), "{stdout}");
}

#[test]
fn debug_evidence_vm_plan_prints_handler_passing_plan() {
    let entry = write_entry(
        "debug-evidence-vm-plan",
        "act out:\n  our say: int -> unit\n\n\
         catch ((\\_ -> out::say(1)) ()):\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("evidence vm plan:"), "{stdout}");
    assert!(stdout.contains("handlers:"), "{stdout}");
    assert!(stdout.contains("operations:"), "{stdout}");
    assert!(
        stdout.contains("evidence_param_functions:"),
        "evidence parameters should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence_env_values:"),
        "value evidence environments should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence_slot_keys:"),
        "evidence slot keys should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence_object_slots:"),
        "evidence object slot summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("function_objects:") && stdout.contains("value_objects:"),
        "function and value object summaries should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("call_objects:"),
        "call object summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("provider_slots:") && stdout.contains("provider_candidates:"),
        "provider summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("env_provider_slots:") && stdout.contains("env_provider_candidates:"),
        "value environment provider summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("known_handler_objects:") && stdout.contains("compiler_state_certificates"),
        "known handler plan summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("known_operation_calls:") && stdout.contains("known_operation_rejects:"),
        "known operation call classification summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence object graph:"),
        "evidence object graph should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("function-objects:"),
        "function evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("value-objects:"),
        "value evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("env_providers [s") && stdout.contains("=[h"),
        "value evidence provider environments should carry handler object candidates:\n{stdout}"
    );
    assert!(
        stdout.contains("handler-objects:"),
        "handler evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("operation-objects:"),
        "operation evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("provider-index:") && stdout.contains("needs-evidence-env"),
        "provider candidates should be visible without forcing direct lowering:\n{stdout}"
    );
    assert!(
        stdout.contains("class tail-resumptive"),
        "handler arm classification should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("signature params [") && stdout.contains("signature captures ["),
        "function and value evidence signatures should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("values:") && stdout.contains("lambda body"),
        "lambda evidence captures should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("lexical-handler-candidate")
            || stdout.contains("generic-fallback")
            || stdout.contains("direct-handler"),
        "operation lowering should be explicit:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_marks_local_var_known_state_handler() {
    let entry = write_entry(
        "debug-evidence-vm-plan-local-var-known-state",
        concat!("my f =\n", "  my $x = 1\n", "  $x\n", "f\n",),
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("known_handler_objects: 1 state 1 compiler_state_certificates 1"),
        "compiler-generated local var should produce one known state handler:\n{stdout}"
    );
    assert!(
        stdout.contains("known-handlers:")
            && stdout.contains("state d")
            && stdout.contains("source compiler-local-var"),
        "known state handler details should be visible:\n{stdout}"
    );
    assert!(
        stdout.contains("continuation snapshot-fork"),
        "known state handler should carry snapshot/fork continuation semantics:\n{stdout}"
    );
    assert!(
        stdout.contains(
            "known_operation_calls: 3 state_get_candidates 2 state_set_candidates 1 direct_gets 2 direct_sets 1 route_proofs 3"
        ),
        "compiler local var should produce known state get/set call candidates:\n{stdout}"
    );
    assert!(
        stdout.contains("known-operation-calls:")
            && stdout.contains("state-get")
            && stdout.contains("proof p")
            && stdout.contains("direct_ready=true reject -")
            && stdout.contains("state-set")
            && !stdout.contains("reject direct-execution-disabled"),
        "known state operation call route proofs should enable direct get/set:\n{stdout}"
    );
    assert!(
        stdout.contains("known-state-operation-route-proofs:")
            && stdout.contains("source compiler-local-var")
            && stdout.contains("visibility clean-known-state-catch")
            && stdout.contains("payload unit-payload-for-get"),
        "plan-only known state operation route proofs should be printed:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_does_not_mark_user_state_like_handler_without_certificate() {
    let entry = write_entry(
        "debug-evidence-vm-plan-user-state-like-not-known",
        concat!(
            "act state 't:\n",
            "  pub get: () -> 't\n",
            "  pub set: 't -> ()\n",
            "my run(v: int, x: [_] int): int = catch x:\n",
            "  state::get(), k -> run v: k v\n",
            "  state::set v, k -> run v: k()\n",
            "my f = run 1: state::get()\n",
            "f\n",
        ),
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("known_handler_objects: 0 state 0 compiler_state_certificates 0"),
        "state-like source handler should not be marked without compiler certificate:\n{stdout}"
    );
    assert!(
        !stdout.contains("known-handlers:"),
        "uncertified user handler should not produce known handler details:\n{stdout}"
    );
    assert!(
        stdout.contains("known_operation_calls: 0 state_get_candidates 0 state_set_candidates 0"),
        "uncertified user handler should not produce known operation candidates:\n{stdout}"
    );
    assert!(
        !stdout.contains("known-operation-calls:"),
        "uncertified user handler should not produce known operation details:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_records_handler_definition_env() {
    let entry = write_entry(
        "debug-evidence-vm-handler-definition-env",
        "act out:\n  our say: int -> unit\n\n\
         catch (catch out::say(1):\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n\
         ):\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("handler-objects:"),
        "handler evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("def_env [h0]"),
        "nested handler objects should record outer definition handler ids:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_visits_method_select_handler_body() {
    let entry = write_entry(
        "debug-evidence-vm-plan-method-select-handler",
        "use std::control::nondet::*\n\n\
         {\n\
         \x20 my xs = (each 1..2).list\n\
         \x20 ()\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("std::control::nondet::nondet::branch resumptive class may-escape-yield"),
        "method-select handler bodies should classify delayed continuation use as escaping:\n{stdout}"
    );
    assert!(
        stdout.contains("std::control::nondet::nondet::reject resumptive class abortive"),
        "method-select handler bodies should contribute abortive operation evidence:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_classifies_direct_multi_shot_resume() {
    let entry = write_entry(
        "debug-evidence-vm-plan-multi-shot-resume",
        "act flip:\n  our coin: () -> bool\n\n\
         catch flip::coin():\n\
         \x20 flip::coin(), k -> {\n\
         \x20\x20 k(true)\n\
         \x20\x20 k(false)\n\
         \x20 }\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("flip::coin resumptive class multi-shot-yield"),
        "directly invoking a continuation twice should be classified as multi-shot:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_matches_control_vm_on_pure_lambda_subset() {
    let entry = write_entry("debug-runtime-evidence-run", "my id x = x\nid 3\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("runtime evidence run:"), "{stdout}");
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("evidence.tasks: 2"), "{stdout}");
    assert!(stdout.contains("run roots [3]\n"), "{stdout}");
}

#[test]
fn debug_evidence_vm_run_alias_matches_control_vm_on_pure_lambda_subset() {
    let entry = write_entry("debug-evidence-vm-run", "my id x = x\nid 3\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("runtime evidence run:"), "{stdout}");
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [3]\n"), "{stdout}");
}

#[test]
fn debug_evidence_vm_run_passes_call_evidence_to_returned_effect_thunks() {
    let entry = write_entry(
        "debug-evidence-vm-run-call-evidence",
        "use std::control::nondet::*\n\n(each 1..2).list\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    let route_hits = stdout
        .lines()
        .find_map(|line| {
            line.trim()
                .strip_prefix("runtime_evidence.provider_env_route_hits: ")
                .and_then(|value| value.parse::<usize>().ok())
        })
        .unwrap_or(0);
    assert!(
        route_hits > 0,
        "call evidence should reach effect thunks returned by the callee:\n{stdout}"
    );
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [[1, 2]]\n"), "{stdout}");
}

#[test]
fn debug_evidence_vm_run_captures_provider_env_on_closure_value() {
    let entry = write_entry(
        "debug-evidence-vm-run-provider-env",
        "act out:\n  our say: int -> unit\n\n\
         catch ((\\_ -> out::say(1)) ()):\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("evidence.plan_env_provider_slots: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_env_provider_candidates: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.provider_env_values: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.provider_env_reads: 1"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [()]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_matches_control_vm_on_std_int_primitives() {
    let entry = write_entry(
        "debug-runtime-evidence-run-std-int",
        "1 + 2\nmy add1 x = x + 1\nadd1 3\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("evidence.tasks:"), "{stdout}");
    assert!(stdout.contains("run roots [3, 4]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_reads_struct_record_payload_fields() {
    let entry = write_entry(
        "debug-runtime-evidence-run-struct-field",
        "struct point { x: int, y: int } with:\n\
         \x20 our p.norm2 = p.x * p.x + p.y * p.y\n\n\
         point { x: 3, y: 4 } .norm2\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [25]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_matches_control_vm_on_record_pattern_defaults() {
    let entry = write_entry(
        "debug-runtime-evidence-run-record-pattern-defaults",
        "my area({width = 1, height = 2}) = width * height\n\
         area { width: 3 }\n\
         area {}\n\
         area { width: 3, height: 4 }\n\
         my next_area({width = 2, height = width + 1}) = width * height\n\
         next_area { width: 3 }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [6, 2, 12, 12]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_applies_function_adapter_for_each() {
    let entry = write_entry(
        "debug-runtime-evidence-run-each-list",
        "use std::control::nondet::*\n\n(each 1..3).list\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [[1, 2, 3]]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_inlines_pure_for_adapter_thunks() {
    let entry = write_entry(
        "debug-runtime-evidence-run-pure-for-adapter-inline",
        "{\n\
         \x20 for x in 1..3:\n\
         \x20\x20 x + 1\n\
         \x20 ()\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [()]\n"), "{stdout}");
    assert!(
        stdout.contains("runtime_evidence.apply_adapter_inline_attempts: 6"),
        "pure for callbacks should try the adapter inline route:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.apply_adapter_inline_hits: 6"),
        "pure for callbacks should finish adapter application without continuation frames:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.apply_adapter_inline_effect_fallbacks: 0"),
        "pure for callbacks should not need the effect fallback in the adapter inline route:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.adapt_value_inline_thunk_wraps: 6"),
        "pure for callback returns should wrap values into thunk values directly:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.catch_body_env_clone_elided: 20"),
        "pure for loop-control catches should reuse env when the body cannot extend it:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.catch_body_env_clone_kept: 0"),
        "pure for loop-control catches should not clone env for preserving bodies:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.continuation_resume_adapter_steps: 0"),
        "pure for callbacks should not resume adapter continuation frames:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_evaluates_list_view_raw() {
    let entry = write_entry(
        "debug-runtime-evidence-run-list-view-raw",
        "use std::data::list::*\n\n[1, 2, 3].rev\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [[3, 2, 1]]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_matches_control_vm_on_text_and_bytes_primitives() {
    let entry = write_entry(
        "debug-runtime-evidence-run-text-bytes",
        "std::text::str::index_raw \"aβc\" 1\n\
         std::text::str::index_range_raw \"aβc\" 1 3\n\
         std::text::str::splice_raw \"abcd\" 1 3 \"XY\"\n\
         std::text::str::line_count \"a\\nb\"\n\
         std::text::str::index_range \"abcdef\" (std::data::range::range 1 4)\n\
         std::data::list::index_range [1, 2, 3, 4] (std::data::range::range 1 3)\n\
         std::data::list::splice_raw [1, 2, 3, 4] 1 3 [9]\n\
         std::text::bytes::len(std::text::str::to_bytes \"abc\")\n\
         std::text::bytes::index_raw(std::text::str::to_bytes \"abc\", 1)\n\
         std::text::bytes::to_utf8_raw(std::text::str::to_bytes \"abc\")\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains(
            "run roots [\"β\", \"βc\", \"aXYd\", 2, \"bcd\", [2, 3], [1, 9, 4], 3, 98, (\"abc\", 3)]\n"
        ),
        "{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_carries_function_adapter_hygiene_markers() {
    let entry = write_entry(
        "debug-runtime-evidence-run-function-adapter-hygiene",
        "pub act sub 'a:\n\
         \x20 pub return: 'a -> never\n\
         \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
         \x20\x20 return a, _ -> a\n\
         \x20\x20 a -> a\n\n\
         pub act note:\n\
         \x20 pub tell: () -> ()\n\n\
         our use_int = sub::sub:\n\
         \x20 sub::return 0\n\n\
         our use_str = sub::sub:\n\
         \x20 sub::return \"done\"\n\n\
         our use_residual() = sub::sub:\n\
         \x20 note::tell()\n\
         \x20 1\n\n\
         (use_int, use_str, use_residual)\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("run roots [(0, \"done\", <closure>)]\n"),
        "{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_resumes_carried_callback_markers() {
    let entry = write_entry(
        "debug-runtime-evidence-run-repeated-callback-hygiene",
        "pub act tick:\n\
         \x20 pub ping: () -> ()\n\n\
         pub strip_tick(action: [tick] _) = catch action:\n\
         \x20 tick::ping(), k -> strip_tick(k ())\n\
         \x20 v -> v\n\n\
         pub count_tick(action: [tick] _) = catch action:\n\
         \x20 tick::ping(), k -> 1 + count_tick(k ())\n\
         \x20 _ -> 0\n\n\
         pub bounce(n: int, f, x) =\n\
         \x20 if n == 0:\n\
         \x20\x20 x\n\
         \x20 else:\n\
         \x20\x20 strip_tick: f (f (bounce(n - 1, f, x)))\n\n\
         count_tick:\n\
         \x20 bounce(3, \\x -> {\n\
         \x20\x20 tick::ping()\n\
         \x20\x20 x + 1\n\
         \x20 }, 0)\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [6]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_for_last_and_nullary_constructors() {
    let entry = write_entry(
        "debug-runtime-evidence-run-for-last",
        "{\n\
         \x20 for x in 0..:\n\
         \x20\x20 if x == 5: last\n\
         \x20 5\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [5]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_formats_labeled_nullary_constructor_results() {
    let entry = write_entry(
        "debug-runtime-evidence-run-once",
        "use std::control::nondet::*\n\n\
         once:\n\
         \x20 my a = each 1..\n\
         \x20 my b = each a<..\n\
         \x20 my c = each b<..\n\
         \x20 guard: a * a + b * b == c * c\n\
         \x20 (a, b, c)\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("run roots [opt::just((3, 4, 5))]\n"),
        "{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_handles_ref_set() {
    let entry = write_entry(
        "debug-runtime-evidence-run-ref-set",
        "{\n\
         \x20 my $x = 10\n\
         \x20 my $y = 20\n\
         \x20 &x = $x + 1\n\
         \x20 &y = $y + 1\n\
         \x20 ($x, $y)\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [(11, 21)]\n"), "{stdout}");
    assert!(
        stdout.contains("runtime_evidence.known_state_direct_gets: 3"),
        "compiler local refs should use direct state get handling:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_direct_sets: 1"),
        "compiler local refs should use direct state set handling:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_entries: 1"),
        "known state catch should push a runtime state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_exits: 1"),
        "known state catch should pop the runtime state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_reads_late: 0"),
        "request-free known state gets should bypass late request reads:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_writes_late: 0"),
        "request-free known state sets should bypass late request writes:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_missing_late: 0"),
        "known state frame lookup should not miss in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_shadow_compat_fallbacks: 0"),
        "local ref canary should not need env shadow compatibility fallback:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_snapshots: 0"),
        "straight-line local ref handling should not snapshot state frames:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_forks: 0"),
        "straight-line local ref handling should not fork state frames:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_get_candidates: 2"),
        "known operation plan should classify the two static get call sites:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_set_candidates: 1"),
        "known operation plan should classify the static set call site:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_state_operation_route_proofs: 3"),
        "known operation plan should build plan-only route proofs for local refs:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_direct_gets: 2"),
        "D3 should enable direct get for the two static local ref get sites:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_direct_sets: 1"),
        "D4 should enable direct set for the static local ref set site:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_reject_direct_execution_disabled: 0"),
        "D4 should not leave route-proven local refs on the disabled direct path:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_candidate_hits: 3"),
        "known operation runtime hits should count forced get requests:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_candidate_hits: 1"),
        "known operation runtime hits should count forced set requests:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_active_frame_hits: 3"),
        "known get operations should see the active state frame at force time:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_active_frame_hits: 1"),
        "known set operations should see the active state frame at force time:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_active_frame_misses: 0"),
        "known get operations should not miss the active state frame in this canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_active_frame_misses: 0"),
        "known set operations should not miss the active state frame in this canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_hits: 4"),
        "route proof shadow guard should hit for every dynamic local ref operation:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_get_hits: 3"),
        "route proof shadow guard should count dynamic local ref gets:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_set_hits: 1"),
        "route proof shadow guard should count dynamic local ref sets:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_missing_proof: 0"),
        "route proof shadow guard should not miss proofs in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_missing_frame: 0"),
        "route proof shadow guard should see the active state frame in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_role_mismatch: 0"),
        "route proof shadow guard should not see role mismatches in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_attempts: 3"),
        "route proof direct get guard should run for every dynamic local ref get:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_hits: 3"),
        "route proof direct get guard should bypass requests for local ref gets:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_missing_proof: 0"),
        "route proof direct get guard should not miss proofs in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_missing_frame: 0"),
        "route proof direct get guard should see the active state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_role_mismatch: 0"),
        "route proof direct get guard should not see role mismatches:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_payload_mismatch: 0"),
        "route proof direct get guard should only see unit get payloads:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_attempts: 1"),
        "route proof direct set guard should run for every dynamic local ref set:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_hits: 1"),
        "route proof direct set guard should bypass requests for local ref sets:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_missing_proof: 0"),
        "route proof direct set guard should not miss proofs in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_missing_frame: 0"),
        "route proof direct set guard should see the active state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_role_mismatch: 0"),
        "route proof direct set guard should not see role mismatches:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_payload_mismatch: 0"),
        "route proof direct set guard should see a single-value set payload proof:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_known_state_frame_matches_control_across_nondet_resume() {
    let entry = write_entry(
        "debug-runtime-evidence-run-known-state-frame-nondet",
        "use std::control::nondet::*\n\n\
         {\n\
         \x20 my $x = 0\n\
         \x20 my ys = {\n\
         \x20\x20 my b = each [true, false]\n\
         \x20\x20 &x = $x + 1\n\
         \x20\x20 $x\n\
         \x20 }.list\n\
         \x20 (ys, $x)\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [([1, 2], 2)]\n"), "{stdout}");
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_entries: 1"),
        "known state frame should be active across the nondet body:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_exits: 1"),
        "known state frame should be popped after the enclosing state handler:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_reads_late: 0"),
        "request-free known state reads should bypass late request handling:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_writes_late: 0"),
        "request-free known state writes should update the runtime state frame directly:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_missing_late: 0"),
        "nondet resume should not lose the active state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_snapshots: 0"),
        "state outside nondet/list should stay shared rather than snapshotted:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_forks: 0"),
        "state outside nondet/list should not be forked by nondet resume:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_active_frame_hits: 7"),
        "known get operations should see the active state frame across nondet resume:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_active_frame_hits: 2"),
        "known set operations should see the active state frame across nondet resume:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_hits: 7"),
        "known get operations should use route-proof direct reads across nondet resume:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_hits: 2"),
        "known set operations should use route-proof direct writes across nondet resume:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_handles_console_stdout_host_effect() {
    let entry = write_entry(
        "debug-runtime-evidence-run-console-stdout",
        "say \"Hello, World\"\n\
         say: 1 + 2\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("Hello, World\n3\nrun roots [(), ()]\n"),
        "{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_uses_direct_handler_evidence() {
    let entry = write_entry(
        "debug-runtime-evidence-run-direct-handler",
        "act flip:\n  our coin: () -> bool\n\n\
         catch flip::coin():\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("control_evidence.effect_calls: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("control_evidence.direct_effect_calls: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_provider_slots: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_provider_candidates: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_candidates: 2"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_effect_routes: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_effect_routes: 1"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [true]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_classifies_unused_continuation_as_direct_abortive() {
    let entry = write_entry(
        "debug-runtime-evidence-run-direct-abortive-handler",
        "act stop:\n  our now: () -> int\n\n\
         catch (stop::now(), 1):\n\
         \x20 stop::now(), _ -> (42, 0)\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("evidence.plan_direct_effect_routes: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_abortive_effect_routes: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_tail_resumptive_effect_routes: 0"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.thunk_force_continuation: 0"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.continuation_appends: 0"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.request_continuation_steps: 0"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [(42, 0)]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_falls_through_handler_arm_patterns_and_guards() {
    let entry = write_entry(
        "debug-runtime-evidence-run-handler-arm-fallthrough",
        "act log:\n  our put: int -> int\n\n\
         catch log::put 1:\n\
         \x20 log::put 0, k -> k 10\n\
         \x20 log::put _, k if false -> k 20\n\
         \x20 log::put _, k -> k 30\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [30]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_falls_through_value_arm_patterns_and_guards() {
    let entry = write_entry(
        "debug-runtime-evidence-run-value-arm-fallthrough",
        "catch 1:\n\
         \x20 0 -> 10\n\
         \x20 _ if false -> 20\n\
         \x20 _ -> 30\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [30]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_falls_through_case_patterns_and_guards() {
    let entry = write_entry(
        "debug-runtime-evidence-run-case-fallthrough",
        "case 1:\n\
         \x20 0 -> 10\n\
         \x20 _ if false -> 20\n\
         \x20 _ -> 30\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [30]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_annotated_handler_function_with_state() {
    let entry = write_entry(
        "debug-runtime-evidence-run-handler-function-state",
        "act log:\n\
         \x20 pub put: str -> ()\n\n\
         my collect_count(comp: [log] 'a): int =\n\
         \x20 my $count = 0\n\
         \x20 catch comp:\n\
         \x20\x20 log::put _, k ->\n\
         \x20\x20\x20 &count = $count + 1\n\
         \x20\x20\x20 k ()\n\
         \x20\x20 v -> v\n\
         \x20 $count\n\n\
         collect_count: log::put \"a\"\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [1]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_resumes_direct_effect_in_apply_argument() {
    let entry = write_entry(
        "debug-runtime-evidence-run-apply-argument-effect",
        "act flip:\n  our coin: () -> bool\n\n\
         my id x = x\n\n\
         catch id flip::coin():\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("control_evidence.direct_effect_calls: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_tail_resumptive_effect_routes: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.request_continuation_steps: 0"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [true]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_resumes_direct_effect_in_tuple_item() {
    let entry = write_entry(
        "debug-runtime-evidence-run-tuple-item-effect",
        "act flip:\n  our coin: () -> bool\n\n\
         catch (1, flip::coin()):\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [(1, true)]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_resumes_direct_effect_in_record_field() {
    let entry = write_entry(
        "debug-runtime-evidence-run-record-field-effect",
        "act flip:\n  our coin: () -> bool\n\n\
         catch ({a: flip::coin()}):\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [{a: true}]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_leaves_value_arm_thunk_unforced() {
    let entry = write_entry(
        "debug-runtime-evidence-run-value-arm-thunk",
        "act flip:\n  our coin: () -> bool\n\n\
         catch ({a: true}).a:\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [<thunk>]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_recursive_all_paths_marker_route() {
    let entry = write_entry(
        "debug-runtime-evidence-run-all-paths",
        "act flip:\n  our coin: () -> bool\n\n\
         our all_paths(action: [flip] _) = catch action:\n\
         \x20 flip::coin(), k -> all_paths(k true) + all_paths(k false)\n\
         \x20 v -> [v]\n\n\
         all_paths:\n\
         \x20 if flip::coin(): 1 else: 0\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("control_evidence.direct_effect_calls: 0"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [[1, 0]]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_resumes_through_primitive_apply() {
    let entry = write_entry(
        "debug-runtime-evidence-run-amount-primitive-apply",
        "act amount:\n  our coin: () -> int\n\n\
         our one(action: [amount] _) = catch action:\n\
         \x20 amount::coin(), k -> k 1\n\
         \x20 v -> v\n\n\
         one:\n\
         \x20 amount::coin() * 10\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [10]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_recursive_amount_handler() {
    let entry = write_entry(
        "debug-runtime-evidence-run-recursive-amount",
        "act amount:\n  our coin: () -> int\n\n\
         our total_amount(action: [amount] _) =\n\
         \x20 my loop(n, action: [amount] _) = catch action:\n\
         \x20\x20 amount::coin(), k -> loop(n, k n)\n\
         \x20\x20 v -> v\n\
         \x20 [loop(1, action), loop(2, action)]\n\n\
         total_amount:\n\
         \x20 amount::coin() * 10\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [[10, 20]]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_nested_flip_amount_handlers() {
    let entry = write_entry(
        "debug-runtime-evidence-run-nested-flip-amount",
        "act flip:\n\
         \x20 our coin: () -> bool\n\
         act amount:\n\
         \x20 our coin: () -> int\n\n\
         our all_paths(action: [flip] _) = catch action:\n\
         \x20 flip::coin(), k -> all_paths(k true) + all_paths(k false)\n\
         \x20 v -> [v]\n\n\
         our total_amount(action: [amount] _) =\n\
         \x20 my loop(n, action: [amount] _) = catch action:\n\
         \x20\x20 amount::coin(), k -> loop(n, k n)\n\
         \x20\x20 v -> v\n\
         \x20 [loop(1, action), loop(2, action)]\n\n\
         total_amount: all_paths:\n\
         \x20 my a = if flip::coin(): amount::coin() else: 0\n\
         \x20 my b = if flip::coin(): amount::coin() * 10 else: 0\n\
         \x20 my c = if flip::coin(): amount::coin() * 100 else: 0\n\
         \x20 a + b + c\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains(
            "run roots [[[111, 11, 101, 1, 110, 10, 100, 0], \
             [222, 22, 202, 2, 220, 20, 200, 0]]]\n"
        ),
        "{stdout}"
    );
}

#[test]
fn compatible_dump_no_prelude_uses_cache() {
    let entry = write_entry("dump-no-prelude-cache", "1\n");
    let root = entry.parent().unwrap().to_path_buf();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("dump")
        .arg("--poly")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert!(stdout(&output).contains("roots"), "{}", stdout(&output));
    assert_eq!(control_cache_file_count(&cache_root), 0);
    assert_eq!(poly_cache_file_count(&cache_root), 1);
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 1);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_parse_expr_prints_event_tree() {
    let entry = write_entry("parse-expr", "1 + 2\n");

    let output = yulang_command()
        .arg("parse")
        .arg(&entry)
        .arg("--as")
        .arg("expr")
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("Expr\n"), "{stdout}");
    assert!(stdout.contains("Number \"1\""), "{stdout}");
    assert!(stdout.contains("Infix \"+\""), "{stdout}");
}

#[test]
fn install_std_writes_explicit_std_root() {
    let root = temp_root("install-std");
    let std_root = root.join("custom-std");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("install")
        .arg("std")
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "");
    assert_eq!(stderr(&output), format!("{}\n", std_root.display()));
    assert!(std_root.join("std.yu").is_file());
    assert!(std_root.join("std").join("prelude.yu").is_file());
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn cache_path_and_clear_use_yulang_cache_dir() {
    let root = temp_root("cache");
    let cache_root = root.join("cache-root");
    fs::create_dir_all(&cache_root).unwrap();
    fs::write(cache_root.join("entry"), "cached").unwrap();
    fs::create_dir_all(cache_root.join("artifacts").join("control-vm")).unwrap();
    fs::create_dir_all(cache_root.join("artifacts").join("poly")).unwrap();
    fs::create_dir_all(cache_root.join("artifacts").join("compiled-unit")).unwrap();
    fs::write(
        cache_root
            .join("artifacts")
            .join("control-vm")
            .join("one.yuvm"),
        "",
    )
    .unwrap();
    fs::write(
        cache_root.join("artifacts").join("poly").join("one.yuir"),
        "",
    )
    .unwrap();
    fs::write(
        cache_root.join("artifacts").join("poly").join("two.yuir"),
        "",
    )
    .unwrap();

    let path_output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("cache")
        .arg("path")
        .output()
        .unwrap();
    assert_success(&path_output);
    assert_eq!(stdout(&path_output), format!("{}\n", cache_root.display()));

    let stats_output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("cache")
        .arg("stats")
        .output()
        .unwrap();
    assert_success(&stats_output);
    assert_eq!(
        stdout(&stats_output),
        format!(
            "cache: {}\ncontrol-vm: 1\nmono: 0\npoly: 2\ncompiled-unit: 0\nrealm-resolution: 0\n",
            cache_root.display()
        )
    );

    let clear_output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("cache")
        .arg("clear")
        .output()
        .unwrap();
    assert_success(&clear_output);
    assert_eq!(
        stdout(&clear_output),
        format!("cleared {}\n", cache_root.display())
    );
    assert!(!cache_root.exists());
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_dump_mono_writes_exact_mono_cache_artifact() {
    let root = temp_root("dump-mono-cache");
    let _ = fs::remove_dir_all(&root);
    let entry = root.join("main.yu");
    fs::create_dir_all(&root).unwrap();
    fs::write(&entry, "my id x = x\nid 1\n").unwrap();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("dump-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(mono_cache_file_count(&cache_root), 1);
    assert_eq!(control_cache_file_count(&cache_root), 0);
    assert_eq!(poly_cache_file_count(&cache_root), 1);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_build_populates_control_vm_cache_unless_disabled() {
    let entry = write_entry("build-control-cache", "1\n");
    let root = entry.parent().unwrap().to_path_buf();
    let cache_root = root.join("cache-root");
    let artifact = root.join("main.yuir");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("build")
        .arg("--out")
        .arg(&artifact)
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), format!("build: {}\n", artifact.display()));
    assert_eq!(control_cache_file_count(&cache_root), 1);
    assert_eq!(poly_cache_file_count(&cache_root), 1);

    let disabled_cache_root = root.join("disabled-cache");
    let disabled_artifact = root.join("disabled.yuir");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &disabled_cache_root)
        .arg("--no-cache")
        .arg("--no-prelude")
        .arg("build")
        .arg("--out")
        .arg(&disabled_artifact)
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(control_cache_file_count(&disabled_cache_root), 0);
    assert_eq!(poly_cache_file_count(&disabled_cache_root), 0);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_populates_control_vm_cache() {
    let entry = write_entry("run-control-cache", "1\n");
    let root = entry.parent().unwrap().to_path_buf();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_eq!(control_cache_file_count(&cache_root), 1);
    assert_eq!(poly_cache_file_count(&cache_root), 1);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_runtime_phase_timings_report_cache_route() {
    let entry = write_entry("runtime-phase-cache-route", "1\n");
    let root = entry.parent().unwrap().to_path_buf();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route(&output, "full-miss");
    assert_run_backend(&output, "evidence-vm");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route_any(&output, &["source-key-control-hit", "control-hit"]);
    assert_run_backend(&output, "evidence-vm");

    remove_cache_stage(&cache_root, "control-vm");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route(&output, "poly-hit");
    assert_run_backend(&output, "evidence-vm");

    remove_cache_stage(&cache_root, "control-vm");
    remove_cache_stage(&cache_root, "poly");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route(&output, "compiled-unit-hit");
    assert_run_backend(&output, "evidence-vm");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_reuses_std_compiled_unit_prefix_for_new_entry() {
    let root = temp_root("run-std-prefix-cache");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let std_root = write_minimal_std(&root);
    let cache_root = root.join("cache-root");
    let first = root.join("first.yu");
    let second = root.join("second.yu");
    fs::write(&first, "1\n").unwrap();
    fs::write(&second, "2\n").unwrap();

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(&std_root)
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&first)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route(&output, "std-prefix-build");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 2);

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(&std_root)
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&second)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [2]\n");
    assert_cache_route(&output, "std-prefix-hit");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 3);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_uses_single_source_unit_prefix_cache() {
    let root = temp_root("run-source-unit-prefix-cache");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("a")).unwrap();
    let entry = root.join("main.yu");
    fs::write(&entry, "mod a;\nuse a::*\nx\n").unwrap();
    fs::write(root.join("a.yu"), "mod b;\npub x = b::y\n").unwrap();
    fs::write(root.join("a").join("b.yu"), "pub y = 7\n").unwrap();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [7]\n");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 3);
    assert_eq!(poly_cache_file_count(&cache_root), 1);
    assert_eq!(control_cache_file_count(&cache_root), 1);

    fs::write(&entry, "mod a;\nuse a::*\nmy keep v = v\nkeep x\n").unwrap();
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [7]\n");
    assert!(stderr(&output).contains("run.cache: source-unit-prefix-hit"));
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 4);
    assert_eq!(poly_cache_file_count(&cache_root), 2);
    assert_eq!(control_cache_file_count(&cache_root), 2);

    remove_cache_stage(&cache_root, "control-vm");
    remove_cache_stage(&cache_root, "poly");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [7]\n");
    assert_cache_route(&output, "compiled-unit-hit");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 4);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_uses_source_unit_prefix_for_editable_realm_band_imports() {
    let root = temp_root("run-editable-realm-band-source-unit-prefix-cache");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("helper")).unwrap();
    fs::write(
        root.join("realm.toml"),
        r#"[realm]
identity = "test/editable-realm-band"
"#,
    )
    .unwrap();
    let entry = root.join("main.yu");
    fs::write(
        &entry,
        "use realm/helper::answer\nuse realm/view::describe\ndescribe answer\n",
    )
    .unwrap();
    fs::write(
        root.join("helper.yu"),
        "mod inner;\nuse band::inner::value as inner_value\npub answer = inner_value\n",
    )
    .unwrap();
    fs::write(root.join("helper").join("inner.yu"), "our value = 42\n").unwrap();
    fs::write(root.join("view.yu"), "pub describe value = value\n").unwrap();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [42]\n");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 4);
    assert_eq!(poly_cache_file_count(&cache_root), 1);
    assert_eq!(control_cache_file_count(&cache_root), 1);

    fs::write(
        &entry,
        "use realm/helper::answer\nuse realm/view::describe\nmy keep value = value\nkeep (describe answer)\n",
    )
    .unwrap();
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [42]\n");
    assert_cache_route_any(
        &output,
        &["source-unit-prefix-hit", "merged-source-unit-prefix-hit"],
    );
    assert_eq!(poly_cache_file_count(&cache_root), 2);
    assert_eq!(control_cache_file_count(&cache_root), 2);

    remove_cache_stage(&cache_root, "control-vm");
    remove_cache_stage(&cache_root, "poly");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [42]\n");
    assert_cache_route(&output, "compiled-unit-hit");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_reports_dependency_lowering_errors_before_runtime() {
    let root = temp_root("run-dependency-lowering-error-before-runtime");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("helper")).unwrap();
    let entry = root.join("main.yu");
    fs::write(&entry, "use realm/helper::answer\nanswer\n").unwrap();
    fs::write(
        root.join("helper.yu"),
        "mod inner;\nuse band::inner::bonus\npub answer = 40 + bonus\n",
    )
    .unwrap();
    fs::write(root.join("helper").join("inner.yu"), "our bonus = 2\n").unwrap();

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains("cannot build executable program with lowering errors"),
        "{stderr}"
    );
    assert!(
        stderr.contains("unresolved value name: #op:infix:+"),
        "{stderr}"
    );
    assert!(!stderr.contains("unbound local"), "{stderr}");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_uses_merged_source_unit_prefix_when_many_are_cached() {
    let root = temp_root("run-many-source-unit-prefix-cache");
    let _ = fs::remove_dir_all(&root);
    let entry = root.join("main.yu");
    fs::create_dir_all(&root).unwrap();
    fs::write(&entry, "mod a;\nmod b;\n(a::x, b::y)\n").unwrap();
    fs::write(root.join("a.yu"), "pub x = 10\n").unwrap();
    fs::write(root.join("b.yu"), "pub y = 2\n").unwrap();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [(10, 2)]\n");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 3);
    assert_eq!(poly_cache_file_count(&cache_root), 1);
    assert_eq!(control_cache_file_count(&cache_root), 1);

    fs::write(&entry, "mod a;\nmod b;\nmy keep v = v\nkeep (a::x, b::y)\n").unwrap();
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [(10, 2)]\n");
    assert_cache_route(&output, "merged-source-unit-prefix-hit");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 5);
    assert_eq!(poly_cache_file_count(&cache_root), 2);
    assert_eq!(control_cache_file_count(&cache_root), 2);

    remove_cache_stage(&cache_root, "control-vm");
    remove_cache_stage(&cache_root, "poly");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [(10, 2)]\n");
    assert_cache_route(&output, "compiled-unit-hit");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 5);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn public_regression_list_update_runs_through_cli_cache() {
    let root = temp_root("public-regression-list-update");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let cache_root = root.join("cache-root");
    let entry = repo_yulang_fixture("regressions/runtime/list_update.yu");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [[2, 6, 4]]\n");
    assert_eq!(control_cache_file_count(&cache_root), 1);
    assert_eq!(poly_cache_file_count(&cache_root), 1);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn public_regression_runtime_fixtures_run_through_cli_golden() {
    let cases = [
        (
            "nondet-once-triple",
            "regressions/runtime/nondet_once_triple.yu",
            "run roots [opt::just((3, 4, 5))]\n",
        ),
        (
            "optional-record-defaults",
            "regressions/runtime/optional_record_defaults.yu",
            "run roots [6, 2, 12, 12]\n",
        ),
        (
            "attached-impl-pick",
            "regressions/runtime/attached_impl_pick.yu",
            "run roots [(10, false)]\n",
        ),
    ];

    for (slug, fixture, expected_stdout) in cases {
        let root = temp_root(&format!("public-regression-{slug}"));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        let cache_root = root.join("cache-root");
        let entry = repo_yulang_fixture(fixture);

        let output = yulang_command()
            .env("YULANG_CACHE_DIR", &cache_root)
            .arg("--std-root")
            .arg(repo_lib_root())
            .arg("run")
            .arg("--print-roots")
            .arg(&entry)
            .output()
            .unwrap();

        assert_success(&output);
        assert_eq!(stdout(&output), expected_stdout, "{slug}");
        assert_eq!(control_cache_file_count(&cache_root), 1, "{slug}");
        assert_eq!(poly_cache_file_count(&cache_root), 1, "{slug}");

        let _ = fs::remove_dir_all(&root);
    }
}

#[test]
fn public_examples_smoke_bridge_runs_representative_cli_golden() {
    let cases = [
        (
            "struct-method",
            "examples/01_struct_with.yu",
            "run roots [25]\n",
        ),
        ("refs", "examples/02_refs.yu", "run roots [(11, 21)]\n"),
        ("for-last", "examples/03_for_last.yu", "run roots [5]\n"),
        ("sub-return", "examples/04_sub_return.yu", "run roots [5]\n"),
        (
            "nondet-all",
            "examples/05_undet_all.yu",
            "run roots [[5, 6, 7, 6, 7, 8, 7, 8, 9]]\n",
        ),
        (
            "nondet-once",
            "examples/06_undet_once.yu",
            "run roots [opt::just((3, 4, 5))]\n",
        ),
        ("junction", "examples/07_junction.yu", "run roots [1]\n"),
        ("types", "examples/08_types.yu", "run roots [42]\n"),
        (
            "optional-record-args",
            "examples/09_optional_record_args.yu",
            "run roots [6, 2, 12, 12]\n",
        ),
        (
            "effect-handler",
            "examples/10_effect_handler.yu",
            "run roots [(9, \"3\\n6\\n\")]\n",
        ),
        (
            "attached-impl",
            "examples/11_attached_impl.yu",
            "run roots [(10, false)]\n",
        ),
        ("cast", "examples/12_cast.yu", "run roots []\n"),
    ];

    for (slug, example, expected_stdout) in cases {
        let root = temp_root(&format!("public-example-{slug}"));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        let cache_root = root.join("cache-root");
        let entry = repo_file(example);

        let output = yulang_command()
            .env("YULANG_CACHE_DIR", &cache_root)
            .arg("--std-root")
            .arg(repo_lib_root())
            .arg("run")
            .arg("--print-roots")
            .arg(&entry)
            .output()
            .unwrap();

        assert_success(&output);
        assert_eq!(stdout(&output), expected_stdout, "{slug}");

        let _ = fs::remove_dir_all(&root);
    }
}

#[test]
fn public_examples_smoke_bridge_keeps_console_stdout() {
    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("run")
        .arg(repo_file("examples/13_console.yu"))
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "Hello, World\n3\n");
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_regression_ref_update_loop_runs_on_cli_vm_stack() {
    let root = temp_root("public-regression-ref-update-loop");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let cache_root = root.join("cache-root");
    let entry = root.join("main.yu");
    fs::write(
        &entry,
        r#"{
    my $x = 0
    for i in 0..:
        if i == 100: last
        &x = $x + 1
    $x
}
"#,
    )
    .unwrap();

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [100]\n");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn realm_freeze_writes_versioned_snapshot() {
    let root = temp_root("realm-freeze");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("realm.toml"),
        r#"[realm]
identity = "app"
"#,
    )
    .unwrap();
    fs::write(root.join("main.yu"), "my main = 1\n").unwrap();

    let output = yulang_command()
        .arg("realm")
        .arg("freeze")
        .arg(&root)
        .arg("--version")
        .arg("1.0.0")
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("realm freeze: frozen "), "{stdout}");
    assert!(stdout.contains(" files=2\n"), "{stdout}");
    assert!(
        root.join(".yulang")
            .join("versions")
            .join("1.0.0")
            .join("snapshot.json")
            .is_file()
    );
    let frozen_manifest = fs::read_to_string(
        root.join(".yulang")
            .join("versions")
            .join("1.0.0")
            .join("realm.toml"),
    )
    .unwrap();
    assert!(!frozen_manifest.contains("version = "));
    assert!(!frozen_manifest.contains("[dependencies]"));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn realm_install_installs_local_snapshot_for_import() {
    let root = temp_root("realm-install");
    let _ = fs::remove_dir_all(&root);
    let lib_root = root.join("lib");
    let realm_root = root.join("theme");
    let app_root = root.join("app");
    fs::create_dir_all(&realm_root).unwrap();
    fs::create_dir_all(&app_root).unwrap();
    fs::write(
        realm_root.join("realm.toml"),
        r#"[realm]
name = "theme"
version = "1.0.0"
"#,
    )
    .unwrap();
    fs::write(realm_root.join("colors.yu"), "pub value = 7\n").unwrap();
    let main_path = app_root.join("main.yu");
    fs::write(&main_path, "use local/theme/colors::value v1.0.0\nvalue\n").unwrap();

    let install = yulang_command()
        .env("YULANG_LIB_DIR", &lib_root)
        .arg("realm")
        .arg("install")
        .arg(&realm_root)
        .output()
        .unwrap();

    assert_success(&install);
    let install_stdout = stdout(&install);
    assert!(
        install_stdout.contains("realm install: installed "),
        "{install_stdout}"
    );
    assert!(install_stdout.contains(" files=2\n"), "{install_stdout}");
    assert!(
        lib_root
            .join("realms")
            .join("local")
            .join("theme")
            .join("1.0.0")
            .join("snapshot.json")
            .is_file()
    );

    let run = yulang_command()
        .env("YULANG_LIB_DIR", &lib_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&main_path)
        .output()
        .unwrap();

    assert_success(&run);
    assert_eq!(stdout(&run), "run roots [7]\n");

    let _ = fs::remove_dir_all(&root);
}

fn yulang_command() -> Command {
    Command::new(env!("CARGO_BIN_EXE_yulang"))
}

fn yulang_command_with_stdin<const N: usize>(args: [&str; N], stdin: &str) -> Output {
    let mut child = yulang_command()
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn write_fixture(name: &str, source: &str) -> (PathBuf, PathBuf) {
    let root = temp_root(name);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let std_root = write_minimal_std(&root);
    let entry = root.join("main.yu");
    fs::write(&entry, source).unwrap();
    (entry, std_root)
}

fn write_entry(name: &str, source: &str) -> PathBuf {
    let root = temp_root(name);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let entry = root.join("main.yu");
    fs::write(&entry, source).unwrap();
    entry
}

fn write_minimal_std(root: &Path) -> PathBuf {
    let std_root = root.join("lib");
    fs::create_dir_all(std_root.join("std")).unwrap();
    fs::write(std_root.join("std.yu"), "mod prelude;\n").unwrap();
    fs::write(std_root.join("std").join("prelude.yu"), "").unwrap();
    std_root
}

fn repo_lib_root() -> PathBuf {
    repo_file("lib")
}

fn repo_yulang_fixture(path: &str) -> PathBuf {
    repo_file("tests").join("yulang").join(path)
}

fn repo_file(path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(path)
}

fn temp_root(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "yulang-cli-{name}-{}",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ))
}

fn control_cache_file_count(root: &Path) -> usize {
    artifact_cache_file_count(root, "control-vm")
}

fn poly_cache_file_count(root: &Path) -> usize {
    artifact_cache_file_count(root, "poly")
}

fn mono_cache_file_count(root: &Path) -> usize {
    artifact_cache_file_count(root, "mono")
}

fn compiled_unit_cache_file_count(root: &Path) -> usize {
    artifact_cache_file_count(root, "compiled-unit")
}

fn remove_cache_stage(root: &Path, stage: &str) {
    let _ = fs::remove_dir_all(root.join("artifacts").join(stage));
}

fn assert_cache_route(output: &Output, route: &str) {
    let stderr = stderr(output);
    assert!(stderr.contains(&format!("run.cache: {route}")), "{stderr}");
}

fn assert_cache_route_any(output: &Output, routes: &[&str]) {
    let stderr = stderr(output);
    assert!(
        routes
            .iter()
            .any(|route| stderr.contains(&format!("run.cache: {route}"))),
        "{stderr}"
    );
}

fn assert_run_backend(output: &Output, backend: &str) {
    let stderr = stderr(output);
    assert!(
        stderr.contains(&format!("run.backend: {backend}")),
        "{stderr}"
    );
}

fn artifact_cache_file_count(root: &Path, stage: &str) -> usize {
    let dir = root.join("artifacts").join(stage);
    match fs::read_dir(dir) {
        Ok(entries) => entries
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.is_file())
            .count(),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => 0,
        Err(error) => panic!("failed to read cache dir: {error}"),
    }
}

fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(output),
        stderr(output)
    );
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}
