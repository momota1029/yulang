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
         my handle(action: [out] _) = catch action:\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n\n\
         my f = \\n -> out::say(n)\n\
         handle(f 1)\n",
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
    assert!(stdout.contains("run roots [true]\n"), "{stdout}");
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
    assert_cache_route(&output, "control-hit");

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
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib")
}

fn repo_yulang_fixture(path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests")
        .join("yulang")
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
