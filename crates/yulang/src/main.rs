use std::cmp::Reverse;
use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs;
use std::fs::File;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;
use std::thread;
use std::time::{Duration, Instant};

use chasa::error::LatestSink;
use chasa::input::{In, Input as _, IsCut};
use either::Either;
use im::HashSet;
use pprof::ProfilerGuardBuilder;
use reborrow_generic::Reborrow as _;
use rowan::SyntaxNode;
use yulang_core_ir as core_ir;
use yulang_infer::ids::{NegId as InferNegId, PosId as InferPosId};
use yulang_infer::{
    ExpectedEdge as InferExpectedEdge, ExpectedEdgeKind as InferExpectedEdgeKind,
    ExpectedShape as InferExpectedShape, FinalizeCompactProfile as InferFinalizeCompactProfile,
    LowerState as InferLowerState, Neg as InferNeg, Path as InferPath, Pos as InferPos,
    SourceLowerProfile as InferSourceLowerProfile, SourceOptions,
    SurfaceDiagnostic as InferSurfaceDiagnostic, TypeError as InferTypeError,
    TypeErrorKind as InferTypeErrorKind, collect_compact_results as collect_infer_compact_results,
    collect_derived_expected_edge_evidence as collect_infer_derived_expected_edge_evidence,
    collect_expected_adapter_edge_evidence as collect_infer_expected_adapter_edge_evidence,
    collect_expected_edge_evidence as collect_infer_expected_edge_evidence,
    collect_expected_edges as collect_infer_expected_edges,
    collect_surface_diagnostics as collect_infer_surface_diagnostics, export_core_program,
    lower_entry_with_options_profiled as lower_infer_entry_with_options_profiled,
    lower_virtual_source_with_options_profiled as lower_infer_virtual_source_with_options_profiled,
};
use yulang_parser::context::{Env, State};
use yulang_parser::expr::parse_expr;
use yulang_parser::lex::{SyntaxKind, TriviaInfo};
use yulang_parser::mark::parse::parse_doc;
use yulang_parser::op::standard_op_table;
use yulang_parser::parse_module_to_green;
use yulang_parser::pat::parse::parse_pattern;
use yulang_parser::scan::trivia::scan_trivia;
use yulang_parser::sink::{Event, EventSink, VecSink, YulangLanguage};
use yulang_parser::stmt::parse_statement;
use yulang_parser::typ::parse::parse_type;
use yulang_runtime as runtime;

// ── CLI ───────────────────────────────────────────────────────────────────────

fn main() {
    let options = parse_args();
    let guard = start_cpu_profile(&options);
    run_with_large_stack({
        let options = options.clone();
        move || run(&options)
    });
    finish_cpu_profile(guard, &options);
}

fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
where
    T: Send + 'static,
{
    thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack yulang thread")
        .join()
        .expect("join large-stack yulang thread")
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CliOptions {
    show_cst: bool,
    parse_mode: Option<ParserMode>,
    infer: bool,
    core_ir: bool,
    runtime_ir: bool,
    hygiene_ir: bool,
    run_vm: bool,
    verbose_ir: bool,
    infer_phase_timings: bool,
    runtime_phase_timings: bool,
    path: Option<String>,
    no_prelude: bool,
    std_root: Option<String>,
    profile_flamegraph: Option<String>,
    profile_repeat: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParserMode {
    Expr,
    Pat,
    Stmt,
    Type,
    Mark,
}

fn parse_args() -> CliOptions {
    let mut show_cst = false;
    let mut parse_mode = None;
    let mut infer = false;
    let mut core_ir = false;
    let mut runtime_ir = false;
    let mut hygiene_ir = false;
    let mut run_vm = false;
    let mut verbose_ir = false;
    let mut infer_phase_timings = false;
    let mut runtime_phase_timings = false;
    let mut path = None;
    let mut no_prelude = false;
    let mut std_root = None;
    let mut profile_flamegraph = None;
    let mut profile_repeat = 1usize;
    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                print_usage();
                process::exit(0);
            }
            "--cst" => show_cst = true,
            "--parse-expr" => parse_mode = Some(ParserMode::Expr),
            "--parse-pat" => parse_mode = Some(ParserMode::Pat),
            "--parse-stmt" => parse_mode = Some(ParserMode::Stmt),
            "--parse-type" | "--parse-typ" => parse_mode = Some(ParserMode::Type),
            "--parse-mark" => parse_mode = Some(ParserMode::Mark),
            "--infer" => infer = true,
            "--core-ir" => core_ir = true,
            "--runtime-ir" => runtime_ir = true,
            "--hygiene-ir" => hygiene_ir = true,
            "--run" => run_vm = true,
            "--verbose-ir" => verbose_ir = true,
            "--infer-phase-timings" => infer_phase_timings = true,
            "--runtime-phase-timings" => runtime_phase_timings = true,
            "--no-prelude" => no_prelude = true,
            "--std-root" => {
                let Some(value) = args.next() else {
                    eprintln!("missing value for --std-root");
                    print_usage();
                    process::exit(2);
                };
                std_root = Some(value);
            }
            "--profile-flamegraph" => {
                let Some(value) = args.next() else {
                    eprintln!("missing value for --profile-flamegraph");
                    print_usage();
                    process::exit(2);
                };
                profile_flamegraph = Some(value);
            }
            "--profile-repeat" => {
                let Some(value) = args.next() else {
                    eprintln!("missing value for --profile-repeat");
                    print_usage();
                    process::exit(2);
                };
                profile_repeat = match value.parse() {
                    Ok(n) if n > 0 => n,
                    _ => {
                        eprintln!("--profile-repeat must be a positive integer");
                        process::exit(2);
                    }
                };
            }
            s if s.starts_with("--") => {
                eprintln!("unknown option: {s}");
                print_usage();
                process::exit(2);
            }
            _ => {
                if path.is_some() {
                    print_usage();
                    process::exit(2);
                }
                path = Some(arg);
            }
        }
    }
    if parse_mode.is_none()
        && !show_cst
        && !infer
        && !core_ir
        && !runtime_ir
        && !hygiene_ir
        && !run_vm
    {
        infer = true;
    }
    CliOptions {
        show_cst,
        parse_mode,
        infer,
        core_ir,
        runtime_ir,
        hygiene_ir,
        run_vm,
        verbose_ir,
        infer_phase_timings,
        runtime_phase_timings,
        path,
        no_prelude,
        std_root,
        profile_flamegraph,
        profile_repeat,
    }
}

fn read_source(path: Option<&str>) -> String {
    match path {
        Some(p) => match fs::read_to_string(p) {
            Ok(s) => s,
            Err(err) => {
                eprintln!("failed to read {p}: {err}");
                process::exit(1);
            }
        },
        None => {
            let mut buf = String::new();
            if let Err(err) = io::stdin().read_to_string(&mut buf) {
                eprintln!("failed to read stdin: {err}");
                process::exit(1);
            }
            buf
        }
    }
}

fn print_usage() {
    eprintln!(
        "usage: yulang [--cst] [--parse-expr|--parse-pat|--parse-stmt|--parse-type|--parse-mark] [--infer] [--core-ir] [--runtime-ir] [--hygiene-ir] [--run] [--verbose-ir] [--infer-phase-timings] [--runtime-phase-timings] [--no-prelude] [--std-root <path>] [--profile-flamegraph <svg>] [<path>]"
    );
    eprintln!("       (no path = read from stdin)");
    eprintln!("       --cst         also print the CST before types");
    eprintln!("       --parse-expr  print the parser event tree for one expression");
    eprintln!("       --parse-pat   print the parser event tree for one pattern");
    eprintln!("       --parse-stmt  print the parser event tree for statements");
    eprintln!("       --parse-type  print the parser event tree for one type");
    eprintln!("       --parse-mark  print the parser event tree for raw Yumark source");
    eprintln!("       --infer       print inferred principal types");
    eprintln!("       --core-ir     print principal core-ir exported from yulang-infer");
    eprintln!("       --runtime-ir  print strict typed runtime IR lowered from principal core-ir");
    eprintln!("       --hygiene-ir  print runtime effect-id hygiene operations");
    eprintln!("       --run         execute the program and print results");
    eprintln!("       --verbose-ir  include detailed graph/evidence sections in IR dumps");
    eprintln!("       --infer-phase-timings  print coarse timing breakdown for the infer pipeline");
    eprintln!(
        "       --runtime-phase-timings  print coarse timing breakdown for runtime lowering/VM"
    );
    eprintln!("       --no-prelude  do not implicitly import std::prelude");
    eprintln!("       --std-root <path>  use an alternate std source root");
    eprintln!("       --profile-flamegraph <svg>  write a CPU flamegraph SVG with pprof");
    eprintln!(
        "       --profile-repeat <n>  run the pipeline n times and print only the last result"
    );
}

fn run(options: &CliOptions) {
    for iteration in 0..options.profile_repeat {
        let source = read_source(options.path.as_deref());
        let emit_output = iteration + 1 == options.profile_repeat;

        if let Some(mode) = options.parse_mode {
            if emit_output {
                run_parser_view(mode, &source);
            }
            continue;
        }

        let green = parse_module_to_green(&source);
        let root = SyntaxNode::<YulangLanguage>::new_root(green);

        if options.show_cst && emit_output {
            print_cst(&root, 0);
            println!();
        }

        if options.infer
            || options.core_ir
            || options.runtime_ir
            || options.hygiene_ir
            || options.run_vm
        {
            run_infer_views(
                options.path.as_deref(),
                &root,
                &source,
                options,
                emit_output,
            );
            continue;
        }
    }
}

fn start_cpu_profile(options: &CliOptions) -> Option<pprof::ProfilerGuard<'static>> {
    let Some(_) = options.profile_flamegraph else {
        return None;
    };
    match ProfilerGuardBuilder::default()
        .frequency(1000)
        .blocklist(&["libc", "libgcc", "pthread", "vdso"])
        .build()
    {
        Ok(guard) => Some(guard),
        Err(err) => {
            eprintln!("failed to start profiler: {err}");
            process::exit(1);
        }
    }
}

fn finish_cpu_profile(guard: Option<pprof::ProfilerGuard<'static>>, options: &CliOptions) {
    let (Some(guard), Some(path)) = (guard, options.profile_flamegraph.as_deref()) else {
        return;
    };
    let report = match guard.report().build() {
        Ok(report) => report,
        Err(err) => {
            eprintln!("failed to build profile report: {err}");
            process::exit(1);
        }
    };
    let file = match File::create(path) {
        Ok(file) => file,
        Err(err) => {
            eprintln!("failed to create flamegraph output {path}: {err}");
            process::exit(1);
        }
    };
    if let Err(err) = report.flamegraph(file) {
        eprintln!("failed to write flamegraph {path}: {err}");
        process::exit(1);
    }
    eprintln!("wrote flamegraph: {path}");
}

// ── CST 表示 ─────────────────────────────────────────────────────────────────

fn print_cst(node: &SyntaxNode<YulangLanguage>, indent: usize) {
    let prefix = "  ".repeat(indent);
    print!("{prefix}{:?}", node.kind());
    let text = node.text().to_string();
    if !text.contains('\n') && text.len() < 40 {
        println!("  {:?}", text);
    } else {
        println!();
    }
    for child in node.children() {
        print_cst(&child, indent + 1);
    }
}

fn run_parser_view(mode: ParserMode, source: &str) {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    let ok = if matches!(mode, ParserMode::Mark) {
        parse_doc(i.rb());
        true
    } else {
        let leading_info = i
            .run(scan_trivia)
            .map(|trivia| trivia.info())
            .unwrap_or(TriviaInfo::None);
        match mode {
            ParserMode::Expr => run_parse_expr(i.rb(), leading_info),
            ParserMode::Pat => run_parse_pat(i.rb(), leading_info),
            ParserMode::Stmt => run_parse_stmt(i.rb(), leading_info),
            ParserMode::Type => run_parse_type(i.rb(), leading_info),
            ParserMode::Mark => unreachable!(),
        }
    };

    let (events, lexs) = std::mem::take(&mut i.env.state.sink).into_parts();
    print_parser_event_tree(&events, &lexs);

    if !ok {
        eprintln!("parse failed");
        process::exit(1);
    }
}

fn print_parser_event_tree(events: &[Event], lexs: &[yulang_parser::lex::Lex]) {
    let mut indent = 0usize;
    let mut iter = lexs.iter();
    for event in events {
        match event {
            Event::Start(kind) => {
                println!("{}{:?}", "  ".repeat(indent), kind);
                indent += 1;
            }
            Event::Lex(kind) => {
                let lex = iter.next();
                let (text, lead, trail) = match lex {
                    Some(lex) => (
                        format!("{:?}", lex.text.as_ref()),
                        format!("{:?}", lex.leading_trivia_info),
                        lex.trailing_trivia.parts().len(),
                    ),
                    None => ("<missing>".to_string(), "-".to_string(), 0),
                };
                println!(
                    "{}{:?} {}  lead={} trail={}",
                    "  ".repeat(indent),
                    kind,
                    text,
                    lead,
                    trail
                );
            }
            Event::Finish => {
                indent = indent.saturating_sub(1);
            }
        }
    }
}

fn run_parse_expr<I: yulang_parser::EventInput>(
    mut i: yulang_parser::context::In<I, VecSink>,
    leading_info: TriviaInfo,
) -> bool {
    let parsed = parse_expr(leading_info, i.rb());
    emit_parse_stop_if_any(i.rb(), parsed)
}

fn run_parse_pat<I: yulang_parser::EventInput>(
    mut i: yulang_parser::context::In<I, VecSink>,
    leading_info: TriviaInfo,
) -> bool {
    let parsed = parse_pattern(leading_info, i.rb());
    emit_parse_stop_if_any(i.rb(), parsed)
}

fn run_parse_type<I: yulang_parser::EventInput>(
    mut i: yulang_parser::context::In<I, VecSink>,
    leading_info: TriviaInfo,
) -> bool {
    let parsed = parse_type(leading_info, i.rb());
    emit_parse_stop_if_any(i.rb(), parsed)
}

fn run_parse_stmt<I: yulang_parser::EventInput>(
    mut i: yulang_parser::context::In<I, VecSink>,
    mut leading_info: TriviaInfo,
) -> bool {
    i.env.state.sink.start(SyntaxKind::IndentBlock);
    loop {
        let parsed = parse_statement(leading_info, i.rb());
        match parsed {
            Some(Either::Left(next)) => leading_info = next,
            Some(Either::Right(stop)) if stop.kind == SyntaxKind::Semicolon => {
                i.env.state.sink.start(SyntaxKind::Separator);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
                leading_info = stop.trailing_trivia_info();
            }
            Some(Either::Right(stop)) => {
                i.env.state.sink.start(SyntaxKind::InvalidToken);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
                leading_info = stop.trailing_trivia_info();
            }
            None => break,
        }
    }
    i.env.state.sink.finish();
    true
}

fn emit_parse_stop_if_any<I: yulang_parser::EventInput>(
    i: yulang_parser::context::In<I, VecSink>,
    parsed: Option<Either<TriviaInfo, yulang_parser::lex::Lex>>,
) -> bool {
    let ok = parsed.is_some();
    if let Some(Either::Right(stop)) = parsed {
        i.env.state.sink.start(SyntaxKind::InvalidToken);
        i.env.state.sink.lex(&stop);
        i.env.state.sink.finish();
    }
    ok
}

fn run_infer_views(
    path: Option<&str>,
    root: &SyntaxNode<YulangLanguage>,
    source: &str,
    options: &CliOptions,
    emit_output: bool,
) {
    let (mut state, diagnostic_source, lower_profile) =
        lower_infer_sources(path, root, source, options);

    let finalized = state.finalize_compact_results_profiled();

    let error_start = Instant::now();
    let errors = state.infer.type_errors();
    let surface_diagnostics = collect_infer_surface_diagnostics(&state);
    let error_duration = error_start.elapsed();

    let (rendered, render_duration, binding_names, quantified_counts) = if options.infer {
        let render_start = Instant::now();
        let rendered = collect_infer_compact_results(&state);
        let render_duration = render_start.elapsed();
        let binding_names = state
            .ctx
            .collect_binding_paths()
            .into_iter()
            .map(|(path, def)| (def, format_infer_path(&path)))
            .collect::<HashMap<_, _>>();
        let quantified_counts = state
            .infer
            .frozen_schemes
            .borrow()
            .iter()
            .map(|(k, v)| (*k, v.quantified.len()))
            .collect::<HashMap<_, _>>();
        (
            Some(rendered),
            render_duration,
            Some(binding_names),
            Some(quantified_counts),
        )
    } else {
        (None, Duration::ZERO, None, None)
    };

    let infer_program = if surface_diagnostics.is_empty()
        && (options.core_ir || options.runtime_ir || options.hygiene_ir || options.run_vm)
    {
        Some(export_core_program(&mut state))
    } else {
        None
    };

    if emit_output {
        for error in errors {
            print_infer_type_error(&state, &error, &diagnostic_source);
        }
        for diagnostic in &surface_diagnostics {
            print_infer_surface_diagnostic(diagnostic, &diagnostic_source);
        }
        if !surface_diagnostics.is_empty()
            && (options.core_ir || options.runtime_ir || options.hygiene_ir || options.run_vm)
        {
            process::exit(1);
        }
        if let Some(rendered) = rendered {
            for (name, scheme) in rendered {
                println!("{name} : {scheme}");
            }
            if options.verbose_ir {
                let expected_edges = collect_infer_expected_edges(&state);
                if !expected_edges.is_empty() {
                    println!();
                    println!("expected-edges:");
                    for edge in expected_edges {
                        println!("  {edge}");
                    }
                }
                let expected_edge_evidence = collect_infer_expected_edge_evidence(&state);
                if !expected_edge_evidence.is_empty() {
                    println!();
                    println!("expected-edge-evidence:");
                    for evidence in expected_edge_evidence {
                        println!("  {}", format_expected_edge_evidence(&evidence));
                    }
                }
                let derived_expected_edge_evidence =
                    collect_infer_derived_expected_edge_evidence(&state);
                if !derived_expected_edge_evidence.is_empty() {
                    println!();
                    println!("derived-expected-edge-evidence:");
                    for evidence in derived_expected_edge_evidence {
                        println!("  {}", format_derived_expected_edge_evidence(&evidence));
                    }
                }
                let expected_adapter_edge_evidence =
                    collect_infer_expected_adapter_edge_evidence(&state);
                if !expected_adapter_edge_evidence.is_empty() {
                    println!();
                    println!("expected-adapter-edge-evidence:");
                    for evidence in expected_adapter_edge_evidence {
                        println!("  {}", format_expected_adapter_edge_evidence(&evidence));
                    }
                }
            }
        }
        if options.core_ir {
            if options.infer {
                println!();
            }
            println!("core-ir:");
            print_infer_program(
                infer_program.as_ref().expect("core program"),
                options.verbose_ir,
            );
        }
        if options.runtime_ir {
            if options.infer || options.core_ir {
                println!();
            }
            println!("runtime-ir:");
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
            );
            print_runtime_module(&lowered.module, options.verbose_ir);
        }
        if options.hygiene_ir {
            if options.infer || options.core_ir || options.runtime_ir {
                println!();
            }
            println!("hygiene-ir:");
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
            );
            print!("{}", runtime::format_hygiene_module(&lowered.module));
        }
        if options.run_vm {
            if options.infer || options.core_ir || options.runtime_ir || options.hygiene_ir {
                println!();
            }
            let lowered =
                lower_runtime_module_or_exit(infer_program.as_ref().expect("core program"), false);
            let compile_start = Instant::now();
            let module = match runtime::compile_vm_module(lowered.module) {
                Ok(module) => module,
                Err(err) => {
                    eprintln!("failed to compile runtime IR: {err}");
                    process::exit(1);
                }
            };
            let compile_duration = compile_start.elapsed();
            let eval_start = Instant::now();
            let results = match module.eval_roots() {
                Ok(results) => results,
                Err(err) => {
                    eprintln!("failed to evaluate runtime IR: {err}");
                    process::exit(1);
                }
            };
            let eval_duration = eval_start.elapsed();
            if options.runtime_phase_timings {
                print_runtime_phase_timings(
                    &lowered.profile,
                    Some(compile_duration),
                    Some(eval_duration),
                );
            }
            for (index, result) in results.iter().enumerate() {
                println!("[{index}] {}", format_runtime_vm_result(result));
            }
        }
        if options.infer_phase_timings && options.infer {
            print_infer_phase_timings(
                &lower_profile,
                error_duration,
                &finalized.profile,
                render_duration,
                finalized.finalized_defs.len(),
                binding_names.as_ref().expect("binding names"),
                quantified_counts.as_ref().expect("quantified counts"),
            );
        }
    }
}

struct RuntimeLowerOutput {
    module: runtime::Module,
    profile: RuntimePhaseProfile,
}

#[derive(Default)]
struct RuntimePhaseProfile {
    lower: Duration,
    lower_profile: runtime::RuntimeLowerProfile,
    monomorphize: Duration,
    monomorphize_profile: runtime::MonomorphizeProfile,
}

fn lower_runtime_module_or_exit(
    program: &core_ir::CoreProgram,
    print_timings: bool,
) -> RuntimeLowerOutput {
    let lower_start = Instant::now();
    let lower_output = match runtime::lower_core_program_profiled(program.clone()) {
        Ok(output) => output,
        Err(err) => {
            eprintln!("failed to lower runtime IR: {err}");
            process::exit(1);
        }
    };
    let lower_profile = lower_output.profile;
    let module = lower_output.module;
    let lower = lower_start.elapsed();
    let mono_start = Instant::now();
    let (module, monomorphize_profile) = match runtime::monomorphize_module_profiled(module) {
        Ok(output) => output,
        Err(err) => {
            eprintln!("failed to lower runtime IR: {err}");
            process::exit(1);
        }
    };
    let monomorphize = mono_start.elapsed();
    let profile = RuntimePhaseProfile {
        lower,
        lower_profile,
        monomorphize,
        monomorphize_profile,
    };
    if print_timings {
        print_runtime_phase_timings(&profile, None, None);
    }
    RuntimeLowerOutput { module, profile }
}

fn print_runtime_phase_timings(
    profile: &RuntimePhaseProfile,
    vm_compile: Option<Duration>,
    vm_eval: Option<Duration>,
) {
    eprintln!("runtime phase timings:");
    eprintln!("    runtime_lower: {}", format_duration(profile.lower));
    eprintln!(
        "    monomorphize: {}",
        format_duration(profile.monomorphize)
    );
    eprintln!(
        "    mono_passes: {}, effective_passes: {}, specializations: {}",
        profile.monomorphize_profile.pass_count(),
        profile.monomorphize_profile.effective_pass_count(),
        profile.monomorphize_profile.added_specializations()
    );
    let expected_arg = &profile.lower_profile.expected_arg_evidence;
    eprintln!(
        "    expected_arg_evidence: present={}, converted={}, usable_by_table={}, usable_by_bounds={}, used_as_arg_type_hint={}, used_as_lowering_expected={}, ignored_no_expected_arg={}, ignored_not_convertible={}, ignored_table_open={}, ignored_table_uninformative={}, ignored_table_not_runtime_usable={}, ignored_bounds_unusable={}, ignored_unusable={}, ignored_no_push={}",
        expected_arg.present,
        expected_arg.converted,
        expected_arg.usable_by_table,
        expected_arg.usable_by_bounds,
        expected_arg.used_as_arg_type_hint,
        expected_arg.used_as_lowering_expected,
        expected_arg.ignored_no_expected_arg,
        expected_arg.ignored_not_convertible,
        expected_arg.ignored_table_open,
        expected_arg.ignored_table_uninformative,
        expected_arg.ignored_table_not_runtime_usable,
        expected_arg.ignored_bounds_unusable,
        expected_arg.ignored_unusable,
        expected_arg.ignored_no_push,
    );
    let adapters = &profile.lower_profile.runtime_adapters;
    eprintln!(
        "    runtime_adapters: value_to_thunk={}, thunk_to_value={}, bind_here={}, apply_evidence_value_to_thunk={}, apply_evidence_thunk_to_value={}, apply_evidence_bind_here={}, apply_evidence_adapter_with_evidence={}, apply_evidence_adapter_with_source_edge={}, apply_evidence_adapter_without_evidence={}, apply_evidence_value_to_thunk_with_source_edge={}, apply_evidence_thunk_to_value_with_source_edge={}, apply_evidence_bind_here_with_source_edge={}, reused_thunk={}, forced_effect_thunk={}",
        adapters.value_to_thunk,
        adapters.thunk_to_value,
        adapters.bind_here,
        adapters.apply_evidence_value_to_thunk,
        adapters.apply_evidence_thunk_to_value,
        adapters.apply_evidence_bind_here,
        adapters.apply_evidence_adapter_with_evidence,
        adapters.apply_evidence_adapter_with_source_edge,
        adapters.apply_evidence_adapter_without_evidence,
        adapters.apply_evidence_value_to_thunk_with_source_edge,
        adapters.apply_evidence_thunk_to_value_with_source_edge,
        adapters.apply_evidence_bind_here_with_source_edge,
        adapters.reused_thunk,
        adapters.forced_effect_thunk,
    );
    eprintln!(
        "    runtime_adapter_phases: apply_lower_callee(value_to_thunk={}, thunk_to_value={}, bind_here={}), apply_lower_argument(value_to_thunk={}, thunk_to_value={}, bind_here={}), apply_prepare_final_argument(value_to_thunk={}, thunk_to_value={}, bind_here={}), apply_prepare_effect_operation_argument(value_to_thunk={}, thunk_to_value={}, bind_here={})",
        adapters.apply_lower_callee_value_to_thunk,
        adapters.apply_lower_callee_thunk_to_value,
        adapters.apply_lower_callee_bind_here,
        adapters.apply_lower_argument_value_to_thunk,
        adapters.apply_lower_argument_thunk_to_value,
        adapters.apply_lower_argument_bind_here,
        adapters.apply_prepare_final_argument_value_to_thunk,
        adapters.apply_prepare_final_argument_thunk_to_value,
        adapters.apply_prepare_final_argument_bind_here,
        adapters.apply_prepare_effect_operation_argument_value_to_thunk,
        adapters.apply_prepare_effect_operation_argument_thunk_to_value,
        adapters.apply_prepare_effect_operation_argument_bind_here,
    );
    print_runtime_adapter_event_summary(adapters);
    let adapter_evidence = &profile.lower_profile.expected_adapter_evidence;
    eprintln!(
        "    expected_adapter_evidence: total={}, runtime_usable={}, closed={}, informative={}, effect_operation_argument={}, value_to_thunk={}, thunk_to_value={}, bind_here={}, handler_residual={}, handler_return={}, resume_argument={}",
        adapter_evidence.total,
        adapter_evidence.runtime_usable,
        adapter_evidence.closed,
        adapter_evidence.informative,
        adapter_evidence.effect_operation_argument,
        adapter_evidence.value_to_thunk,
        adapter_evidence.thunk_to_value,
        adapter_evidence.bind_here,
        adapter_evidence.handler_residual,
        adapter_evidence.handler_return,
        adapter_evidence.resume_argument,
    );
    let derived_evidence = &profile.lower_profile.derived_expected_evidence;
    eprintln!(
        "    derived_expected_evidence: total={}, record_field={}, tuple_item={}, variant_payload={}, function_param={}, function_return={}, covariant={}, contravariant={}, invariant={}",
        derived_evidence.total,
        derived_evidence.record_field,
        derived_evidence.tuple_item,
        derived_evidence.variant_payload,
        derived_evidence.function_param,
        derived_evidence.function_return,
        derived_evidence.covariant,
        derived_evidence.contravariant,
        derived_evidence.invariant,
    );
    let demand_queue = profile.monomorphize_profile.demand_queue_profile();
    eprintln!(
        "    demand_queue: attempted={}, pushed={}, pushed_open={}, pushed_closed={}, skipped_duplicate={}, skipped_covered_by_closed={}",
        demand_queue.attempted,
        demand_queue.pushed,
        demand_queue.pushed_open,
        demand_queue.pushed_closed,
        demand_queue.skipped_duplicate,
        demand_queue.skipped_covered_by_closed,
    );
    let demand_evidence = &profile.monomorphize_profile.demand_evidence;
    eprintln!(
        "    demand_evidence: apply_arg_calls={}, expected_arg_disabled={}, expected_arg_present={}, expected_arg_converted={}, expected_arg_used={}, expected_arg_changed_signature={}, expected_arg_same_signature={}, expected_arg_rejected_open={}, apply_callee_calls={}, expected_callee_disabled={}, expected_callee_present={}, expected_callee_converted={}, expected_callee_used={}, expected_callee_changed_param_signature={}, expected_callee_same_param_signature={}, expected_callee_rejected_open={}, expected_callee_rejected_non_function={}",
        demand_evidence.apply_arg_signature_calls,
        demand_evidence.expected_arg_hint_disabled,
        demand_evidence.expected_arg_hint_present,
        demand_evidence.expected_arg_hint_converted,
        demand_evidence.expected_arg_hint_used,
        demand_evidence.expected_arg_hint_changed_signature,
        demand_evidence.expected_arg_hint_same_signature,
        demand_evidence.expected_arg_hint_rejected_open,
        demand_evidence.apply_callee_signature_calls,
        demand_evidence.expected_callee_hint_disabled,
        demand_evidence.expected_callee_hint_present,
        demand_evidence.expected_callee_hint_converted,
        demand_evidence.expected_callee_hint_used,
        demand_evidence.expected_callee_hint_changed_param_signature,
        demand_evidence.expected_callee_hint_same_param_signature,
        demand_evidence.expected_callee_hint_rejected_open,
        demand_evidence.expected_callee_hint_rejected_non_function,
    );
    eprintln!("    monomorphize_passes:");
    for pass in &profile.monomorphize_profile.passes {
        let added_paths = pass
            .added_binding_paths
            .iter()
            .map(format_core_path)
            .collect::<Vec<_>>()
            .join(", ");
        eprintln!(
            "        {}: bindings {}->{}, roots {}->{}, changed_bindings={}, changed_roots={}, added_specializations={}, queue_attempted={}, queue_pushed={}, added=[{}]",
            pass.name,
            pass.bindings_before,
            pass.bindings_after,
            pass.roots_before,
            pass.roots_after,
            pass.progress.changed_bindings,
            pass.progress.changed_roots,
            pass.progress.added_specializations,
            pass.demand_queue.attempted,
            pass.demand_queue.pushed,
            added_paths,
        );
        for specialization in &pass.added_specializations {
            eprintln!(
                "            specialization {} <= {} :: {:?}",
                format_core_path(&specialization.path),
                format_core_path(&specialization.target),
                specialization.solved,
            );
        }
        print_substitution_specialize_profile(pass);
    }
    if let Some(duration) = vm_compile {
        eprintln!("    vm_compile: {}", format_duration(duration));
    }
    if let Some(duration) = vm_eval {
        eprintln!("    vm_eval: {}", format_duration(duration));
    }
}

fn print_substitution_specialize_profile(profile: &runtime::MonomorphizePassProfile) {
    let subst = &profile.substitution_specialize;
    if subst.stats.is_empty() && subst.target_skips.is_empty() {
        return;
    }
    let mut stats = subst.stats.iter().collect::<Vec<_>>();
    stats.sort_by(|(left_key, left_count), (right_key, right_count)| {
        right_count
            .cmp(left_count)
            .then_with(|| left_key.cmp(right_key))
    });
    let stats = stats
        .into_iter()
        .take(16)
        .map(|(key, count)| format!("{key}={count}"))
        .collect::<Vec<_>>()
        .join(", ");
    eprintln!("            substitution_specialize: {stats}");
    for target in subst.target_skips.iter().take(12) {
        let total = target
            .reasons
            .iter()
            .map(|reason| reason.count)
            .sum::<usize>();
        let reasons = target
            .reasons
            .iter()
            .map(|reason| format!("{}={}", reason.reason, reason.count))
            .collect::<Vec<_>>()
            .join(", ");
        let missing_vars = target
            .missing_vars
            .iter()
            .take(8)
            .map(|var| format!("{}={}", var.var.0, var.count))
            .collect::<Vec<_>>()
            .join(", ");
        let no_complete_causes = target
            .no_complete_causes
            .iter()
            .map(|cause| format!("{}={}", cause.reason, cause.count))
            .collect::<Vec<_>>()
            .join(", ");
        let survives_final_prune = match target.survives_final_prune {
            Some(true) => "yes",
            Some(false) => "no",
            None => "unknown",
        };
        eprintln!(
            "                skip_target {} total={} survives_final_prune={} reasons=[{}] missing_vars=[{}] no_complete_causes=[{}]",
            format_core_path(&target.target),
            total,
            survives_final_prune,
            reasons,
            missing_vars,
            no_complete_causes,
        );
    }
    for target in subst.target_inferences.iter().take(12) {
        let total = target
            .sources
            .iter()
            .map(|source| source.count)
            .sum::<usize>();
        let sources = target
            .sources
            .iter()
            .map(|source| format!("{}={}", source.source, source.count))
            .collect::<Vec<_>>()
            .join(", ");
        eprintln!(
            "                infer_target {} total={} sources=[{}]",
            format_core_path(&target.target),
            total,
            sources,
        );
    }
}

fn print_runtime_adapter_event_summary(adapters: &runtime::RuntimeAdapterProfile) {
    if adapters.events.is_empty() {
        eprintln!("    runtime_adapter_events: total=0");
        return;
    }
    eprintln!(
        "    runtime_adapter_events: total={}",
        adapters.events.len()
    );
    eprintln!(
        "    runtime_adapter_match: matched_expected_adapter={}, unmatched_expected_adapter={}, unmatched_value_to_thunk={}, unmatched_thunk_to_value={}, unmatched_bind_here={}, matched_derived_parent={}, unmatched_derived_parent={}",
        adapters.matched_expected_adapter,
        adapters.unmatched_expected_adapter,
        adapters.unmatched_value_to_thunk,
        adapters.unmatched_thunk_to_value,
        adapters.unmatched_bind_here,
        adapters.matched_derived_expected_edge_parent,
        adapters.unmatched_derived_expected_edge_parent,
    );
    print_observed_adapter_evidence_summary(adapters);
    let mut by_context = BTreeMap::<(String, String, String, String), usize>::new();
    for event in &adapters.events {
        let phase = runtime_adapter_phase_name(event.phase).to_string();
        let owner = event
            .owner
            .as_ref()
            .map(format_core_path)
            .unwrap_or_else(|| "<root>".to_string());
        let target = event
            .apply_target
            .as_ref()
            .map(format_core_path)
            .unwrap_or_else(|| "<unknown>".to_string());
        let kind = runtime_adapter_kind_name(event.kind).to_string();
        *by_context.entry((phase, owner, target, kind)).or_default() += 1;
    }
    let mut by_context = by_context.into_iter().collect::<Vec<_>>();
    by_context.sort_by(
        |((left_phase, left_owner, left_target, left_kind), left_count),
         ((right_phase, right_owner, right_target, right_kind), right_count)| {
            right_count
                .cmp(left_count)
                .then_with(|| left_phase.cmp(right_phase))
                .then_with(|| left_owner.cmp(right_owner))
                .then_with(|| left_target.cmp(right_target))
                .then_with(|| left_kind.cmp(right_kind))
        },
    );
    for ((phase, owner, target, kind), count) in by_context.iter().take(12) {
        eprintln!(
            "        adapter_event phase={} owner={} target={} kind={} count={}",
            phase, owner, target, kind, count
        );
    }
    if env::var_os("YULANG_TRACE_RUNTIME_ADAPTER_EVENTS").is_some() {
        for event in &adapters.events {
            let owner = event
                .owner
                .as_ref()
                .map(format_core_path)
                .unwrap_or_else(|| "<root>".to_string());
            let target = event
                .apply_target
                .as_ref()
                .map(format_core_path)
                .unwrap_or_else(|| "<unknown>".to_string());
            eprintln!(
                "        adapter_event_detail phase={} owner={} target={} kind={} callee_source_edge={:?} arg_source_edge={:?} actual={:?} expected={:?}",
                runtime_adapter_phase_name(event.phase),
                owner,
                target,
                runtime_adapter_kind_name(event.kind),
                event.callee_source_edge,
                event.arg_source_edge,
                event.actual,
                event.expected,
            );
        }
    }
}

fn print_observed_adapter_evidence_summary(adapters: &runtime::RuntimeAdapterProfile) {
    let mut value_to_thunk = 0;
    let mut force_thunk_to_value = 0;
    for evidence in &adapters.observed_adapter_evidence {
        match evidence.kind {
            runtime::ObservedAdapterEvidenceKind::ValueToThunk => value_to_thunk += 1,
            runtime::ObservedAdapterEvidenceKind::ForceThunkToValue => force_thunk_to_value += 1,
        }
    }
    eprintln!(
        "    observed_adapter_evidence: total={}, value_to_thunk={}, force_thunk_to_value={}, with_source_edge={}, without_source_edge={}, source_application_callee={}, source_application_argument={}, source_other_expected_edge={}, source_with_derived_parent={}, source_without_derived_parent={}",
        adapters.observed_adapter_evidence.len(),
        value_to_thunk,
        force_thunk_to_value,
        adapters.observed_adapter_with_source_expected_edge,
        adapters.observed_adapter_without_source_expected_edge,
        adapters.observed_adapter_source_application_callee,
        adapters.observed_adapter_source_application_argument,
        adapters.observed_adapter_source_other_expected_edge,
        adapters.observed_adapter_source_with_derived_parent,
        adapters.observed_adapter_source_without_derived_parent,
    );

    let mut by_context = BTreeMap::<(String, String, String, String), usize>::new();
    for evidence in &adapters.observed_adapter_evidence {
        let phase = runtime_adapter_phase_name(evidence.phase).to_string();
        let owner = evidence
            .owner
            .as_ref()
            .map(format_core_path)
            .unwrap_or_else(|| "<root>".to_string());
        let target = evidence
            .apply_target
            .as_ref()
            .map(format_core_path)
            .unwrap_or_else(|| "<unknown>".to_string());
        let kind = observed_adapter_evidence_kind_name(evidence.kind).to_string();
        *by_context.entry((phase, owner, target, kind)).or_default() += 1;
    }
    let mut by_context = by_context.into_iter().collect::<Vec<_>>();
    by_context.sort_by(
        |((left_phase, left_owner, left_target, left_kind), left_count),
         ((right_phase, right_owner, right_target, right_kind), right_count)| {
            right_count
                .cmp(left_count)
                .then_with(|| left_phase.cmp(right_phase))
                .then_with(|| left_owner.cmp(right_owner))
                .then_with(|| left_target.cmp(right_target))
                .then_with(|| left_kind.cmp(right_kind))
        },
    );
    for ((phase, owner, target, kind), count) in by_context.iter().take(12) {
        eprintln!(
            "        observed_adapter phase={} owner={} target={} kind={} count={}",
            phase, owner, target, kind, count
        );
    }

    if env::var_os("YULANG_TRACE_RUNTIME_ADAPTER_EVENTS").is_some() {
        for evidence in &adapters.observed_adapter_evidence {
            let owner = evidence
                .owner
                .as_ref()
                .map(format_core_path)
                .unwrap_or_else(|| "<root>".to_string());
            let target = evidence
                .apply_target
                .as_ref()
                .map(format_core_path)
                .unwrap_or_else(|| "<unknown>".to_string());
            eprintln!(
                "        observed_adapter_detail phase={} owner={} target={} kind={} source_expected_edge={:?} actual={:?} expected={:?}",
                runtime_adapter_phase_name(evidence.phase),
                owner,
                target,
                observed_adapter_evidence_kind_name(evidence.kind),
                evidence.source_expected_edge,
                evidence.actual,
                evidence.expected,
            );
        }
    }
}

fn observed_adapter_evidence_kind_name(kind: runtime::ObservedAdapterEvidenceKind) -> &'static str {
    match kind {
        runtime::ObservedAdapterEvidenceKind::ValueToThunk => "value-to-thunk",
        runtime::ObservedAdapterEvidenceKind::ForceThunkToValue => "force-thunk-to-value",
    }
}

fn runtime_adapter_phase_name(phase: runtime::RuntimeApplyAdapterPhase) -> &'static str {
    match phase {
        runtime::RuntimeApplyAdapterPhase::LowerCallee => "apply.lower-callee",
        runtime::RuntimeApplyAdapterPhase::LowerArgument => "apply.lower-argument",
        runtime::RuntimeApplyAdapterPhase::PrepareFinalArgument => "apply.prepare-final-argument",
        runtime::RuntimeApplyAdapterPhase::PrepareEffectOperationArgument => {
            "apply.prepare-effect-operation-argument"
        }
    }
}

fn runtime_adapter_kind_name(kind: runtime::RuntimeAdapterEventKind) -> &'static str {
    match kind {
        runtime::RuntimeAdapterEventKind::ValueToThunk => "value-to-thunk",
        runtime::RuntimeAdapterEventKind::ThunkToValue => "thunk-to-value",
        runtime::RuntimeAdapterEventKind::BindHere => "bind-here",
    }
}

fn print_infer_phase_timings(
    lower: &InferSourceLowerProfile,
    error_collection: Duration,
    finalize: &InferFinalizeCompactProfile,
    render: Duration,
    finalized_defs: usize,
    binding_names: &HashMap<yulang_infer::DefId, String>,
    quantified_counts: &HashMap<yulang_infer::DefId, usize>,
) {
    eprintln!("infer phase timings:");
    eprintln!("  lower: {}", format_duration(lower.total()));
    eprintln!("    collect: {}", format_duration(lower.collect));
    eprintln!("    parse: {}", format_duration(lower.parse));
    eprintln!("    infer_lower: {}", format_duration(lower.infer_lower()));
    eprintln!("      lower_roots: {}", format_duration(lower.lower_roots));
    eprintln!("      finish: {}", format_duration(lower.finish));
    eprintln!(
        "      detail.lower_binding: {}",
        format_duration(lower.detail.lower_binding)
    );
    eprintln!(
        "      detail.extract_binding_lhs: {}",
        format_duration(lower.detail.extract_binding_lhs)
    );
    eprintln!(
        "      detail.lower_binding_scope: {}",
        format_duration(lower.detail.lower_binding_scope)
    );
    eprintln!(
        "      detail.lower_binding_body: {}",
        format_duration(lower.detail.lower_binding_body)
    );
    eprintln!(
        "      detail.wrap_header_lambdas: {}",
        format_duration(lower.detail.wrap_header_lambdas)
    );
    eprintln!(
        "      detail.lower_var_binding_suffix: {}",
        format_duration(lower.detail.lower_var_binding_suffix)
    );
    eprintln!(
        "      detail.lower_act_copy_body: {}",
        format_duration(lower.detail.lower_act_copy_body)
    );
    eprintln!(
        "      detail.lower_act_body: {}",
        format_duration(lower.detail.lower_act_body)
    );
    eprintln!(
        "      detail.lower_act_body_collect_items: {}",
        format_duration(lower.detail.lower_act_body_collect_items)
    );
    eprintln!(
        "      detail.lower_act_body_ops: {}",
        format_duration(lower.detail.lower_act_body_ops)
    );
    eprintln!(
        "      detail.lower_act_body_preregister: {}",
        format_duration(lower.detail.lower_act_body_preregister)
    );
    eprintln!(
        "      detail.lower_act_body_bindings: {}",
        format_duration(lower.detail.lower_act_body_bindings)
    );
    eprintln!(
        "      detail.try_copy_lowered_act_body: {}",
        format_duration(lower.detail.try_copy_lowered_act_body)
    );
    eprintln!(
        "      detail.try_lower_act_copy_from_template: {}",
        format_duration(lower.detail.try_lower_act_copy_from_template)
    );
    eprintln!(
        "      detail.copy_effect_ops_from_source_module: {}",
        format_duration(lower.detail.copy_effect_ops_from_source_module)
    );
    eprintln!(
        "      detail.connect_pat_shape_and_locals: {}",
        format_duration(lower.detail.connect_pat_shape_and_locals)
    );
    eprintln!(
        "      detail.lower_expr: {}",
        format_duration(lower.detail.lower_expr)
    );
    eprintln!(
        "      detail.lower_expr_chain: {}",
        format_duration(lower.detail.lower_expr_chain)
    );
    eprintln!(
        "      detail.resolve_path_expr: {}",
        format_duration(lower.detail.resolve_path_expr)
    );
    eprintln!(
        "      detail.apply_suffix: {}",
        format_duration(lower.detail.apply_suffix)
    );
    eprintln!(
        "      detail.lower_expr_atom: {}",
        format_duration(lower.detail.lower_expr_atom)
    );
    eprintln!(
        "      detail.lower_expr_atom_tuple: {}",
        format_duration(lower.detail.lower_expr_atom_tuple)
    );
    eprintln!(
        "      detail.lower_expr_atom_record: {}",
        format_duration(lower.detail.lower_expr_atom_record)
    );
    eprintln!(
        "      detail.lower_expr_atom_block: {}",
        format_duration(lower.detail.lower_expr_atom_block)
    );
    eprintln!(
        "      detail.lower_expr_atom_lambda: {}",
        format_duration(lower.detail.lower_expr_atom_lambda)
    );
    eprintln!(
        "      detail.lower_expr_atom_catch: {}",
        format_duration(lower.detail.lower_expr_atom_catch)
    );
    eprintln!(
        "      detail.lower_expr_atom_case: {}",
        format_duration(lower.detail.lower_expr_atom_case)
    );
    eprintln!(
        "      detail.lower_expr_atom_if: {}",
        format_duration(lower.detail.lower_expr_atom_if)
    );
    eprintln!(
        "      detail.lower_expr_atom_literal: {}",
        format_duration(lower.detail.lower_expr_atom_literal)
    );
    eprintln!(
        "      detail.lower_catch: {}",
        format_duration(lower.detail.lower_catch)
    );
    eprintln!(
        "      detail.lower_catch_arm: {}",
        format_duration(lower.detail.lower_catch_arm)
    );
    eprintln!(
        "      detail.bind_catch_pat_locals: {}",
        format_duration(lower.detail.bind_catch_pat_locals)
    );
    eprintln!(
        "      detail.connect_catch_pat_locals: {}",
        format_duration(lower.detail.connect_catch_pat_locals)
    );
    eprintln!(
        "      detail.instantiate_effect_op_use: {}",
        format_duration(lower.detail.instantiate_effect_op_use)
    );
    eprintln!(
        "      detail.extract_catch_effect_path: {}",
        format_duration(lower.detail.extract_catch_effect_path)
    );
    eprintln!(
        "      detail.lower_catch_effect_payload_pat: {}",
        format_duration(lower.detail.lower_catch_effect_payload_pat)
    );
    eprintln!(
        "      detail.connect_pat_name: {}",
        format_duration(lower.detail.connect_pat_name)
    );
    eprintln!(
        "      detail.connect_pat_tuple: {}",
        format_duration(lower.detail.connect_pat_tuple)
    );
    eprintln!(
        "      detail.connect_pat_record: {}",
        format_duration(lower.detail.connect_pat_record)
    );
    eprintln!(
        "      detail.connect_pat_poly_variant: {}",
        format_duration(lower.detail.connect_pat_poly_variant)
    );
    eprintln!(
        "      detail.connect_pat_alias: {}",
        format_duration(lower.detail.connect_pat_alias)
    );
    eprintln!(
        "      detail.connect_pat_or: {}",
        format_duration(lower.detail.connect_pat_or)
    );
    eprintln!("    files: {}", lower.files);
    eprintln!("  type_errors: {}", format_duration(error_collection));
    eprintln!(
        "  finalize: {}  (iterations={}, finalized_defs={})",
        format_duration(finalize.total),
        finalize.iterations,
        finalized_defs,
    );
    eprintln!("    scc_compute: {}", format_duration(finalize.scc_compute));
    eprintln!(
        "    scc_compress: {}",
        format_duration(finalize.scc_compress)
    );
    eprintln!("    scc_share: {}", format_duration(finalize.scc_share));
    eprintln!(
        "    commit_ready: {}  (ready_components={}, committed_components={}, compacted_defs={}, instantiated_refs={})",
        format_duration(finalize.commit_ready.total),
        finalize.commit_ready.ready_components,
        finalize.commit_ready.committed_components,
        finalize.commit_ready.compacted_defs,
        finalize.commit_ready.instantiated_refs,
    );
    eprintln!(
        "      ready_scan: {}",
        format_duration(finalize.commit_ready.ready_scan)
    );
    eprintln!(
        "      compact: {}",
        format_duration(finalize.commit_ready.compact)
    );
    eprintln!(
        "        compact_var_side: {}",
        format_duration(finalize.commit_ready.compact_var_side)
    );
    eprintln!(
        "        compact_pos_ref: {}",
        format_duration(finalize.commit_ready.compact_pos_ref)
    );
    eprintln!(
        "        compact_neg_ref: {}",
        format_duration(finalize.commit_ready.compact_neg_ref)
    );
    eprintln!(
        "        compact_reachable_rec_vars: {}",
        format_duration(finalize.commit_ready.compact_reachable_rec_vars)
    );
    eprintln!(
        "      role_constraints: {}",
        format_duration(finalize.commit_ready.role_constraints)
    );
    eprintln!(
        "      cooccur: {}",
        format_duration(finalize.commit_ready.cooccur)
    );
    eprintln!(
        "      freeze: {}",
        format_duration(finalize.commit_ready.freeze)
    );
    eprintln!(
        "      instantiate: {}",
        format_duration(finalize.commit_ready.instantiate)
    );
    eprintln!(
        "        instantiate_build_subst: {}",
        format_duration(finalize.commit_ready.instantiate_build_subst)
    );
    eprintln!(
        "        instantiate_subst_body: {}",
        format_duration(finalize.commit_ready.instantiate_subst_body)
    );
    eprintln!(
        "        instantiate_constrain: {}",
        format_duration(finalize.commit_ready.instantiate_constrain)
    );
    eprintln!(
        "        instantiate_role_constraints: {}",
        format_duration(finalize.commit_ready.instantiate_role_constraints)
    );
    if !finalize.commit_ready.instantiate_counts_by_def.is_empty() {
        let mut top = finalize
            .commit_ready
            .instantiate_counts_by_def
            .iter()
            .map(|(def, count)| (*count, def.0))
            .collect::<Vec<_>>();
        top.sort_unstable_by(|lhs, rhs| rhs.cmp(lhs));
        let rendered = top
            .into_iter()
            .take(8)
            .map(|(count, def)| {
                let def_id = yulang_infer::DefId(def);
                let name = binding_names
                    .get(&def_id)
                    .cloned()
                    .unwrap_or_else(|| format!("def#{def}"));
                let quantified = quantified_counts.get(&def_id).copied().unwrap_or(0);
                format!("{name}[q={quantified}]x{count}")
            })
            .collect::<Vec<_>>()
            .join(", ");
        eprintln!("      instantiate_top: {rendered}");
    }
    eprintln!(
        "      prune_edges: {}",
        format_duration(finalize.commit_ready.prune_edges)
    );
    eprintln!("  render: {}", format_duration(render));
}

fn format_duration(duration: Duration) -> String {
    let nanos = duration.as_nanos();
    if nanos < 1_000 {
        return format!("{nanos}ns");
    }
    if nanos < 1_000_000 {
        return format!("{:.3}us", duration.as_secs_f64() * 1_000_000.0);
    }
    if nanos < 1_000_000_000 {
        return format!("{:.3}ms", duration.as_secs_f64() * 1_000.0);
    }
    format!("{:.3}s", duration.as_secs_f64())
}

fn lower_infer_sources(
    path: Option<&str>,
    _root: &SyntaxNode<YulangLanguage>,
    source: &str,
    options: &CliOptions,
) -> (InferLowerState, String, InferSourceLowerProfile) {
    let Some(path) = path else {
        let lowered = match lower_infer_virtual_source_with_options_profiled(
            source,
            env::current_dir().ok(),
            source_options(options),
        ) {
            Ok(lowered) => lowered,
            Err(err) => {
                eprintln!("{err}");
                process::exit(1);
            }
        };
        return (
            lowered.lowered.state,
            if lowered.lowered.diagnostic_source.is_empty() {
                source.to_string()
            } else {
                lowered.lowered.diagnostic_source
            },
            lowered.profile,
        );
    };

    let lowered = match lower_infer_entry_with_options_profiled(path, source_options(options)) {
        Ok(lowered) => lowered,
        Err(err) => {
            eprintln!("{err}");
            process::exit(1);
        }
    };
    (
        lowered.lowered.state,
        if lowered.lowered.diagnostic_source.is_empty() {
            source.to_string()
        } else {
            lowered.lowered.diagnostic_source
        },
        lowered.profile,
    )
}

fn print_infer_type_error(state: &InferLowerState, error: &InferTypeError, source: &str) {
    eprintln!("type error: {}", infer_error_headline(state, error));
    if let Some(span) = error.cause.span {
        let (line, col) = line_col(source, u32::from(span.start()) as usize);
        eprintln!("  at {line}:{col} ({:?})", error.cause.reason);
    } else {
        eprintln!("  at <unknown> ({:?})", error.cause.reason);
    }
    eprintln!(
        "  while checking: {} <: {}",
        format_infer_pos(state, error.pos),
        format_infer_neg(state, error.neg)
    );
    if let Some(context) = infer_error_expected_context(state, error) {
        eprintln!("  context: {}", context.summary);
        if let Some(edge) = context.edge {
            eprintln!("  from edge: {edge}");
        }
        if let Some(detail) = context.detail {
            eprintln!("  detail: {detail}");
        }
    }
    for origin in &error.origins {
        match origin.span {
            Some(span) => {
                let (line, col) = line_col(source, u32::from(span.start()) as usize);
                if let Some(label) = &origin.label {
                    eprintln!("  generated at {line}:{col}: {:?} `{label}`", origin.kind);
                } else {
                    eprintln!("  generated at {line}:{col}: {:?}", origin.kind);
                }
            }
            None => {
                if let Some(label) = &origin.label {
                    eprintln!("  generated at <unknown>: {:?} `{label}`", origin.kind);
                } else {
                    eprintln!("  generated at <unknown>: {:?}", origin.kind);
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct InferExpectedContext {
    summary: String,
    edge: Option<String>,
    detail: Option<String>,
}

fn infer_error_expected_context(
    state: &InferLowerState,
    error: &InferTypeError,
) -> Option<InferExpectedContext> {
    let error_vars = yulang_infer::diagnostic::type_error_vars(&state.infer, error);
    let edge = state
        .expected_edges
        .iter()
        .filter(|edge| infer_expected_edge_is_diagnostic_context(edge.kind))
        .filter_map(|edge| {
            let rank = infer_expected_edge_error_rank(edge, error, &error_vars);
            (rank.score > 0).then_some((rank, edge))
        })
        .max_by_key(|(rank, _)| *rank)
        .map(|(_, edge)| edge)?;

    let detail = infer_error_derived_expected_context(state, error, edge);
    Some(InferExpectedContext {
        summary: format!(
            "{} expected {}; expression provides {}",
            infer_expected_edge_context_label(edge.kind),
            format_infer_neg(state, error.neg),
            format_infer_pos(state, error.pos),
        ),
        edge: Some(infer_expected_edge_flow_context(state, edge)),
        detail,
    })
}

fn infer_error_derived_expected_context(
    state: &InferLowerState,
    error: &InferTypeError,
    parent: &InferExpectedEdge,
) -> Option<String> {
    let actual = format_infer_pos(state, error.pos);
    let expected = format_infer_neg(state, error.neg);
    yulang_infer::collect_derived_expected_edge_evidence(state)
        .into_iter()
        .filter(|edge| edge.parent == parent.id)
        .filter_map(|edge| {
            let rank = infer_derived_expected_edge_error_rank(&edge, &actual, &expected);
            Some((rank, edge))
        })
        .max_by_key(|(rank, edge)| (*rank, edge.path.len()))
        .map(|(_, edge)| format_derived_expected_edge_context(&edge))
}

fn infer_derived_expected_edge_error_rank(
    edge: &yulang_infer::DerivedExpectedEdgeEvidence,
    actual: &str,
    expected: &str,
) -> u8 {
    let mut rank = 1;
    if format_core_bounds(&edge.actual) == actual {
        rank += 3;
    }
    if format_core_bounds(&edge.expected) == expected {
        rank += 3;
    }
    rank
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct InferExpectedEdgeRank {
    score: u8,
    span_match: bool,
    reason_match: bool,
    kind_priority: u8,
    shorter_span: Reverse<u32>,
}

fn infer_expected_edge_error_rank(
    edge: &InferExpectedEdge,
    error: &InferTypeError,
    error_vars: &[yulang_infer::TypeVar],
) -> InferExpectedEdgeRank {
    let mut score = 0;
    if error_vars.contains(&edge.actual_tv) {
        score += 3;
    }
    if error_vars.contains(&edge.expected_tv) {
        score += 3;
    }
    if edge
        .actual_eff
        .is_some_and(|actual_eff| error_vars.contains(&actual_eff))
    {
        score += 3;
    }
    if edge
        .expected_eff
        .is_some_and(|expected_eff| error_vars.contains(&expected_eff))
    {
        score += 3;
    }
    let span_match = edge.cause.span == error.cause.span;
    if span_match {
        score += 2;
    }
    let reason_match = edge.cause.reason == error.cause.reason;
    if reason_match {
        score += 1;
    }
    InferExpectedEdgeRank {
        score,
        span_match,
        reason_match,
        kind_priority: infer_expected_edge_kind_priority(edge.kind),
        shorter_span: Reverse(infer_expected_edge_span_len(edge)),
    }
}

fn infer_expected_edge_is_diagnostic_context(kind: InferExpectedEdgeKind) -> bool {
    matches!(
        kind,
        InferExpectedEdgeKind::Annotation
            | InferExpectedEdgeKind::ApplicationArgument
            | InferExpectedEdgeKind::AssignmentValue
    )
}

fn infer_expected_edge_context_label(kind: InferExpectedEdgeKind) -> &'static str {
    match kind {
        InferExpectedEdgeKind::Annotation => "annotation",
        InferExpectedEdgeKind::ApplicationCallee => "function callee",
        InferExpectedEdgeKind::ApplicationArgument => "function argument",
        InferExpectedEdgeKind::AssignmentValue => "assignment value",
        _ => "context",
    }
}

fn format_expected_edge_evidence(evidence: &yulang_infer::ExpectedEdgeEvidence) -> String {
    let mut parts = vec![
        format!(
            "#{} {}",
            evidence.id.0,
            format_expected_edge_kind(evidence.kind)
        ),
        format!("actual={}", format_core_bounds(&evidence.actual)),
        format!("expected={}", format_core_bounds(&evidence.expected)),
    ];
    if let Some(actual_effect) = &evidence.actual_effect {
        parts.push(format!(
            "actual-effect={}",
            format_core_bounds(actual_effect)
        ));
    }
    if let Some(expected_effect) = &evidence.expected_effect {
        parts.push(format!(
            "expected-effect={}",
            format_core_bounds(expected_effect)
        ));
    }
    parts.push(format!("closed={}", evidence.closed));
    parts.push(format!("informative={}", evidence.informative));
    parts.push(format!("runtime-usable={}", evidence.runtime_usable));
    parts.join(" ")
}

fn format_expected_adapter_edge_evidence(
    evidence: &yulang_infer::ExpectedAdapterEdgeEvidence,
) -> String {
    let mut parts = vec![format!(
        "#{} {}",
        evidence.id.0,
        format_expected_adapter_edge_kind(evidence.kind)
    )];
    if let Some(source_expected_edge) = evidence.source_expected_edge {
        parts.push(format!("source-expected-edge=#{}", source_expected_edge.0));
    }
    if let Some(actual_value) = &evidence.actual_value {
        parts.push(format!("actual-value={}", format_core_bounds(actual_value)));
    }
    if let Some(expected_value) = &evidence.expected_value {
        parts.push(format!(
            "expected-value={}",
            format_core_bounds(expected_value)
        ));
    }
    if let Some(actual_effect) = &evidence.actual_effect {
        parts.push(format!(
            "actual-effect={}",
            format_core_bounds(actual_effect)
        ));
    }
    if let Some(expected_effect) = &evidence.expected_effect {
        parts.push(format!(
            "expected-effect={}",
            format_core_bounds(expected_effect)
        ));
    }
    parts.push(format!("closed={}", evidence.closed));
    parts.push(format!("informative={}", evidence.informative));
    parts.push(format!("runtime-usable={}", evidence.runtime_usable));
    parts.join(" ")
}

fn format_expected_adapter_edge_kind(kind: yulang_infer::ExpectedAdapterEdgeKind) -> &'static str {
    match kind {
        yulang_infer::ExpectedAdapterEdgeKind::EffectOperationArgument => {
            "effect-operation-argument"
        }
        yulang_infer::ExpectedAdapterEdgeKind::ValueToThunk => "value-to-thunk",
        yulang_infer::ExpectedAdapterEdgeKind::ThunkToValue => "thunk-to-value",
        yulang_infer::ExpectedAdapterEdgeKind::BindHere => "bind-here",
        yulang_infer::ExpectedAdapterEdgeKind::HandlerResidual => "handler-residual",
        yulang_infer::ExpectedAdapterEdgeKind::HandlerReturn => "handler-return",
        yulang_infer::ExpectedAdapterEdgeKind::ResumeArgument => "resume-argument",
    }
}

fn format_derived_expected_edge_evidence(
    evidence: &yulang_infer::DerivedExpectedEdgeEvidence,
) -> String {
    let mut parts = vec![
        format!(
            "parent=#{} {}",
            evidence.parent.0,
            format_derived_expected_edge_kind(evidence.kind)
        ),
        format!("polarity={}", format_edge_polarity(evidence.polarity)),
        format!("path={}", format_edge_path(&evidence.path)),
        format!("actual={}", format_core_bounds(&evidence.actual)),
        format!("expected={}", format_core_bounds(&evidence.expected)),
    ];
    parts.retain(|part| !part.is_empty());
    parts.join(" ")
}

fn format_derived_expected_edge_context(
    evidence: &yulang_infer::DerivedExpectedEdgeEvidence,
) -> String {
    format!(
        "{} {} polarity={} actual={} expected={}",
        format_derived_expected_edge_kind(evidence.kind),
        format_edge_path(&evidence.path),
        format_edge_polarity(evidence.polarity),
        format_core_bounds(&evidence.actual),
        format_core_bounds(&evidence.expected),
    )
}

fn format_edge_polarity(polarity: yulang_infer::EdgePolarity) -> &'static str {
    match polarity {
        yulang_infer::EdgePolarity::Covariant => "covariant",
        yulang_infer::EdgePolarity::Contravariant => "contravariant",
        yulang_infer::EdgePolarity::Invariant => "invariant",
    }
}

fn format_derived_expected_edge_kind(kind: yulang_infer::DerivedExpectedEdgeKind) -> &'static str {
    match kind {
        yulang_infer::DerivedExpectedEdgeKind::RecordField => "record-field",
        yulang_infer::DerivedExpectedEdgeKind::TupleItem => "tuple-item",
        yulang_infer::DerivedExpectedEdgeKind::VariantPayload => "variant-payload",
        yulang_infer::DerivedExpectedEdgeKind::FunctionParam => "function-param",
        yulang_infer::DerivedExpectedEdgeKind::FunctionReturn => "function-return",
    }
}

fn format_edge_path(path: &[yulang_infer::EdgePathSegment]) -> String {
    path.iter()
        .map(|segment| match segment {
            yulang_infer::EdgePathSegment::Field(name) => format!(".{}", name.0),
            yulang_infer::EdgePathSegment::TupleIndex(index) => format!("[{index}]"),
            yulang_infer::EdgePathSegment::VariantCase(name) => format!(":{}", name.0),
            yulang_infer::EdgePathSegment::PayloadIndex(index) => format!("({index})"),
            yulang_infer::EdgePathSegment::FunctionParam => ".param".to_string(),
            yulang_infer::EdgePathSegment::FunctionReturn => ".return".to_string(),
        })
        .collect::<Vec<_>>()
        .join("")
}

fn format_expected_edge_kind(kind: InferExpectedEdgeKind) -> &'static str {
    match kind {
        InferExpectedEdgeKind::IfCondition => "if-condition",
        InferExpectedEdgeKind::IfBranch => "if-branch",
        InferExpectedEdgeKind::MatchGuard => "match-guard",
        InferExpectedEdgeKind::MatchBranch => "match-branch",
        InferExpectedEdgeKind::CatchGuard => "catch-guard",
        InferExpectedEdgeKind::CatchBranch => "catch-branch",
        InferExpectedEdgeKind::ApplicationCallee => "application-callee",
        InferExpectedEdgeKind::ApplicationArgument => "application-argument",
        InferExpectedEdgeKind::Annotation => "annotation",
        InferExpectedEdgeKind::RecordField => "record-field",
        InferExpectedEdgeKind::VariantPayload => "variant-payload",
        InferExpectedEdgeKind::AssignmentValue => "assignment-value",
        InferExpectedEdgeKind::RepresentationCoerce => "representation-coerce",
    }
}

fn infer_expected_edge_kind_priority(kind: InferExpectedEdgeKind) -> u8 {
    match kind {
        InferExpectedEdgeKind::Annotation
        | InferExpectedEdgeKind::ApplicationArgument
        | InferExpectedEdgeKind::AssignmentValue => 4,
        InferExpectedEdgeKind::RepresentationCoerce => 2,
        _ => 1,
    }
}

fn infer_expected_edge_span_len(edge: &InferExpectedEdge) -> u32 {
    edge.cause
        .span
        .map(|span| u32::from(span.end()) - u32::from(span.start()))
        .unwrap_or(u32::MAX)
}

fn infer_expected_edge_flow_context(state: &InferLowerState, edge: &InferExpectedEdge) -> String {
    let actual = yulang_infer::export::types::export_coalesced_type_bounds_for_tv(
        &state.infer,
        edge.actual_tv,
    );
    let expected = yulang_infer::export::types::export_coalesced_type_bounds_for_tv(
        &state.infer,
        edge.expected_tv,
    );
    let mut parts = vec![format!(
        "#{} {} {} {} => {} {}",
        edge.id.0,
        format_expected_edge_kind(edge.kind),
        infer_expected_edge_actual_label(edge.kind),
        format_core_bounds(&actual),
        infer_expected_edge_expected_label(edge.kind),
        format_core_bounds(&expected),
    )];
    if let (Some(actual_eff), Some(expected_eff)) = (edge.actual_eff, edge.expected_eff) {
        let actual_eff = yulang_infer::export::types::export_coalesced_type_bounds_for_tv(
            &state.infer,
            actual_eff,
        );
        let expected_eff = yulang_infer::export::types::export_coalesced_type_bounds_for_tv(
            &state.infer,
            expected_eff,
        );
        parts.push(format!(
            "effect {} => {}",
            format_core_bounds(&actual_eff),
            format_core_bounds(&expected_eff),
        ));
    }
    parts.join("; ")
}

fn infer_expected_edge_actual_label(kind: InferExpectedEdgeKind) -> &'static str {
    match kind {
        InferExpectedEdgeKind::ApplicationCallee => "callee actual",
        InferExpectedEdgeKind::ApplicationArgument => "argument actual",
        InferExpectedEdgeKind::Annotation => "expression actual",
        InferExpectedEdgeKind::AssignmentValue => "value actual",
        _ => "actual",
    }
}

fn infer_expected_edge_expected_label(kind: InferExpectedEdgeKind) -> &'static str {
    match kind {
        InferExpectedEdgeKind::ApplicationCallee => "callable",
        InferExpectedEdgeKind::ApplicationArgument => "parameter",
        InferExpectedEdgeKind::Annotation => "annotation",
        InferExpectedEdgeKind::AssignmentValue => "reference slot",
        _ => "expected",
    }
}

fn print_infer_surface_diagnostic(diagnostic: &InferSurfaceDiagnostic, source: &str) {
    eprintln!("error: {}", diagnostic.message);
    if let Some(span) = diagnostic.span {
        let (line, col) = line_col(source, u32::from(span.start()) as usize);
        eprintln!("  at {line}:{col}");
    } else {
        eprintln!("  at <unknown>");
    }
}

fn print_infer_program(program: &core_ir::CoreProgram, verbose: bool) {
    print_core_ir_module(&program.program);
    print_infer_graph(&program.graph, verbose);
    print_core_principal_evidence(&program.evidence, verbose);
}

fn print_core_ir_module(module: &core_ir::PrincipalModule) {
    let (visible_bindings, hidden_std_bindings): (Vec<_>, Vec<_>) = module
        .bindings
        .iter()
        .partition(|binding| !is_std_prelude_path(&binding.name));
    if !visible_bindings.is_empty() {
        println!("bindings:");
        for binding in visible_bindings {
            print_core_ir_binding(binding);
        }
    }
    if !hidden_std_bindings.is_empty() {
        println!(
            "  [hidden {} std/prelude bindings]",
            hidden_std_bindings.len()
        );
    }
    if !module.root_exprs.is_empty() {
        println!("roots:");
        for (index, expr) in module.root_exprs.iter().enumerate() {
            println!("  [{index}] {}", format_core_expr(expr));
        }
    }
}

fn print_infer_graph(graph: &core_ir::CoreGraphView, verbose: bool) {
    if graph.bindings.is_empty() && graph.root_exprs.is_empty() && graph.runtime_symbols.is_empty()
    {
        return;
    }
    println!("graph:");
    if !verbose {
        println!(
            "  {} binding nodes, {} root nodes, {} runtime symbols (use --verbose-ir for details)",
            graph.bindings.len(),
            graph.root_exprs.len(),
            graph.runtime_symbols.len()
        );
        return;
    }
    if !graph.runtime_symbols.is_empty() {
        println!("  runtime symbols:");
        for symbol in &graph.runtime_symbols {
            println!(
                "    {} :: {}",
                format_core_path(&symbol.path),
                format_runtime_symbol_kind(symbol.kind)
            );
        }
    }
    if !graph.bindings.is_empty() {
        println!("  binding bounds:");
        for node in &graph.bindings {
            let scheme = format_core_type(&node.scheme_body);
            let body = format_core_bounds(&node.body_bounds);
            if bounds_exact_type(&node.body_bounds).is_some_and(|ty| ty == &node.scheme_body) {
                println!("    {} :: {}", format_core_path(&node.binding), scheme);
            } else {
                println!(
                    "    {} :: {} ; body={}",
                    format_core_path(&node.binding),
                    scheme,
                    body
                );
            }
        }
    }
    if !graph.root_exprs.is_empty() {
        println!("  root bounds:");
        for node in &graph.root_exprs {
            let bounds = format_core_bounds(&node.bounds);
            if let Some(exact) = bounds_exact_type(&node.bounds) {
                println!(
                    "    {} :: {}",
                    format_graph_owner(&node.owner),
                    format_core_type(exact)
                );
            } else {
                println!("    {} :: {}", format_graph_owner(&node.owner), bounds);
            }
        }
    }
}

fn print_core_principal_evidence(evidence: &core_ir::PrincipalEvidence, verbose: bool) {
    if evidence.expected_edges.is_empty()
        && evidence.expected_adapter_edges.is_empty()
        && evidence.derived_expected_edges.is_empty()
    {
        return;
    }
    println!("principal-evidence:");
    if !verbose {
        println!(
            "  {} expected edges, {} expected adapter edges, {} derived expected edges (use --verbose-ir for details)",
            evidence.expected_edges.len(),
            evidence.expected_adapter_edges.len(),
            evidence.derived_expected_edges.len(),
        );
        return;
    }
    if !evidence.expected_edges.is_empty() {
        println!("  expected edges:");
        for edge in &evidence.expected_edges {
            println!("    {}", format_core_expected_edge_evidence(edge));
        }
    }
    if !evidence.expected_adapter_edges.is_empty() {
        println!("  expected adapter edges:");
        for edge in &evidence.expected_adapter_edges {
            println!("    {}", format_core_expected_adapter_edge_evidence(edge));
        }
    }
    if !evidence.derived_expected_edges.is_empty() {
        println!("  derived expected edges:");
        for edge in &evidence.derived_expected_edges {
            println!("    {}", format_core_derived_expected_edge_evidence(edge));
        }
    }
}

fn format_core_expected_edge_evidence(evidence: &core_ir::ExpectedEdgeEvidence) -> String {
    let mut parts = vec![
        format!(
            "#{} {}",
            evidence.id,
            format_core_expected_edge_kind(evidence.kind)
        ),
        format!("actual={}", format_core_bounds(&evidence.actual)),
        format!("expected={}", format_core_bounds(&evidence.expected)),
    ];
    if let Some(actual_effect) = &evidence.actual_effect {
        parts.push(format!(
            "actual-effect={}",
            format_core_bounds(actual_effect)
        ));
    }
    if let Some(expected_effect) = &evidence.expected_effect {
        parts.push(format!(
            "expected-effect={}",
            format_core_bounds(expected_effect)
        ));
    }
    parts.push(format!("closed={}", evidence.closed));
    parts.push(format!("informative={}", evidence.informative));
    parts.push(format!("runtime-usable={}", evidence.runtime_usable));
    parts.join(" ")
}

fn format_core_expected_adapter_edge_evidence(
    evidence: &core_ir::ExpectedAdapterEdgeEvidence,
) -> String {
    let mut parts = vec![format!(
        "#{} {}",
        evidence.id,
        format_core_expected_adapter_edge_kind(evidence.kind)
    )];
    if let Some(source_expected_edge) = evidence.source_expected_edge {
        parts.push(format!("source-expected-edge=#{source_expected_edge}"));
    }
    if let Some(actual_value) = &evidence.actual_value {
        parts.push(format!("actual-value={}", format_core_bounds(actual_value)));
    }
    if let Some(expected_value) = &evidence.expected_value {
        parts.push(format!(
            "expected-value={}",
            format_core_bounds(expected_value)
        ));
    }
    if let Some(actual_effect) = &evidence.actual_effect {
        parts.push(format!(
            "actual-effect={}",
            format_core_bounds(actual_effect)
        ));
    }
    if let Some(expected_effect) = &evidence.expected_effect {
        parts.push(format!(
            "expected-effect={}",
            format_core_bounds(expected_effect)
        ));
    }
    parts.push(format!("closed={}", evidence.closed));
    parts.push(format!("informative={}", evidence.informative));
    parts.push(format!("runtime-usable={}", evidence.runtime_usable));
    parts.join(" ")
}

fn format_core_derived_expected_edge_evidence(
    evidence: &core_ir::DerivedExpectedEdgeEvidence,
) -> String {
    let mut parts = vec![
        format!(
            "parent=#{} {}",
            evidence.parent,
            format_core_derived_expected_edge_kind(evidence.kind)
        ),
        format!("polarity={}", format_core_edge_polarity(evidence.polarity)),
        format!("path={}", format_core_edge_path(&evidence.path)),
        format!("actual={}", format_core_bounds(&evidence.actual)),
        format!("expected={}", format_core_bounds(&evidence.expected)),
    ];
    parts.retain(|part| !part.is_empty());
    parts.join(" ")
}

fn format_core_expected_edge_kind(kind: core_ir::ExpectedEdgeKind) -> &'static str {
    match kind {
        core_ir::ExpectedEdgeKind::IfCondition => "if-condition",
        core_ir::ExpectedEdgeKind::IfBranch => "if-branch",
        core_ir::ExpectedEdgeKind::MatchGuard => "match-guard",
        core_ir::ExpectedEdgeKind::MatchBranch => "match-branch",
        core_ir::ExpectedEdgeKind::CatchGuard => "catch-guard",
        core_ir::ExpectedEdgeKind::CatchBranch => "catch-branch",
        core_ir::ExpectedEdgeKind::ApplicationCallee => "application-callee",
        core_ir::ExpectedEdgeKind::ApplicationArgument => "application-argument",
        core_ir::ExpectedEdgeKind::Annotation => "annotation",
        core_ir::ExpectedEdgeKind::RecordField => "record-field",
        core_ir::ExpectedEdgeKind::VariantPayload => "variant-payload",
        core_ir::ExpectedEdgeKind::AssignmentValue => "assignment-value",
        core_ir::ExpectedEdgeKind::RepresentationCoerce => "representation-coerce",
    }
}

fn format_core_edge_polarity(polarity: core_ir::EdgePolarity) -> &'static str {
    match polarity {
        core_ir::EdgePolarity::Covariant => "covariant",
        core_ir::EdgePolarity::Contravariant => "contravariant",
        core_ir::EdgePolarity::Invariant => "invariant",
    }
}

fn format_core_derived_expected_edge_kind(kind: core_ir::DerivedExpectedEdgeKind) -> &'static str {
    match kind {
        core_ir::DerivedExpectedEdgeKind::RecordField => "record-field",
        core_ir::DerivedExpectedEdgeKind::TupleItem => "tuple-item",
        core_ir::DerivedExpectedEdgeKind::VariantPayload => "variant-payload",
        core_ir::DerivedExpectedEdgeKind::FunctionParam => "function-param",
        core_ir::DerivedExpectedEdgeKind::FunctionReturn => "function-return",
    }
}

fn format_core_edge_path(path: &[core_ir::EdgePathSegment]) -> String {
    path.iter()
        .map(|segment| match segment {
            core_ir::EdgePathSegment::Field(name) => format!(".{}", name.0),
            core_ir::EdgePathSegment::TupleIndex(index) => format!("[{index}]"),
            core_ir::EdgePathSegment::VariantCase(name) => format!(":{}", name.0),
            core_ir::EdgePathSegment::PayloadIndex(index) => format!("({index})"),
            core_ir::EdgePathSegment::FunctionParam => ".param".to_string(),
            core_ir::EdgePathSegment::FunctionReturn => ".return".to_string(),
        })
        .collect::<Vec<_>>()
        .join("")
}

fn format_core_expected_adapter_edge_kind(kind: core_ir::ExpectedAdapterEdgeKind) -> &'static str {
    match kind {
        core_ir::ExpectedAdapterEdgeKind::EffectOperationArgument => "effect-operation-argument",
        core_ir::ExpectedAdapterEdgeKind::ValueToThunk => "value-to-thunk",
        core_ir::ExpectedAdapterEdgeKind::ThunkToValue => "thunk-to-value",
        core_ir::ExpectedAdapterEdgeKind::BindHere => "bind-here",
        core_ir::ExpectedAdapterEdgeKind::HandlerResidual => "handler-residual",
        core_ir::ExpectedAdapterEdgeKind::HandlerReturn => "handler-return",
        core_ir::ExpectedAdapterEdgeKind::ResumeArgument => "resume-argument",
    }
}

fn format_runtime_symbol_kind(kind: core_ir::RuntimeSymbolKind) -> &'static str {
    match kind {
        core_ir::RuntimeSymbolKind::Value => "value",
        core_ir::RuntimeSymbolKind::RoleMethod => "role-method",
        core_ir::RuntimeSymbolKind::EffectOperation => "effect-op",
    }
}

fn print_core_ir_binding(binding: &core_ir::PrincipalBinding) {
    println!("  {}", format_core_path(&binding.name));
    println!("    : {}", format_core_scheme(&binding.scheme));
    println!("    = {}", format_core_expr(&binding.body));
}

fn print_runtime_module(module: &runtime::Module, verbose: bool) {
    if !module.bindings.is_empty() {
        println!("bindings:");
        for binding in &module.bindings {
            print_runtime_binding(binding, verbose);
        }
    }
    if !module.root_exprs.is_empty() {
        println!("roots:");
        for (index, expr) in module.root_exprs.iter().enumerate() {
            println!("  [{index}] {}", format_runtime_typed_expr(expr, verbose));
        }
    }
}

fn print_runtime_binding(binding: &runtime::Binding, verbose: bool) {
    println!("  {}", format_core_path(&binding.name));
    if verbose {
        println!("    principal: {}", format_core_scheme(&binding.scheme));
    }
    if !binding.type_params.is_empty() {
        let params = binding
            .type_params
            .iter()
            .map(|param| param.0.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        println!("    forall {params}");
    }
    println!("    runtime: {}", format_runtime_type(&binding.body.ty));
    println!(
        "    = {}",
        format_runtime_typed_expr(&binding.body, verbose)
    );
}

fn format_runtime_vm_result(result: &runtime::VmResult) -> String {
    match result {
        runtime::VmResult::Value(value) => format_runtime_vm_value(value),
        runtime::VmResult::Request(request) => format!(
            "request {} {} blocked={:?}",
            format_core_path(&request.effect),
            format_runtime_vm_value(&request.payload),
            request.blocked_id
        ),
    }
}

fn format_runtime_vm_value(value: &runtime::VmValue) -> String {
    match value {
        runtime::VmValue::Int(value) | runtime::VmValue::Float(value) => value.clone(),
        runtime::VmValue::String(value) => format!("{:?}", value.to_flat_string()),
        runtime::VmValue::Bool(value) => value.to_string(),
        runtime::VmValue::Unit => "()".to_string(),
        runtime::VmValue::List(items) => format!(
            "[{}]",
            items
                .to_vec()
                .iter()
                .map(format_runtime_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        runtime::VmValue::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(format_runtime_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        runtime::VmValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, value)| format!("{} = {}", name.0, format_runtime_vm_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        runtime::VmValue::Variant { tag, value } => match value {
            Some(value) => format!("{} {}", tag.0, format_runtime_vm_value(value)),
            None => tag.0.clone(),
        },
        runtime::VmValue::EffectOp(path) => format!("<effect-op {}>", format_core_path(path)),
        runtime::VmValue::PrimitiveOp(_) => "<primitive>".to_string(),
        runtime::VmValue::Resume(_) => "<resume>".to_string(),
        runtime::VmValue::Closure(_) => "<closure>".to_string(),
        runtime::VmValue::Thunk(_) => "<thunk>".to_string(),
        runtime::VmValue::EffectId(id) => format!("<effect-id {id}>"),
    }
}

fn format_primitive_op(op: core_ir::PrimitiveOp) -> &'static str {
    match op {
        core_ir::PrimitiveOp::BoolNot => "std::bool::not",
        core_ir::PrimitiveOp::BoolEq => "std::bool::eq",
        core_ir::PrimitiveOp::ListEmpty => "std::list::empty",
        core_ir::PrimitiveOp::ListSingleton => "std::list::singleton",
        core_ir::PrimitiveOp::ListLen => "std::list::len",
        core_ir::PrimitiveOp::ListMerge => "std::list::merge",
        core_ir::PrimitiveOp::ListIndex => "std::list::index_raw",
        core_ir::PrimitiveOp::ListIndexRange => "std::list::index_range",
        core_ir::PrimitiveOp::ListSplice => "std::list::splice",
        core_ir::PrimitiveOp::ListIndexRangeRaw => "std::list::index_range_raw",
        core_ir::PrimitiveOp::ListSpliceRaw => "std::list::splice_raw",
        core_ir::PrimitiveOp::ListViewRaw => "std::list::view_raw",
        core_ir::PrimitiveOp::StringLen => "std::str::len",
        core_ir::PrimitiveOp::StringIndex => "std::str::index_raw",
        core_ir::PrimitiveOp::StringIndexRange => "std::str::index_range",
        core_ir::PrimitiveOp::StringSplice => "std::str::splice",
        core_ir::PrimitiveOp::StringIndexRangeRaw => "std::str::index_range_raw",
        core_ir::PrimitiveOp::StringSpliceRaw => "std::str::splice_raw",
        core_ir::PrimitiveOp::IntAdd => "std::int::add",
        core_ir::PrimitiveOp::IntSub => "std::int::sub",
        core_ir::PrimitiveOp::IntMul => "std::int::mul",
        core_ir::PrimitiveOp::IntDiv => "std::int::div",
        core_ir::PrimitiveOp::IntEq => "std::int::eq",
        core_ir::PrimitiveOp::IntLt => "std::int::lt",
        core_ir::PrimitiveOp::IntLe => "std::int::le",
        core_ir::PrimitiveOp::IntGt => "std::int::gt",
        core_ir::PrimitiveOp::IntGe => "std::int::ge",
        core_ir::PrimitiveOp::FloatAdd => "std::float::add",
        core_ir::PrimitiveOp::FloatSub => "std::float::sub",
        core_ir::PrimitiveOp::FloatMul => "std::float::mul",
        core_ir::PrimitiveOp::FloatDiv => "std::float::div",
        core_ir::PrimitiveOp::FloatEq => "std::float::eq",
        core_ir::PrimitiveOp::FloatLt => "std::float::lt",
        core_ir::PrimitiveOp::FloatLe => "std::float::le",
        core_ir::PrimitiveOp::FloatGt => "std::float::gt",
        core_ir::PrimitiveOp::FloatGe => "std::float::ge",
        core_ir::PrimitiveOp::StringConcat => "std::str::concat",
        core_ir::PrimitiveOp::IntToString => "std::int::to_string",
        core_ir::PrimitiveOp::IntToHex => "std::int::to_hex",
        core_ir::PrimitiveOp::IntToUpperHex => "std::int::to_upper_hex",
        core_ir::PrimitiveOp::FloatToString => "std::float::to_string",
        core_ir::PrimitiveOp::BoolToString => "std::bool::to_string",
    }
}

fn format_core_scheme(scheme: &core_ir::Scheme) -> String {
    if scheme.requirements.is_empty() {
        format_core_type(&scheme.body)
    } else {
        let requirements = scheme
            .requirements
            .iter()
            .map(format_core_requirement)
            .collect::<Vec<_>>()
            .join(", ");
        format!("{requirements} => {}", format_core_type(&scheme.body))
    }
}

fn format_core_requirement(requirement: &core_ir::RoleRequirement) -> String {
    let args = requirement
        .args
        .iter()
        .map(format_core_requirement_arg)
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}<{args}>", format_core_path(&requirement.role))
}

fn format_core_requirement_arg(arg: &core_ir::RoleRequirementArg) -> String {
    match arg {
        core_ir::RoleRequirementArg::Input(bounds) => format_core_bounds(bounds),
        core_ir::RoleRequirementArg::Associated { name, bounds } => {
            format!("{} = {}", name.0, format_core_bounds(bounds))
        }
    }
}

fn format_core_bounds(bounds: &core_ir::TypeBounds) -> String {
    match (&bounds.lower, &bounds.upper) {
        (Some(lower), Some(upper)) if lower == upper => format_core_type(lower),
        (Some(lower), Some(upper)) => {
            format!(
                "{} <: _ <: {}",
                format_core_type(lower),
                format_core_type(upper)
            )
        }
        (Some(lower), None) => format!("{} <: _", format_core_type(lower)),
        (None, Some(upper)) => format!("_ <: {}", format_core_type(upper)),
        (None, None) => "_".to_string(),
    }
}

fn bounds_exact_type(bounds: &core_ir::TypeBounds) -> Option<&core_ir::Type> {
    match (&bounds.lower, &bounds.upper) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower),
        _ => None,
    }
}

fn format_graph_owner(owner: &core_ir::GraphOwner) -> String {
    match owner {
        core_ir::GraphOwner::RootExpr(index) => format!("root[{index}]"),
    }
}

fn format_core_type(ty: &core_ir::Type) -> String {
    match ty {
        core_ir::Type::Never => "⊥".to_string(),
        core_ir::Type::Any => "⊤".to_string(),
        core_ir::Type::Var(var) => var.0.clone(),
        core_ir::Type::Named { path, args } => {
            let head = format_core_path(path);
            if args.is_empty() {
                head
            } else {
                let args = args
                    .iter()
                    .map(format_core_type_arg)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{head}<{args}>")
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            if is_implicit_fun_effect(param_effect, ret_effect) {
                format!(
                    "{} -> {}",
                    format_core_fun_side(param),
                    format_core_type(ret)
                )
            } else {
                format!(
                    "{} -{} / {}-> {}",
                    format_core_fun_side(param),
                    format_core_type(param_effect),
                    format_core_type(ret_effect),
                    format_core_type(ret)
                )
            }
        }
        core_ir::Type::Tuple(items) => {
            let items = items
                .iter()
                .map(format_core_type)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        core_ir::Type::Record(record) => format_core_record_type(record),
        core_ir::Type::Variant(variant) => format_core_variant_type(variant),
        core_ir::Type::Row { items, tail } => format_core_row_type(items, tail),
        core_ir::Type::Union(items) => items
            .iter()
            .map(format_core_type)
            .collect::<Vec<_>>()
            .into_iter()
            .fold(Vec::<String>::new(), |mut acc, item| {
                if !acc.contains(&item) {
                    acc.push(item);
                }
                acc
            })
            .join(" | "),
        core_ir::Type::Inter(items) => items
            .iter()
            .map(format_core_type)
            .collect::<Vec<_>>()
            .into_iter()
            .fold(Vec::<String>::new(), |mut acc, item| {
                if !acc.contains(&item) {
                    acc.push(item);
                }
                acc
            })
            .join(" & "),
        core_ir::Type::Recursive { var, body } => {
            format!("rec {}. {}", var.0, format_core_type(body))
        }
    }
}

fn format_core_type_arg(arg: &core_ir::TypeArg) -> String {
    match arg {
        core_ir::TypeArg::Type(ty) => format_core_type(ty),
        core_ir::TypeArg::Bounds(bounds) => format_core_bounds(bounds),
    }
}

fn format_core_record_type(record: &core_ir::RecordType) -> String {
    let mut items = record
        .fields
        .iter()
        .map(|field| {
            let optional = if field.optional { "?" } else { "" };
            format!(
                "{}{}: {}",
                field.name.0,
                optional,
                format_core_type(&field.value)
            )
        })
        .collect::<Vec<_>>();
    if let Some(spread) = &record.spread {
        items.push(format_core_record_spread_type(spread));
    }
    format!("{{{}}}", items.join(", "))
}

fn format_core_record_spread_type(spread: &core_ir::RecordSpread) -> String {
    match spread {
        core_ir::RecordSpread::Head(ty) => format!("..{}", format_core_type(ty)),
        core_ir::RecordSpread::Tail(ty) => format!("{}..", format_core_type(ty)),
    }
}

fn format_core_variant_type(variant: &core_ir::VariantType) -> String {
    let mut items = variant
        .cases
        .iter()
        .map(|case| {
            if case.payloads.is_empty() {
                case.name.0.clone()
            } else {
                let payloads = case
                    .payloads
                    .iter()
                    .map(format_core_type)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({payloads})", case.name.0)
            }
        })
        .collect::<Vec<_>>();
    if let Some(tail) = &variant.tail {
        items.push(format!("..{}", format_core_type(tail)));
    }
    format!(":[{}]", items.join(" | "))
}

fn format_core_row_type(items: &[core_ir::Type], tail: &core_ir::Type) -> String {
    let mut parts = Vec::new();
    flatten_core_row_parts(items, tail, &mut parts);
    match parts.as_slice() {
        [] => "[]".to_string(),
        [single] => single.clone(),
        _ => format!("[{}]", parts.join("; ")),
    }
}

fn flatten_core_row_parts(items: &[core_ir::Type], tail: &core_ir::Type, parts: &mut Vec<String>) {
    parts.extend(items.iter().map(format_core_type));
    match tail {
        core_ir::Type::Never => {}
        core_ir::Type::Row { items, tail } => flatten_core_row_parts(items, tail, parts),
        other => parts.push(format_core_type(other)),
    }
}

fn format_core_fun_side(ty: &core_ir::Type) -> String {
    match ty {
        core_ir::Type::Fun { .. } => format!("({})", format_core_type(ty)),
        _ => format_core_type(ty),
    }
}

fn format_core_expr(expr: &core_ir::Expr) -> String {
    match expr {
        core_ir::Expr::Var(path) => format_core_path(path),
        core_ir::Expr::PrimitiveOp(op) => format!("<primitive {}>", format_primitive_op(*op)),
        core_ir::Expr::Lit(lit) => format_core_lit(lit),
        core_ir::Expr::Lambda { param, body, .. } => {
            format!("fun {} -> {}", param.0, format_core_expr(body))
        }
        core_ir::Expr::Apply {
            callee,
            arg,
            evidence,
        } => {
            let mut text = format!(
                "{} {}",
                format_core_expr_atom(callee),
                format_core_expr_atom(arg)
            );
            if let Some(evidence) = evidence {
                text.push_str(&format!(" :: {}", format_apply_evidence(evidence)));
            }
            text
        }
        core_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            let mut text = format!(
                "if {} then {} else {}",
                format_core_expr(cond),
                format_core_expr(then_branch),
                format_core_expr(else_branch)
            );
            if let Some(evidence) = evidence {
                text.push_str(&format!(" :: {}", format_join_evidence(evidence)));
            }
            text
        }
        core_ir::Expr::Tuple(items) => {
            let items = items
                .iter()
                .map(format_core_expr)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        core_ir::Expr::Record { fields, spread } => {
            let mut items = fields
                .iter()
                .map(|field| format!("{}: {}", field.name.0, format_core_expr(&field.value)))
                .collect::<Vec<_>>();
            if let Some(spread) = spread {
                items.push(format_core_record_spread_expr(spread));
            }
            format!("{{{}}}", items.join(", "))
        }
        core_ir::Expr::Variant { tag, value } => match value {
            Some(value) => format!(":{} {}", tag.0, format_core_expr_atom(value)),
            None => format!(":{}", tag.0),
        },
        core_ir::Expr::Select { base, field } => {
            format!("{}.{}", format_core_expr_atom(base), field.0)
        }
        core_ir::Expr::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            let arms = arms
                .iter()
                .map(format_core_match_arm)
                .collect::<Vec<_>>()
                .join(" | ");
            let mut text = format!("case {}: {}", format_core_expr(scrutinee), arms);
            if let Some(evidence) = evidence {
                text.push_str(&format!(" :: {}", format_join_evidence(evidence)));
            }
            text
        }
        core_ir::Expr::Block { stmts, tail } => {
            let mut parts = stmts.iter().map(format_core_stmt).collect::<Vec<_>>();
            if let Some(tail) = tail {
                parts.push(format_core_expr(tail));
            }
            format!("do {{ {} }}", parts.join("; "))
        }
        core_ir::Expr::Handle {
            body,
            arms,
            evidence,
        } => {
            let arms = arms
                .iter()
                .map(format_core_handle_arm)
                .collect::<Vec<_>>()
                .join(" | ");
            let mut text = format!("catch {}: {}", format_core_expr(body), arms);
            if let Some(evidence) = evidence {
                text.push_str(&format!(" :: {}", format_join_evidence(evidence)));
            }
            text
        }
        core_ir::Expr::Coerce { expr, evidence } => {
            let mut text = format!("coerce {}", format_core_expr_atom(expr));
            if let Some(evidence) = evidence {
                text.push_str(&format!(" :: {}", format_coerce_evidence(evidence)));
            }
            text
        }
        core_ir::Expr::Pack { var, expr } => {
            format!("pack {} in {}", var.0, format_core_expr(expr))
        }
    }
}

fn format_core_expr_atom(expr: &core_ir::Expr) -> String {
    match expr {
        core_ir::Expr::Var(_)
        | core_ir::Expr::Lit(_)
        | core_ir::Expr::Select { .. }
        | core_ir::Expr::Record { .. }
        | core_ir::Expr::Variant { .. } => format_core_expr(expr),
        _ => format!("({})", format_core_expr(expr)),
    }
}

fn format_core_record_spread_expr(spread: &core_ir::RecordSpreadExpr) -> String {
    match spread {
        core_ir::RecordSpreadExpr::Head(expr) => format!("..{}", format_core_expr(expr)),
        core_ir::RecordSpreadExpr::Tail(expr) => format!("{}..", format_core_expr(expr)),
    }
}

fn format_core_match_arm(arm: &core_ir::MatchArm) -> String {
    let guard = arm
        .guard
        .as_ref()
        .map(|guard| format!(" if {}", format_core_expr(guard)))
        .unwrap_or_default();
    format!(
        "{}{} -> {}",
        format_core_pattern(&arm.pattern),
        guard,
        format_core_expr(&arm.body)
    )
}

fn format_core_handle_arm(arm: &core_ir::HandleArm) -> String {
    let resume = arm
        .resume
        .as_ref()
        .map(|resume| format!(", {}", resume.0))
        .unwrap_or_default();
    let guard = arm
        .guard
        .as_ref()
        .map(|guard| format!(" if {}", format_core_expr(guard)))
        .unwrap_or_default();
    format!(
        "{} {}{}{} -> {}",
        format_core_path(&arm.effect),
        format_core_pattern(&arm.payload),
        resume,
        guard,
        format_core_expr(&arm.body)
    )
}

fn format_core_stmt(stmt: &core_ir::Stmt) -> String {
    match stmt {
        core_ir::Stmt::Let { pattern, value } => {
            format!(
                "let {} = {}",
                format_core_pattern(pattern),
                format_core_expr(value)
            )
        }
        core_ir::Stmt::Expr(expr) => format_core_expr(expr),
        core_ir::Stmt::Module { def, body } => {
            format!(
                "module {} = {}",
                format_core_path(def),
                format_core_expr(body)
            )
        }
    }
}

fn format_core_pattern(pattern: &core_ir::Pattern) -> String {
    match pattern {
        core_ir::Pattern::Wildcard => "_".to_string(),
        core_ir::Pattern::Bind(name) => name.0.clone(),
        core_ir::Pattern::Lit(lit) => format_core_lit(lit),
        core_ir::Pattern::Tuple(items) => {
            let items = items
                .iter()
                .map(format_core_pattern)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        core_ir::Pattern::List {
            prefix,
            spread,
            suffix,
        } => {
            let mut items = prefix.iter().map(format_core_pattern).collect::<Vec<_>>();
            if let Some(spread) = spread {
                items.push(format!("..{}", format_core_pattern(spread)));
            }
            items.extend(suffix.iter().map(format_core_pattern));
            format!("[{}]", items.join(", "))
        }
        core_ir::Pattern::Record { fields, spread } => {
            let mut items = fields
                .iter()
                .map(|field| match &field.default {
                    Some(default) if matches!(&field.pattern, core_ir::Pattern::Bind(name) if name == &field.name) => {
                        format!("{} = {}", field.name.0, format_core_expr(default))
                    }
                    Some(default) => format!(
                        "{}: {} = {}",
                        field.name.0,
                        format_core_pattern(&field.pattern),
                        format_core_expr(default)
                    ),
                    None => format!("{}: {}", field.name.0, format_core_pattern(&field.pattern)),
                })
                .collect::<Vec<_>>();
            if let Some(spread) = spread {
                items.push(format_core_record_spread_pattern(spread));
            }
            format!("{{{}}}", items.join(", "))
        }
        core_ir::Pattern::Variant { tag, value } => match value {
            Some(value) => format!(":{} {}", tag.0, format_core_pattern(value)),
            None => format!(":{}", tag.0),
        },
        core_ir::Pattern::Or { left, right } => {
            format!(
                "{} | {}",
                format_core_pattern(left),
                format_core_pattern(right)
            )
        }
        core_ir::Pattern::As { pattern, name } => {
            format!("{} as {}", format_core_pattern(pattern), name.0)
        }
    }
}

fn format_core_record_spread_pattern(spread: &core_ir::RecordSpreadPattern) -> String {
    match spread {
        core_ir::RecordSpreadPattern::Head(pattern) => {
            format!("..{}", format_core_pattern(pattern))
        }
        core_ir::RecordSpreadPattern::Tail(pattern) => {
            format!("{}..", format_core_pattern(pattern))
        }
    }
}

fn format_core_lit(lit: &core_ir::Lit) -> String {
    match lit {
        core_ir::Lit::Int(value) => value.clone(),
        core_ir::Lit::Float(value) => value.clone(),
        core_ir::Lit::String(value) => format!("{value:?}"),
        core_ir::Lit::Bool(value) => value.to_string(),
        core_ir::Lit::Unit => "()".to_string(),
    }
}

fn format_apply_evidence(evidence: &core_ir::ApplyEvidence) -> String {
    let mut out = format!(
        "apply[callee={}, arg={}, result={}]",
        format_core_bounds(&evidence.callee),
        format_core_bounds(&evidence.arg),
        format_core_bounds(&evidence.result)
    );
    if let Some(expected_callee) = &evidence.expected_callee {
        out.push_str(&format!(
            ", expected-callee={}",
            format_core_bounds(expected_callee)
        ));
    }
    if let Some(expected_arg) = &evidence.expected_arg {
        out.push_str(&format!(
            ", expected-arg={}",
            format_core_bounds(expected_arg)
        ));
    }
    if let Some(callee_source_edge) = evidence.callee_source_edge {
        out.push_str(&format!(", callee-source-edge={callee_source_edge}"));
    }
    if let Some(arg_source_edge) = evidence.arg_source_edge {
        out.push_str(&format!(", arg-source-edge={arg_source_edge}"));
    }
    if let Some(principal) = &evidence.principal_callee {
        out.push_str(&format!(", principal={}", format_core_type(principal)));
    }
    if !evidence.substitutions.is_empty() {
        let substitutions = evidence
            .substitutions
            .iter()
            .map(|substitution| {
                format!(
                    "{} := {}",
                    substitution.var.0,
                    format_core_type(&substitution.ty)
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(", subst=[{substitutions}]"));
    }
    if !evidence.substitution_candidates.is_empty() {
        let candidates = evidence
            .substitution_candidates
            .iter()
            .map(format_principal_substitution_candidate)
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(", subst-candidates=[{candidates}]"));
    }
    out
}

fn format_principal_substitution_candidate(
    candidate: &core_ir::PrincipalSubstitutionCandidate,
) -> String {
    let relation = match candidate.relation {
        core_ir::PrincipalCandidateRelation::Lower => "<=",
        core_ir::PrincipalCandidateRelation::Upper => ">=",
        core_ir::PrincipalCandidateRelation::Exact => "=",
    };
    let path = candidate
        .path
        .iter()
        .map(format_principal_slot_path_segment)
        .collect::<Vec<_>>()
        .join(".");
    let source = candidate
        .source_edge
        .map(|edge| format!(" edge#{edge}"))
        .unwrap_or_default();
    format!(
        "{} {} {} @{}{}",
        candidate.var.0,
        relation,
        format_core_type(&candidate.ty),
        path,
        source,
    )
}

fn format_principal_slot_path_segment(segment: &core_ir::PrincipalSlotPathSegment) -> String {
    match segment {
        core_ir::PrincipalSlotPathSegment::Callee => "callee".to_string(),
        core_ir::PrincipalSlotPathSegment::Arg => "arg".to_string(),
        core_ir::PrincipalSlotPathSegment::Result => "result".to_string(),
        core_ir::PrincipalSlotPathSegment::Field(name) => format!("field({})", name.0),
        core_ir::PrincipalSlotPathSegment::TupleIndex(index) => format!("tuple({index})"),
        core_ir::PrincipalSlotPathSegment::VariantCase(name) => format!("case({})", name.0),
        core_ir::PrincipalSlotPathSegment::PayloadIndex(index) => format!("payload({index})"),
        core_ir::PrincipalSlotPathSegment::FunctionParam => "param".to_string(),
        core_ir::PrincipalSlotPathSegment::FunctionReturn => "return".to_string(),
    }
}

fn format_join_evidence(evidence: &core_ir::JoinEvidence) -> String {
    format!("join[{}]", format_core_bounds(&evidence.result))
}

fn format_coerce_evidence(evidence: &core_ir::CoerceEvidence) -> String {
    let mut text = format!(
        "coerce[actual={}, expected={}]",
        format_core_bounds(&evidence.actual),
        format_core_bounds(&evidence.expected)
    );
    if let Some(source_edge) = evidence.source_edge {
        text.push_str(&format!(", source-edge={source_edge}"));
    }
    text
}

fn format_runtime_typed_expr(expr: &runtime::Expr, verbose: bool) -> String {
    format!(
        "{} : {}",
        format_runtime_expr(expr, verbose),
        format_runtime_type(&expr.ty)
    )
}

fn format_runtime_type(ty: &runtime::Type) -> String {
    match ty {
        runtime::Type::Core(ty) => format_runtime_core_type_inner(ty, true),
        runtime::Type::Fun { param, ret } => {
            format!(
                "{} -> {}",
                format_runtime_type_atom(param),
                format_runtime_type(ret)
            )
        }
        runtime::Type::Thunk { effect, value } => {
            format!(
                "Thunk[{}, {}]",
                format_core_type(effect),
                format_runtime_type(value)
            )
        }
    }
}

fn format_runtime_core_type(ty: &core_ir::Type) -> String {
    format_runtime_core_type_inner(ty, false)
}

fn format_runtime_core_type_inner(ty: &core_ir::Type, nested_fun_as_thunk: bool) -> String {
    match ty {
        core_ir::Type::Named { path, args } => {
            let head = format_core_path(path);
            if args.is_empty() {
                head
            } else {
                let args = args
                    .iter()
                    .map(format_runtime_core_type_arg)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{head}<{args}>")
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } if nested_fun_as_thunk => {
            let param = format_runtime_effected_core_value(param, param_effect, false);
            let ret = format_runtime_effected_core_value(ret, ret_effect, true);
            format!("{param} -> {ret}")
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            if is_implicit_fun_effect(param_effect, ret_effect) {
                format!(
                    "{} -> {}",
                    format_runtime_core_fun_side(param),
                    format_runtime_core_type_inner(ret, true)
                )
            } else {
                format!(
                    "{} -{} / {}-> {}",
                    format_runtime_core_fun_side(param),
                    format_core_type(param_effect),
                    format_core_type(ret_effect),
                    format_runtime_core_type_inner(ret, true)
                )
            }
        }
        core_ir::Type::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| format_runtime_core_type_inner(item, true))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        core_ir::Type::Record(record) => format_core_record_type(record),
        core_ir::Type::Variant(variant) => format_core_variant_type(variant),
        core_ir::Type::Union(items) => items
            .iter()
            .map(format_runtime_core_type)
            .collect::<Vec<_>>()
            .join(" | "),
        core_ir::Type::Inter(items) => items
            .iter()
            .map(format_runtime_core_type)
            .collect::<Vec<_>>()
            .join(" & "),
        other => format_core_type(other),
    }
}

fn format_runtime_core_type_arg(arg: &core_ir::TypeArg) -> String {
    match arg {
        core_ir::TypeArg::Type(ty) => format_runtime_core_type_inner(ty, true),
        core_ir::TypeArg::Bounds(bounds) => format_core_bounds(bounds),
    }
}

fn format_runtime_effected_core_value(
    value: &core_ir::Type,
    effect: &core_ir::Type,
    force_thunk: bool,
) -> String {
    let value = format_runtime_core_type_inner(value, true);
    if force_thunk || !is_empty_effect(effect) {
        format!("Thunk[{}, {}]", format_core_type(effect), value)
    } else {
        value
    }
}

fn format_runtime_core_fun_side(ty: &core_ir::Type) -> String {
    match ty {
        core_ir::Type::Fun { .. } => format!("({})", format_runtime_core_type(ty)),
        _ => format_runtime_core_type(ty),
    }
}

fn format_runtime_type_atom(ty: &runtime::Type) -> String {
    match ty {
        runtime::Type::Core(core_ir::Type::Fun { .. })
        | runtime::Type::Fun { .. }
        | runtime::Type::Thunk { .. } => format!("({})", format_runtime_type(ty)),
        _ => format_runtime_type(ty),
    }
}

fn format_runtime_expr(expr: &runtime::Expr, verbose: bool) -> String {
    match &expr.kind {
        runtime::ExprKind::Var(path) => format_core_path(path),
        runtime::ExprKind::EffectOp(path) => format!("<effect-op {}>", format_core_path(path)),
        runtime::ExprKind::PrimitiveOp(op) => format!("<primitive {}>", format_primitive_op(*op)),
        runtime::ExprKind::Lit(lit) => format_core_lit(lit),
        runtime::ExprKind::Lambda { param, body, .. } => {
            format!("fun {} -> {}", param.0, format_runtime_expr(body, verbose))
        }
        runtime::ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => {
            let mut text = format!(
                "{} {}",
                format_runtime_expr_atom(callee, verbose),
                format_runtime_expr_atom(arg, verbose)
            );
            if verbose && let Some(instantiation) = instantiation {
                text.push_str(&format!(
                    " :: {}",
                    format_runtime_type_instantiation(instantiation)
                ));
            }
            if verbose && let Some(evidence) = evidence {
                text.push_str(&format!(" :: {}", format_apply_evidence(evidence)));
            }
            text
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            let mut text = format!(
                "if {} then {} else {}",
                format_runtime_expr(cond, verbose),
                format_runtime_expr(then_branch, verbose),
                format_runtime_expr(else_branch, verbose)
            );
            if verbose {
                if let Some(evidence) = evidence {
                    text.push_str(&format!(" :: join[{}]", format_core_type(&evidence.result)));
                }
            }
            text
        }
        runtime::ExprKind::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| format_runtime_expr(item, verbose))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        runtime::ExprKind::Record { fields, spread } => {
            let mut items = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}: {}",
                        field.name.0,
                        format_runtime_expr(&field.value, verbose)
                    )
                })
                .collect::<Vec<_>>();
            if let Some(spread) = spread {
                items.push(format_runtime_record_spread_expr(spread, verbose));
            }
            format!("{{{}}}", items.join(", "))
        }
        runtime::ExprKind::Variant { tag, value } => match value {
            Some(value) => format!(":{} {}", tag.0, format_runtime_expr_atom(value, verbose)),
            None => format!(":{}", tag.0),
        },
        runtime::ExprKind::Select { base, field } => {
            format!("{}.{}", format_runtime_expr_atom(base, verbose), field.0)
        }
        runtime::ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            let arms = arms
                .iter()
                .map(|arm| format_runtime_match_arm(arm, verbose))
                .collect::<Vec<_>>()
                .join(" | ");
            let mut text = format!("case {}: {}", format_runtime_expr(scrutinee, verbose), arms);
            if verbose {
                text.push_str(&format!(" :: join[{}]", format_core_type(&evidence.result)));
            }
            text
        }
        runtime::ExprKind::Block { stmts, tail } => {
            let mut parts = stmts
                .iter()
                .map(|stmt| format_runtime_stmt(stmt, verbose))
                .collect::<Vec<_>>();
            if let Some(tail) = tail {
                parts.push(format_runtime_expr(tail, verbose));
            }
            format!("do {{ {} }}", parts.join("; "))
        }
        runtime::ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            let arms = arms
                .iter()
                .map(|arm| format_runtime_handle_arm(arm, verbose))
                .collect::<Vec<_>>()
                .join(" | ");
            let mut text = format!("catch {}: {}", format_runtime_expr(body, verbose), arms);
            if verbose {
                text.push_str(&format!(" :: join[{}]", format_core_type(&evidence.result)));
                text.push_str(&format!(" :: {}", format_runtime_handle_effect(handler)));
            }
            text
        }
        runtime::ExprKind::BindHere { expr } => {
            format!("bind_here {}", format_runtime_expr_atom(expr, verbose))
        }
        runtime::ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            format!(
                "thunk[{}, {}] {}",
                format_core_type(effect),
                format_runtime_type(value),
                format_runtime_expr_atom(expr, verbose)
            )
        }
        runtime::ExprKind::LocalPushId { id, body } => {
            format!(
                "local_push_id {} {}",
                format_runtime_effect_id_var(*id),
                format_runtime_expr_atom(body, verbose)
            )
        }
        runtime::ExprKind::PeekId => "peek_id".to_string(),
        runtime::ExprKind::FindId { id } => {
            format!("find_id {}", format_runtime_effect_id_ref(*id))
        }
        runtime::ExprKind::AddId { id, allowed, thunk } => {
            format!(
                "add_id[{}, {}] {}",
                format_runtime_effect_id_ref(*id),
                format_core_type(allowed),
                format_runtime_expr_atom(thunk, verbose)
            )
        }
        runtime::ExprKind::Coerce { from, to, expr } => {
            format!(
                "coerce[{} => {}] {}",
                format_core_type(from),
                format_core_type(to),
                format_runtime_expr_atom(expr, verbose)
            )
        }
        runtime::ExprKind::Pack { var, expr } => {
            format!("pack {} in {}", var.0, format_runtime_expr(expr, verbose))
        }
    }
}

fn format_runtime_expr_atom(expr: &runtime::Expr, verbose: bool) -> String {
    match &expr.kind {
        runtime::ExprKind::Var(_)
        | runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::Select { .. }
        | runtime::ExprKind::Record { .. }
        | runtime::ExprKind::Variant { .. } => format_runtime_expr(expr, verbose),
        _ => format!("({})", format_runtime_expr(expr, verbose)),
    }
}

fn format_runtime_effect_id_ref(id: runtime::EffectIdRef) -> String {
    match id {
        runtime::EffectIdRef::Var(var) => format_runtime_effect_id_var(var),
        runtime::EffectIdRef::Peek => "peek".to_string(),
    }
}

fn format_runtime_effect_id_var(id: runtime::EffectIdVar) -> String {
    format!("ae{}", id.0)
}

fn format_runtime_record_spread_expr(spread: &runtime::RecordSpreadExpr, verbose: bool) -> String {
    match spread {
        runtime::RecordSpreadExpr::Head(expr) => {
            format!("..{}", format_runtime_expr(expr, verbose))
        }
        runtime::RecordSpreadExpr::Tail(expr) => {
            format!("{}..", format_runtime_expr(expr, verbose))
        }
    }
}

fn format_runtime_type_instantiation(instantiation: &runtime::TypeInstantiation) -> String {
    let args = instantiation
        .args
        .iter()
        .map(|arg| format!("{} = {}", arg.var.0, format_core_type(&arg.ty)))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "inst[{}; {}]",
        format_core_path(&instantiation.target),
        args
    )
}

fn format_runtime_match_arm(arm: &runtime::MatchArm, verbose: bool) -> String {
    let guard = arm
        .guard
        .as_ref()
        .map(|guard| format!(" if {}", format_runtime_expr(guard, verbose)))
        .unwrap_or_default();
    format!(
        "{}{} -> {}",
        format_runtime_pattern(&arm.pattern),
        guard,
        format_runtime_expr(&arm.body, verbose)
    )
}

fn format_runtime_handle_arm(arm: &runtime::HandleArm, verbose: bool) -> String {
    let resume = arm
        .resume
        .as_ref()
        .map(|resume| {
            if verbose {
                format!(", {}: {}", resume.name.0, format_runtime_type(&resume.ty))
            } else {
                format!(", {}", resume.name.0)
            }
        })
        .unwrap_or_default();
    let guard = arm
        .guard
        .as_ref()
        .map(|guard| format!(" if {}", format_runtime_expr(guard, verbose)))
        .unwrap_or_default();
    format!(
        "{}({}{}){} -> {}",
        format_core_path(&arm.effect),
        format_runtime_pattern(&arm.payload),
        resume,
        guard,
        format_runtime_expr(&arm.body, verbose)
    )
}

fn format_runtime_handle_effect(effect: &runtime::HandleEffect) -> String {
    let consumes = effect
        .consumes
        .iter()
        .map(format_core_path)
        .collect::<Vec<_>>()
        .join(", ");
    let before = effect
        .residual_before
        .as_ref()
        .map(|ty| format!(" before={}", format_core_type(ty)))
        .unwrap_or_default();
    let after = effect
        .residual_after
        .as_ref()
        .map(|ty| format!(" after={}", format_core_type(ty)))
        .unwrap_or_default();
    format!("handle[consumes=[{consumes}]{}{}]", before, after)
}

fn format_runtime_stmt(stmt: &runtime::Stmt, verbose: bool) -> String {
    match stmt {
        runtime::Stmt::Let { pattern, value } => {
            format!(
                "let {} = {}",
                format_runtime_pattern(pattern),
                format_runtime_expr(value, verbose)
            )
        }
        runtime::Stmt::Expr(expr) => format_runtime_expr(expr, verbose),
        runtime::Stmt::Module { def, body } => {
            format!(
                "module {} = {}",
                format_core_path(def),
                format_runtime_expr(body, verbose)
            )
        }
    }
}

fn format_runtime_pattern(pattern: &runtime::Pattern) -> String {
    match pattern {
        runtime::Pattern::Wildcard { .. } => "_".to_string(),
        runtime::Pattern::Bind { name, .. } => name.0.clone(),
        runtime::Pattern::Lit { lit, .. } => format_core_lit(lit),
        runtime::Pattern::Tuple { items, .. } => {
            let items = items
                .iter()
                .map(format_runtime_pattern)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        runtime::Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            let mut items = prefix
                .iter()
                .map(format_runtime_pattern)
                .collect::<Vec<_>>();
            if let Some(spread) = spread {
                items.push(format!("..{}", format_runtime_pattern(spread)));
            }
            items.extend(suffix.iter().map(format_runtime_pattern));
            format!("[{}]", items.join(", "))
        }
        runtime::Pattern::Record { fields, spread, .. } => {
            let mut items = fields
                .iter()
                .map(|field| match &field.default {
                    Some(default)
                        if matches!(&field.pattern, runtime::Pattern::Bind { name, .. } if name == &field.name) =>
                    {
                        format!("{} = {}", field.name.0, format_runtime_expr(default, false))
                    }
                    Some(default) => format!(
                        "{}: {} = {}",
                        field.name.0,
                        format_runtime_pattern(&field.pattern),
                        format_runtime_expr(default, false)
                    ),
                    None => format!("{}: {}", field.name.0, format_runtime_pattern(&field.pattern)),
                })
                .collect::<Vec<_>>();
            if let Some(spread) = spread {
                items.push(format_runtime_record_spread_pattern(spread));
            }
            format!("{{{}}}", items.join(", "))
        }
        runtime::Pattern::Variant { tag, value, .. } => match value {
            Some(value) => format!(":{} {}", tag.0, format_runtime_pattern(value)),
            None => format!(":{}", tag.0),
        },
        runtime::Pattern::Or { left, right, .. } => {
            format!(
                "{} | {}",
                format_runtime_pattern(left),
                format_runtime_pattern(right)
            )
        }
        runtime::Pattern::As { pattern, name, .. } => {
            format!("{} as {}", format_runtime_pattern(pattern), name.0)
        }
    }
}

fn format_runtime_record_spread_pattern(spread: &runtime::RecordSpreadPattern) -> String {
    match spread {
        runtime::RecordSpreadPattern::Head(pattern) => {
            format!("..{}", format_runtime_pattern(pattern))
        }
        runtime::RecordSpreadPattern::Tail(pattern) => {
            format!("{}..", format_runtime_pattern(pattern))
        }
    }
}

fn format_core_path(path: &core_ir::Path) -> String {
    if path.segments.is_empty() {
        "<root>".to_string()
    } else {
        path.segments
            .iter()
            .map(|segment| segment.0.as_str())
            .collect::<Vec<_>>()
            .join("::")
    }
}

fn is_top_type(ty: &core_ir::Type) -> bool {
    matches!(ty, core_ir::Type::Any)
}

fn is_implicit_fun_effect(param_effect: &core_ir::Type, ret_effect: &core_ir::Type) -> bool {
    is_top_type(param_effect) && (is_top_type(ret_effect) || is_pure_row(ret_effect))
}

fn is_empty_effect(ty: &core_ir::Type) -> bool {
    matches!(ty, core_ir::Type::Never) || is_pure_row(ty)
}

fn is_pure_row(ty: &core_ir::Type) -> bool {
    matches!(
        ty,
        core_ir::Type::Row { items, tail }
            if items.is_empty() && matches!(tail.as_ref(), core_ir::Type::Never)
    )
}

fn is_std_prelude_path(path: &core_ir::Path) -> bool {
    matches!(
        path.segments.as_slice(),
        [core_ir::Name(std), core_ir::Name(prelude), ..] if std == "std" && prelude == "prelude"
    )
}

fn infer_error_headline(state: &InferLowerState, error: &InferTypeError) -> String {
    match &error.kind {
        InferTypeErrorKind::ConstructorMismatch => {
            format!(
                "expected {}, found {}",
                format_infer_neg(state, error.neg),
                format_infer_pos(state, error.pos)
            )
        }
        InferTypeErrorKind::TupleArityMismatch { pos_len, neg_len } => {
            format!("tuple arity mismatch: expected {neg_len}, found {pos_len}")
        }
        InferTypeErrorKind::MissingRecordField { name } => {
            infer_missing_record_field_message(&state.infer.arena.get_pos(error.pos), name)
        }
        InferTypeErrorKind::ExpectedShape { expected } => match expected {
            InferExpectedShape::Function => "expected function".to_string(),
            InferExpectedShape::Tuple => "expected tuple".to_string(),
            InferExpectedShape::Record => "expected record".to_string(),
            InferExpectedShape::Constructor => "expected constructor".to_string(),
        },
        InferTypeErrorKind::MissingImpl { role, args } => {
            format!("no impl for {}<{}>", role, args.join(", "))
        }
        InferTypeErrorKind::MissingImplMember { role, member } => {
            format!("impl {} is missing required member `{}`", role, member)
        }
        InferTypeErrorKind::UnknownImplMember { role, member } => {
            format!("impl {} defines unknown member `{}`", role, member)
        }
        InferTypeErrorKind::AmbiguousImpl {
            role,
            args,
            candidates,
            previews,
        } => {
            let preview_suffix = if previews.is_empty() {
                String::new()
            } else {
                format!(
                    ": {}",
                    previews
                        .iter()
                        .take(2)
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(" vs ")
                )
            };
            format!(
                "ambiguous impl for {}<{}> ({} candidates{})",
                role,
                args.join(", "),
                candidates,
                preview_suffix,
            )
        }
        InferTypeErrorKind::MissingImplPrerequisite {
            role,
            args,
            prerequisite_role,
            prerequisite_args,
        } => {
            format!(
                "impl {}<{}> requires {}<{}>",
                role,
                args.join(", "),
                prerequisite_role,
                prerequisite_args.join(", "),
            )
        }
        InferTypeErrorKind::AmbiguousImplPrerequisite {
            role,
            args,
            prerequisite_role,
            prerequisite_args,
            candidates,
            previews,
        } => {
            let preview_suffix = if previews.is_empty() {
                String::new()
            } else {
                format!(
                    ": {}",
                    previews
                        .iter()
                        .take(2)
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(" vs ")
                )
            };
            format!(
                "impl {}<{}> requires ambiguous {}<{}> ({} candidates{})",
                role,
                args.join(", "),
                prerequisite_role,
                prerequisite_args.join(", "),
                candidates,
                preview_suffix,
            )
        }
        InferTypeErrorKind::AmbiguousEffectMethod { method, effects } => {
            format!(
                "ambiguous effect method `{}` from effects {}",
                method,
                effects.join(", ")
            )
        }
    }
}

fn infer_missing_record_field_message(pos: &InferPos, name: &str) -> String {
    if infer_pos_has_optional_record_field(pos, name) {
        format!("record field `{name}` may be missing, but a required field was expected")
    } else {
        format!("missing required record field `{name}`")
    }
}

fn infer_pos_has_optional_record_field(pos: &InferPos, name: &str) -> bool {
    match pos {
        InferPos::Record(fields)
        | InferPos::RecordTailSpread { fields, .. }
        | InferPos::RecordHeadSpread { fields, .. } => fields
            .iter()
            .any(|field| field.name.0 == name && field.optional),
        _ => false,
    }
}

fn format_infer_pos(state: &InferLowerState, pos: InferPosId) -> String {
    match state.infer.arena.get_pos(pos).clone() {
        InferPos::Bot => "⊥".to_string(),
        InferPos::Var(tv) => format!("?{}", tv.0),
        InferPos::Raw(tv) => format!("?{}...", tv.0),
        InferPos::Atom(atom) => format_infer_path(&atom.path),
        InferPos::Forall(_, body) => format_infer_pos(state, body),
        InferPos::Con(path, args) => {
            let head = format_infer_path(&path);
            if args.is_empty() {
                head
            } else {
                let args = args
                    .iter()
                    .map(|(pos, _)| format_infer_pos(state, *pos))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{head}<{args}>")
            }
        }
        InferPos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => format!(
            "{} [{}] -> [{}] {}",
            format_infer_neg(state, arg),
            format_infer_neg(state, arg_eff),
            format_infer_pos(state, ret_eff),
            format_infer_pos(state, ret)
        ),
        InferPos::Record(fields) => {
            let fields = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}{}: {}",
                        field.name.0,
                        if field.optional { "?" } else { "" },
                        format_infer_pos(state, field.value),
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{{fields}}}")
        }
        InferPos::RecordTailSpread { fields, tail } => {
            let mut items = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}{}: {}",
                        field.name.0,
                        if field.optional { "?" } else { "" },
                        format_infer_pos(state, field.value),
                    )
                })
                .collect::<Vec<_>>();
            items.push(format!("..{}", format_infer_pos(state, tail)));
            format!("{{{}}}", items.join(", "))
        }
        InferPos::RecordHeadSpread { tail, fields } => {
            let mut items = vec![format!("..{}", format_infer_pos(state, tail))];
            items.extend(fields.iter().map(|field| {
                format!(
                    "{}{}: {}",
                    field.name.0,
                    if field.optional { "?" } else { "" },
                    format_infer_pos(state, field.value),
                )
            }));
            format!("{{{}}}", items.join(", "))
        }
        InferPos::PolyVariant(items) => items
            .iter()
            .map(|(name, _)| name.0.clone())
            .collect::<Vec<_>>()
            .join(" | "),
        InferPos::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| format_infer_pos(state, *item))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        InferPos::Row(items, tail) => format_infer_pos_row(state, &items, tail),
        InferPos::Union(lhs, rhs) => {
            format!(
                "{} | {}",
                format_infer_pos(state, lhs),
                format_infer_pos(state, rhs)
            )
        }
    }
}

fn format_infer_neg(state: &InferLowerState, neg: InferNegId) -> String {
    match state.infer.arena.get_neg(neg).clone() {
        InferNeg::Top => "⊤".to_string(),
        InferNeg::Var(tv) => format!("?{}", tv.0),
        InferNeg::Atom(atom) => format_infer_path(&atom.path),
        InferNeg::Forall(_, body) => format_infer_neg(state, body),
        InferNeg::Con(path, args) => {
            let head = format_infer_path(&path);
            if args.is_empty() {
                head
            } else {
                let args = args
                    .iter()
                    .map(|(_, neg)| format_infer_neg(state, *neg))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{head}<{args}>")
            }
        }
        InferNeg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => format!(
            "{} [{}] -> [{}] {}",
            format_infer_pos(state, arg),
            format_infer_pos(state, arg_eff),
            format_infer_neg(state, ret_eff),
            format_infer_neg(state, ret)
        ),
        InferNeg::Record(fields) => {
            let fields = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}{}: {}",
                        field.name.0,
                        if field.optional { "?" } else { "" },
                        format_infer_neg(state, field.value),
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{{fields}}}")
        }
        InferNeg::PolyVariant(items) => items
            .iter()
            .map(|(name, _)| name.0.clone())
            .collect::<Vec<_>>()
            .join(" & "),
        InferNeg::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| format_infer_neg(state, *item))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        InferNeg::Row(items, tail) => format_infer_neg_row(state, &items, tail),
        InferNeg::Intersection(lhs, rhs) => {
            format!(
                "{} & {}",
                format_infer_neg(state, lhs),
                format_infer_neg(state, rhs)
            )
        }
    }
}

fn format_infer_pos_row(state: &InferLowerState, items: &[InferPosId], tail: InferPosId) -> String {
    let mut parts = items
        .iter()
        .map(|item| format_infer_pos(state, *item))
        .collect::<Vec<_>>();
    let tail = format_infer_pos(state, tail);
    if tail != "⊥" {
        parts.push(tail);
    }
    format!("[{}]", parts.join("; "))
}

fn format_infer_neg_row(state: &InferLowerState, items: &[InferNegId], tail: InferNegId) -> String {
    let mut parts = items
        .iter()
        .map(|item| format_infer_neg(state, *item))
        .collect::<Vec<_>>();
    let tail = format_infer_neg(state, tail);
    if tail != "⊤" {
        parts.push(tail);
    }
    format!("[{}]", parts.join("; "))
}

fn format_infer_path(path: &InferPath) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut line_start = 0;
    for (idx, ch) in source.char_indices() {
        if idx >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = idx + ch.len_utf8();
        }
    }
    (line, offset.saturating_sub(line_start) + 1)
}

fn source_options(options: &CliOptions) -> SourceOptions {
    let std_root = options
        .std_root
        .as_ref()
        .map(PathBuf::from)
        .or_else(default_std_root);
    SourceOptions {
        implicit_prelude: !options.no_prelude && std_root.is_some(),
        std_root,
        search_paths: Vec::new(),
    }
}

fn default_std_root() -> Option<PathBuf> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib/std");
    root.is_dir().then_some(root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_infer::{Name as InferName, RecordField as InferRecordField};

    fn test_cli_options() -> CliOptions {
        CliOptions {
            show_cst: false,
            parse_mode: None,
            infer: true,
            core_ir: false,
            runtime_ir: false,
            hygiene_ir: false,
            run_vm: false,
            verbose_ir: false,
            infer_phase_timings: false,
            runtime_phase_timings: false,
            path: None,
            no_prelude: true,
            std_root: None,
            profile_flamegraph: None,
            profile_repeat: 1,
        }
    }

    #[test]
    fn infer_missing_record_field_message_reports_absent_field() {
        let pos = InferPos::Record(vec![]);
        assert_eq!(
            infer_missing_record_field_message(&pos, "width"),
            "missing required record field `width`",
        );
    }

    #[test]
    fn infer_missing_record_field_message_reports_optional_field() {
        let pos = InferPos::Record(vec![InferRecordField::optional(
            InferName("width".to_string()),
            InferPosId(0),
        )]);
        assert_eq!(
            infer_missing_record_field_message(&pos, "width"),
            "record field `width` may be missing, but a required field was expected",
        );
    }

    #[test]
    fn top_level_projected_var_assignment_runs() {
        run_with_large_stack(|| {
            let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
            let std_root = repo_root.join("lib/std");
            let mut lowered = yulang_infer::lower_virtual_source_with_options(
                "my $xs = [2, 3, 4]\n&xs[1] = 6\n$xs\n",
                Some(repo_root),
                SourceOptions {
                    std_root: Some(std_root),
                    implicit_prelude: true,
                    search_paths: Vec::new(),
                },
            )
            .expect("lowered source");
            let program = export_core_program(&mut lowered.state);
            let module = runtime::lower_core_program(program).expect("lowered runtime IR");
            let (module, _) = runtime::monomorphize_module_profiled(module).expect("monomorphized");
            let vm = runtime::compile_vm_module(module).expect("compiled VM module");
            let results = vm.eval_roots().expect("evaluated roots");
            assert_eq!(results.len(), 1);
            assert_eq!(format_runtime_vm_result(&results[0]), "[2, 6, 4]");
        });
    }

    #[test]
    fn infer_error_headline_reports_missing_impl() {
        let source = "role Display 'a:\n    our a.display: string\n\nmy shown = 1.display\n";
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let (mut state, _, _) = lower_infer_sources(None, &root, source, &options);
        let _ = state.finalize_compact_results();
        let errors = state.infer.type_errors();
        let error = errors
            .iter()
            .find(|error| matches!(error.kind, InferTypeErrorKind::MissingImpl { .. }))
            .expect("missing impl error should be reported after finalize");

        assert_eq!(
            infer_error_headline(&state, error),
            "no impl for Display<int>"
        );
    }

    #[test]
    fn infer_error_context_reports_annotation_edge() {
        let source = "my x: int = \"s\"\n";
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let (state, _, _) = lower_infer_sources(None, &root, source, &options);
        let errors = state.infer.type_errors();
        let error = errors
            .iter()
            .find(|error| matches!(error.kind, InferTypeErrorKind::ConstructorMismatch))
            .expect("annotation mismatch should report constructor mismatch");

        let context = infer_error_expected_context(&state, error).expect("expected context");
        assert_eq!(
            context.summary,
            "annotation expected int; expression provides std::str::str"
        );
        let edge = context.edge.expect("from edge");
        assert!(edge.starts_with("#0 annotation expression actual "));
        assert!(edge.contains("std::str::str"));
        assert!(edge.contains("=> annotation "));
        assert!(context.detail.is_none());
    }

    #[test]
    fn infer_error_context_reports_application_argument_edge() {
        let source = "my f(x: int) = x\nf \"s\"\n";
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let (state, _, _) = lower_infer_sources(None, &root, source, &options);
        let errors = state.infer.type_errors();
        let error = errors
            .iter()
            .find(|error| matches!(error.kind, InferTypeErrorKind::ConstructorMismatch))
            .expect("argument mismatch should report constructor mismatch");

        let context = infer_error_expected_context(&state, error).expect("expected context");
        assert_eq!(
            context.summary,
            "function argument expected int; expression provides std::str::str"
        );
        let edge = context.edge.expect("from edge");
        assert!(edge.contains("application-argument argument actual "));
        assert!(edge.contains("std::str::str"));
        assert!(edge.contains("=> parameter "));
        assert!(context.detail.is_none());
    }

    #[test]
    fn infer_error_context_reports_derived_record_field_edge() {
        let source = "my p: { a: { b: int } } = { a: { b: \"s\" } }\n";
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let (state, _, _) = lower_infer_sources(None, &root, source, &options);
        let errors = state.infer.type_errors();
        let error = errors
            .iter()
            .find(|error| matches!(error.kind, InferTypeErrorKind::ConstructorMismatch))
            .expect("nested record mismatch should report constructor mismatch");

        let context = infer_error_expected_context(&state, error).expect("expected context");
        let detail = context.detail.expect("derived edge detail");

        assert!(
            detail.starts_with("record-field .a.b "),
            "detail was {detail}"
        );
        assert!(detail.contains("std::str::str"), "detail was {detail}");
        assert!(detail.contains("expected=int"), "detail was {detail}");
    }

    #[test]
    fn infer_error_headline_reports_ambiguous_impl() {
        let source = concat!(
            "role Display 'a:\n    our a.display: string\n\n",
            "impl Display int;\n",
            "impl Display int;\n",
            "my shown = 1.display\n",
        );
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let (mut state, _, _) = lower_infer_sources(None, &root, source, &options);
        let _ = state.finalize_compact_results();
        let errors = state.infer.type_errors();
        let error = errors
            .iter()
            .find(|error| matches!(error.kind, InferTypeErrorKind::AmbiguousImpl { .. }))
            .expect("ambiguous impl error should be reported after finalize");

        assert_eq!(
            infer_error_headline(&state, error),
            "ambiguous impl for Display<int> (2 candidates: Display<int> vs Display<int>)"
        );
    }

    #[test]
    fn infer_error_headline_reports_missing_impl_member() {
        let source = concat!(
            "role Pair 'a:\n    our a.first: int\n    our a.second: int\n\n",
            "impl Pair int:\n    our x.first = 1\n",
        );
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let (mut state, _, _) = lower_infer_sources(None, &root, source, &options);
        let _ = state.finalize_compact_results();
        let errors = state.infer.type_errors();
        let error = errors
            .iter()
            .find(|error| matches!(error.kind, InferTypeErrorKind::MissingImplMember { .. }))
            .expect("missing impl member error should be reported after finalize");

        assert_eq!(
            infer_error_headline(&state, error),
            "impl Pair is missing required member `second`"
        );
    }

    #[test]
    fn infer_error_headline_reports_unknown_impl_member() {
        let source = concat!(
            "role Score 'a:\n    our a.score: int\n\n",
            "impl Score int:\n    our x.other = 1\n",
        );
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let (mut state, _, _) = lower_infer_sources(None, &root, source, &options);
        let _ = state.finalize_compact_results();
        let errors = state.infer.type_errors();
        let error = errors
            .iter()
            .find(|error| matches!(error.kind, InferTypeErrorKind::UnknownImplMember { .. }))
            .expect("unknown impl member error should be reported after finalize");

        assert_eq!(
            infer_error_headline(&state, error),
            "impl Score defines unknown member `other`"
        );
    }

    #[test]
    fn format_apply_evidence_shows_full_projected_bounds() {
        let evidence = core_ir::ApplyEvidence {
            callee_source_edge: None,
            expected_callee: None,
            arg_source_edge: None,
            callee: core_ir::TypeBounds {
                lower: None,
                upper: Some(Box::new(core_ir::Type::Fun {
                    param: Box::new(core_ir::Type::Named {
                        path: core_ir::Path {
                            segments: vec![core_ir::Name("int".to_string())],
                        },
                        args: vec![],
                    }),
                    param_effect: Box::new(core_ir::Type::Any),
                    ret_effect: Box::new(core_ir::Type::Row {
                        items: vec![],
                        tail: Box::new(core_ir::Type::Never),
                    }),
                    ret: Box::new(core_ir::Type::Named {
                        path: core_ir::Path {
                            segments: vec![core_ir::Name("int".to_string())],
                        },
                        args: vec![],
                    }),
                })),
            },
            arg: core_ir::TypeBounds {
                lower: Some(Box::new(core_ir::Type::Named {
                    path: core_ir::Path {
                        segments: vec![core_ir::Name("int".to_string())],
                    },
                    args: vec![],
                })),
                upper: Some(Box::new(core_ir::Type::Named {
                    path: core_ir::Path {
                        segments: vec![core_ir::Name("int".to_string())],
                    },
                    args: vec![],
                })),
            },
            expected_arg: None,
            result: core_ir::TypeBounds {
                lower: Some(Box::new(core_ir::Type::Var(core_ir::TypeVar(
                    "a".to_string(),
                )))),
                upper: Some(Box::new(core_ir::Type::Named {
                    path: core_ir::Path {
                        segments: vec![core_ir::Name("int".to_string())],
                    },
                    args: vec![],
                })),
            },
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
        };

        assert_eq!(
            format_apply_evidence(&evidence),
            "apply[callee=_ <: int -> int, arg=int, result=a <: _ <: int]"
        );
    }
}
