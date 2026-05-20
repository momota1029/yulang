use std::cmp::Reverse;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::env;
use std::fs;
#[cfg(not(windows))]
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process;
use std::process::Command;
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use chasa::error::LatestSink;
use chasa::input::{In, Input as _, IsCut};
use either::Either;
use im::HashSet;
#[cfg(not(windows))]
use pprof::ProfilerGuardBuilder;
use reborrow_generic::Reborrow as _;
use rowan::SyntaxNode;
use yulang_infer::ids::{NegId as InferNegId, PosId as InferPosId};
use yulang_infer::{
    CompiledRuntimeBundle, CompiledUnitArtifactBundle, CompiledUnitArtifactCache,
    ExpectedEdge as InferExpectedEdge, ExpectedEdgeKind as InferExpectedEdgeKind,
    ExpectedShape as InferExpectedShape, FinalizeCompactProfile as InferFinalizeCompactProfile,
    LowerState as InferLowerState, Neg as InferNeg, Path as InferPath, Pos as InferPos,
    ProfiledLoweredSources as InferProfiledLoweredSources,
    SourceLowerProfile as InferSourceLowerProfile, SourceOptions, SourceSet,
    SurfaceDiagnostic as InferSurfaceDiagnostic, TypeError as InferTypeError,
    TypeErrorKind as InferTypeErrorKind, build_compiled_unit_artifact_bundle,
    build_compiled_unit_artifacts, collect_compact_results as collect_infer_compact_results,
    collect_derived_expected_edge_evidence as collect_infer_derived_expected_edge_evidence,
    collect_expected_adapter_edge_evidence as collect_infer_expected_adapter_edge_evidence,
    collect_expected_edge_evidence as collect_infer_expected_edge_evidence,
    collect_expected_edges as collect_infer_expected_edges,
    collect_surface_diagnostics as collect_infer_surface_diagnostics, export_core_program,
    lower_source_set, lower_source_set_profiled,
    lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled,
    with_profile_enabled as with_infer_profile_enabled,
};
use yulang_parser::context::{Env, State};
use yulang_parser::expr::parse_expr;
use yulang_parser::lex::{SyntaxKind, TriviaInfo};
use yulang_parser::mark::parse::parse_doc;
use yulang_parser::op::standard_op_table;
use yulang_parser::pat::parse::parse_pattern;
use yulang_parser::scan::trivia::scan_trivia;
use yulang_parser::sink::{Event, EventSink, VecSink, YulangLanguage};
use yulang_parser::stmt::parse_statement;
use yulang_parser::typ::parse::parse_type;
use yulang_parser::{parse_module_to_green, parse_module_to_green_with_ops};
use yulang_runtime as runtime;
use yulang_sources::{
    SourceCompilationUnitOrigin, collect_source_files_with_options,
    collect_virtual_source_files_with_options, default_versioned_std_root, install_embedded_std,
    resolve_or_install_std_root,
};
use yulang_typed_ir as typed_ir;

// ── CLI ───────────────────────────────────────────────────────────────────────

#[cfg(not(windows))]
type CpuProfileGuard = pprof::ProfilerGuard<'static>;

#[cfg(windows)]
struct CpuProfileGuard;

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

const YUIR_SOURCE_CACHE_VERSION: u32 = 4;

#[derive(Debug, Clone, PartialEq, Eq)]
struct CliOptions {
    show_cst: bool,
    parse_mode: Option<ParserMode>,
    infer: bool,
    core_ir: bool,
    runtime_ir: bool,
    hygiene_ir: bool,
    run_interpreter: bool,
    control_vm: bool,
    control_vm_emit: Option<NativeOutput>,
    control_vm_load: Option<String>,
    native_compare_i64: bool,
    native_abi_lanes: bool,
    native_object: Option<NativeOutput>,
    native_exe: Option<NativeOutput>,
    native_value_exe: Option<NativeOutput>,
    native_run: Option<NativeOutput>,
    native_run_exe: Option<NativeOutput>,
    native_run_value_exe: Option<NativeOutput>,
    native_run_cps_repr_exe: Option<NativeOutput>,
    native_run_mmtk_cps_repr_exe: Option<NativeOutput>,
    print_roots: bool,
    verbose_ir: bool,
    infer_phase_timings: bool,
    runtime_phase_timings: bool,
    path: Option<String>,
    no_prelude: bool,
    no_cache: bool,
    std_root: Option<String>,
    profile_flamegraph: Option<String>,
    profile_repeat: usize,
    install_std: bool,
    cache_op: Option<CacheOp>,
    lock_op: Option<LockOp>,
    realm_op: Option<RealmOp>,
    server: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
enum ParserMode {
    Expr,
    Pat,
    Stmt,
    Type,
    Mark,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum NativeOutput {
    Path(String),
    Default,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CacheOp {
    Clear,
    Path,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LockOp {
    check: bool,
    out: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum RealmOp {
    Freeze {
        path: Option<String>,
        version: String,
    },
}

#[derive(clap::Parser)]
#[command(
    name = "yulang",
    version,
    about = "Yulang language CLI",
    disable_help_subcommand = true
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,

    /// Also print the CST before downstream phases
    #[arg(long, global = true)]
    cst: bool,
    /// Do not implicitly import std::prelude
    #[arg(long, global = true)]
    no_prelude: bool,
    /// Disable source and dependency artifact cache reads/writes
    #[arg(long, global = true)]
    no_cache: bool,
    /// Use an alternate std source root
    #[arg(long, global = true, value_name = "PATH")]
    std_root: Option<String>,
    /// Include detailed graph/evidence sections in IR dumps
    #[arg(long, global = true)]
    verbose_ir: bool,
    /// Print coarse timing breakdown for the infer pipeline
    #[arg(long, global = true)]
    infer_phase_timings: bool,
    /// Print coarse timing breakdown for runtime lowering / interpreter execution
    #[arg(long, global = true)]
    runtime_phase_timings: bool,
    /// Write a CPU flamegraph SVG with pprof
    #[arg(long, global = true, value_name = "SVG")]
    profile_flamegraph: Option<String>,
    /// Run the pipeline N times and print only the last result
    #[arg(long, global = true, value_name = "N", default_value_t = 1)]
    profile_repeat: usize,
}

#[derive(clap::Subcommand)]
enum Cmd {
    /// Type-check and print principal types (no path = read stdin)
    Check { path: Option<String> },
    /// Build a Yulang runtime artifact
    Build(BuildArgs),
    /// Execute the program
    #[command(visible_alias = "interpret")]
    Run(RunArgs),
    /// Print intermediate representations
    Dump(DumpArgs),
    /// Parser views (parse event tree for one fragment)
    Parse(ParseArgs),
    /// Install Yulang resources
    Install {
        #[command(subcommand)]
        target: InstallTarget,
    },
    /// Inspect or clear Yulang cache directories
    Cache {
        #[command(subcommand)]
        op: CacheCmd,
    },
    /// Generate or validate yulang.lock for the current source graph
    Lock(LockArgs),
    /// Manage local realms
    Realm {
        #[command(subcommand)]
        op: RealmCmd,
    },
    /// Install the embedded std sources and exit
    #[command(hide = true)]
    InstallStd,
    /// Backend diagnostics
    Debug {
        #[command(subcommand)]
        op: DebugOp,
    },
    /// Start the Yulang language server
    Server,
}

#[derive(clap::Args)]
struct RunArgs {
    path: Option<String>,
    /// Execute through the reference interpreter
    #[arg(long)]
    interpreter: bool,
    /// Print root expression values after executing them
    #[arg(long)]
    print_roots: bool,
}

#[derive(clap::Args)]
struct BuildArgs {
    path: Option<String>,
    /// Output path for the YUIR artifact (defaults to target/yulang/yuir/)
    #[arg(long, value_name = "PATH")]
    out: Option<String>,
}

#[derive(clap::Args)]
struct LockArgs {
    path: Option<String>,
    /// Validate the generated lock graph without writing a file
    #[arg(long)]
    check: bool,
    /// Output path for the lock file (defaults to the entry realm root)
    #[arg(long, value_name = "PATH")]
    out: Option<String>,
}

#[derive(clap::Subcommand)]
enum RealmCmd {
    /// Freeze an editable realm into .yulang/versions/<version>
    Freeze(RealmFreezeArgs),
}

#[derive(clap::Args)]
struct RealmFreezeArgs {
    /// Realm root path (defaults to current directory)
    path: Option<String>,
    /// Version to write into the frozen realm manifest
    #[arg(long, value_name = "VERSION")]
    version: String,
}

#[derive(clap::Subcommand)]
enum InstallTarget {
    /// Install the embedded std sources and exit
    Std,
}

#[derive(clap::Subcommand)]
enum CacheCmd {
    /// Delete the user cache root used by this command
    Clear,
    /// Print the user cache root used by this command
    Path,
}

#[derive(clap::Args)]
struct DumpArgs {
    path: Option<String>,
    /// Print principal core-ir exported from yulang-infer
    #[arg(long)]
    core_ir: bool,
    /// Print strict typed runtime IR lowered from principal core-ir
    #[arg(long)]
    runtime_ir: bool,
    /// Print runtime effect-id hygiene operations
    #[arg(long)]
    hygiene_ir: bool,
}

#[derive(clap::Args)]
struct ParseArgs {
    path: Option<String>,
    /// What to parse
    #[arg(long = "as", value_enum)]
    parse_as: ParserMode,
}

#[derive(clap::Subcommand)]
enum DebugOp {
    /// Execute through the experimental arena-backed control VM
    #[command(hide = true)]
    ControlVm {
        path: Option<String>,
        #[arg(long)]
        print_roots: bool,
    },
    /// Emit experimental arena-backed control VM artifact
    #[command(hide = true)]
    ControlVmEmit {
        path: Option<String>,
        #[arg(long, value_name = "PATH")]
        out: String,
    },
    /// Load and execute experimental arena-backed control VM artifact
    #[command(hide = true)]
    ControlVmLoad {
        path: String,
        #[arg(long)]
        print_roots: bool,
    },
}

fn parse_args() -> CliOptions {
    use clap::Parser as _;
    let cli = Cli::parse();
    let mut opts = CliOptions {
        show_cst: cli.cst,
        parse_mode: None,
        infer: false,
        core_ir: false,
        runtime_ir: false,
        hygiene_ir: false,
        run_interpreter: false,
        control_vm: false,
        control_vm_emit: None,
        control_vm_load: None,
        native_compare_i64: false,
        native_abi_lanes: false,
        native_object: None,
        native_exe: None,
        native_value_exe: None,
        native_run: None,
        native_run_exe: None,
        native_run_value_exe: None,
        native_run_cps_repr_exe: None,
        native_run_mmtk_cps_repr_exe: None,
        print_roots: false,
        verbose_ir: cli.verbose_ir,
        infer_phase_timings: cli.infer_phase_timings,
        runtime_phase_timings: cli.runtime_phase_timings,
        path: None,
        no_prelude: cli.no_prelude,
        no_cache: cli.no_cache,
        std_root: cli.std_root,
        profile_flamegraph: cli.profile_flamegraph,
        profile_repeat: if cli.profile_repeat == 0 {
            eprintln!("--profile-repeat must be a positive integer");
            process::exit(2);
        } else {
            cli.profile_repeat
        },
        install_std: false,
        cache_op: None,
        lock_op: None,
        realm_op: None,
        server: false,
    };
    match cli.cmd {
        Cmd::Check { path } => {
            opts.infer = true;
            opts.path = path;
        }
        Cmd::Build(BuildArgs { path, out }) => {
            opts.path = path;
            opts.control_vm = true;
            opts.control_vm_emit = Some(match out {
                Some(path) => NativeOutput::Path(path),
                None => NativeOutput::Default,
            });
        }
        Cmd::Run(args) => {
            opts.path = args.path;
            opts.print_roots = args.print_roots;
            if args.interpreter {
                opts.run_interpreter = true;
            } else {
                opts.control_vm = true;
                if let Some(path) = opts.path.as_deref()
                    && is_yuir_artifact_path(path)
                {
                    opts.control_vm = false;
                    opts.control_vm_load = Some(path.to_string());
                }
            }
        }
        Cmd::Dump(DumpArgs {
            path,
            core_ir,
            runtime_ir,
            hygiene_ir,
        }) => {
            if !core_ir && !runtime_ir && !hygiene_ir {
                eprintln!(
                    "yulang dump: specify at least one of --core-ir, --runtime-ir, --hygiene-ir"
                );
                process::exit(2);
            }
            opts.path = path;
            opts.core_ir = core_ir;
            opts.runtime_ir = runtime_ir;
            opts.hygiene_ir = hygiene_ir;
        }
        Cmd::Parse(ParseArgs { path, parse_as }) => {
            opts.path = path;
            opts.parse_mode = Some(parse_as);
        }
        Cmd::Install {
            target: InstallTarget::Std,
        }
        | Cmd::InstallStd => {
            opts.install_std = true;
        }
        Cmd::Cache { op } => {
            opts.cache_op = Some(match op {
                CacheCmd::Clear => CacheOp::Clear,
                CacheCmd::Path => CacheOp::Path,
            });
        }
        Cmd::Lock(LockArgs { path, check, out }) => {
            opts.path = path;
            opts.lock_op = Some(LockOp { check, out });
        }
        Cmd::Realm { op } => match op {
            RealmCmd::Freeze(RealmFreezeArgs { path, version }) => {
                opts.realm_op = Some(RealmOp::Freeze { path, version });
            }
        },
        Cmd::Debug { op } => match op {
            DebugOp::ControlVm { path, print_roots } => {
                opts.control_vm = true;
                opts.path = path;
                opts.print_roots = print_roots;
            }
            DebugOp::ControlVmEmit { path, out } => {
                opts.control_vm = true;
                opts.control_vm_emit = Some(NativeOutput::Path(out));
                opts.path = path;
            }
            DebugOp::ControlVmLoad { path, print_roots } => {
                opts.control_vm = true;
                opts.control_vm_load = Some(path);
                opts.print_roots = print_roots;
            }
        },
        Cmd::Server => {
            opts.server = true;
        }
    }
    opts
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

fn run_control_vm_load_or_exit(path: &str, options: &CliOptions) {
    let load_start = Instant::now();
    let module = match runtime::ControlVmModule::read_artifact_file(Path::new(path)) {
        Ok(module) => module,
        Err(err) => {
            eprintln!("failed to read YUIR artifact {path}: {err}");
            process::exit(1);
        }
    };
    let load_duration = load_start.elapsed();

    let eval_start = Instant::now();
    let mut results = Vec::new();
    let mut profile = runtime::VmProfile::default();
    let mut host_stdout = String::new();
    for index in 0..module.root_count() {
        match module.eval_root_expr_with_basic_host_profiled(index, &mut host_stdout) {
            Ok((result, item_profile)) => {
                profile.merge(item_profile);
                if !host_stdout.is_empty() {
                    print!("{host_stdout}");
                    host_stdout.clear();
                }
                results.push(result);
            }
            Err(err) => {
                eprintln!("failed to evaluate YUIR artifact {path}: {err}");
                process::exit(1);
            }
        }
    }
    let eval_duration = eval_start.elapsed();

    if options.runtime_phase_timings {
        eprintln!("runtime phase timings:");
        eprintln!("    yuir_load: {}", format_duration(load_duration));
        eprintln!("    vm_eval: {}", format_duration(eval_duration));
        eprintln!(
            "    vm_profile: eval_expr_calls={} max_eval_depth={} continuation_steps={} max_continuation_frames={}",
            profile.eval_expr_calls,
            profile.max_eval_depth,
            profile.continuation_steps,
            profile.max_continuation_frames
        );
    }
    if options.print_roots {
        for (index, result) in results.iter().enumerate() {
            println!("[{index}] {}", format_runtime_vm_result(result));
        }
    }
}

fn run_cached_control_vm_module_or_exit(
    module: runtime::ControlVmModule,
    load_duration: Duration,
    options: &CliOptions,
) {
    if let Some(path) = &options.control_vm_emit {
        let path = yuir_artifact_output_path(path, options.path.as_deref());
        ensure_parent_dir_or_exit(&path, "YUIR artifact");
        if let Err(err) = module.write_artifact_file(&path) {
            eprintln!("failed to write YUIR artifact {}: {err}", path.display());
            process::exit(1);
        }
        if options.runtime_phase_timings {
            eprintln!("runtime phase timings:");
            eprintln!(
                "    yuir_source_cache_load: {}",
                format_duration(load_duration)
            );
        }
        if !options.print_roots {
            println!("build: {}", path.display());
        }
        return;
    }

    let eval_start = Instant::now();
    let mut results = Vec::new();
    let mut profile = runtime::VmProfile::default();
    let mut host_stdout = String::new();
    for index in 0..module.root_count() {
        match module.eval_root_expr_with_basic_host_profiled(index, &mut host_stdout) {
            Ok((result, item_profile)) => {
                profile.merge(item_profile);
                if !host_stdout.is_empty() {
                    print!("{host_stdout}");
                    host_stdout.clear();
                }
                results.push(result);
            }
            Err(err) => {
                eprintln!("failed to evaluate cached control VM: {err}");
                process::exit(1);
            }
        }
    }
    let eval_duration = eval_start.elapsed();

    if options.runtime_phase_timings {
        eprintln!("runtime phase timings:");
        eprintln!(
            "    yuir_source_cache_load: {}",
            format_duration(load_duration)
        );
        eprintln!("    vm_eval: {}", format_duration(eval_duration));
        eprintln!(
            "    vm_profile: eval_expr_calls={} max_eval_depth={} continuation_steps={} max_continuation_frames={}",
            profile.eval_expr_calls,
            profile.max_eval_depth,
            profile.continuation_steps,
            profile.max_continuation_frames
        );
    }
    if options.print_roots {
        for (index, result) in results.iter().enumerate() {
            println!("[{index}] {}", format_runtime_vm_result(result));
        }
    }
}

fn run(options: &CliOptions) {
    if let Some(op) = options.cache_op {
        run_cache_op_or_exit(op);
        return;
    }

    if let Some(op) = &options.lock_op {
        run_lock_op_or_exit(op, options);
        return;
    }

    if let Some(op) = &options.realm_op {
        run_realm_op_or_exit(op);
        return;
    }

    if options.install_std {
        let root = default_versioned_std_root();
        if let Err(err) = install_embedded_std(&root) {
            eprintln!("failed to install std to {}: {err}", root.display());
            process::exit(1);
        }
        eprintln!("{}", root.display());
        return;
    }

    if options.server {
        #[cfg(feature = "server")]
        {
            yulang::server::run_blocking();
            return;
        }
        #[cfg(not(feature = "server"))]
        {
            eprintln!(
                "yulang server: this build was compiled without the `server` feature; rebuild with `cargo build --features server`"
            );
            process::exit(2);
        }
    }

    if let Some(path) = &options.control_vm_load {
        run_control_vm_load_or_exit(path, options);
        return;
    }

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

        let run_semantic_pipeline = options.requests_semantic_pipeline();

        if run_semantic_pipeline {
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

fn run_cache_op_or_exit(op: CacheOp) {
    let root = yulang_sources::default_user_cache_root();
    match op {
        CacheOp::Path => {
            println!("{}", root.display());
        }
        CacheOp::Clear => match fs::remove_dir_all(&root) {
            Ok(()) => println!("cleared {}", root.display()),
            Err(err) if err.kind() == io::ErrorKind::NotFound => {
                println!("cache already empty {}", root.display());
            }
            Err(err) => {
                eprintln!("failed to clear cache {}: {err}", root.display());
                process::exit(1);
            }
        },
    }
}

fn run_lock_op_or_exit(op: &LockOp, options: &CliOptions) {
    let source_set = collect_lock_source_set_or_exit(options);
    let lock = match yulang_sources::YulangLockFile::from_source_set(&source_set) {
        Ok(lock) => lock,
        Err(err) => {
            eprintln!("{err}");
            process::exit(1);
        }
    };
    let output_path = lock_output_path(op, options);
    if op.check {
        let existing = read_lock_file_or_exit(&output_path);
        if let Err(err) = existing.validate_with_constraints() {
            eprintln!("{err}");
            process::exit(1);
        }
        if existing != lock {
            eprintln!("lock file {} is out of date", output_path.display());
            process::exit(1);
        }
        println!(
            "lock: ok realms={} dependencies={} with_constraints={}",
            lock.realms.len(),
            lock.dependencies.len(),
            lock.with_constraints.len()
        );
        return;
    }

    ensure_parent_dir_or_exit(&output_path, "lock file");
    let json = match serde_json::to_string_pretty(&lock) {
        Ok(json) => json,
        Err(err) => {
            eprintln!("failed to encode lock file: {err}");
            process::exit(1);
        }
    };
    if let Err(err) = fs::write(&output_path, format!("{json}\n")) {
        eprintln!("failed to write lock file {}: {err}", output_path.display());
        process::exit(1);
    }
    println!("lock: {}", output_path.display());
}

fn run_realm_op_or_exit(op: &RealmOp) {
    match op {
        RealmOp::Freeze { path, version } => {
            let root = path.as_deref().unwrap_or(".");
            match yulang_sources::freeze_realm_version(root, version.clone()) {
                Ok(output) => {
                    let status = if output.already_exists {
                        "already frozen"
                    } else {
                        "frozen"
                    };
                    println!(
                        "realm freeze: {status} {} hash={:016x} files={}",
                        output.root.display(),
                        output.snapshot.source_hash,
                        output.snapshot.files.len()
                    );
                }
                Err(err) => {
                    eprintln!("{err}");
                    process::exit(1);
                }
            }
        }
    }
}

fn read_lock_file_or_exit(path: &Path) -> yulang_sources::YulangLockFile {
    let source = match fs::read_to_string(path) {
        Ok(source) => source,
        Err(err) => {
            eprintln!("failed to read lock file {}: {err}", path.display());
            process::exit(1);
        }
    };
    match serde_json::from_str(&source) {
        Ok(lock) => lock,
        Err(err) => {
            eprintln!("failed to decode lock file {}: {err}", path.display());
            process::exit(1);
        }
    }
}

fn collect_lock_source_set_or_exit(options: &CliOptions) -> SourceSet {
    match options.path.as_deref() {
        Some(path) => {
            match collect_source_files_with_options(
                path,
                source_options(options, path_base_dir(path)),
            ) {
                Ok(source_set) => source_set,
                Err(err) => {
                    eprintln!("{err}");
                    process::exit(1);
                }
            }
        }
        None => {
            let source = read_source(None);
            let base_dir = env::current_dir().ok();
            match collect_virtual_source_files_with_options(
                &source,
                base_dir.clone(),
                source_options(options, base_dir.as_deref()),
            ) {
                Ok(source_set) => source_set,
                Err(err) => {
                    eprintln!("{err}");
                    process::exit(1);
                }
            }
        }
    }
}

fn lock_output_path(op: &LockOp, options: &CliOptions) -> PathBuf {
    if let Some(path) = &op.out {
        return PathBuf::from(path);
    }
    let project_root = options
        .path
        .as_deref()
        .and_then(path_base_dir)
        .map(PathBuf::from)
        .unwrap_or_else(|| env::current_dir().unwrap_or_else(|_| PathBuf::from(".")));
    yulang_sources::YulangCachePaths::for_project(&project_root).lock_path(project_root)
}

fn start_cpu_profile(options: &CliOptions) -> Option<CpuProfileGuard> {
    let Some(_) = options.profile_flamegraph else {
        return None;
    };
    #[cfg(windows)]
    {
        eprintln!("--profile-flamegraph is not supported on Windows builds");
        process::exit(2)
    }
    #[cfg(not(windows))]
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

fn finish_cpu_profile(guard: Option<CpuProfileGuard>, options: &CliOptions) {
    let (Some(guard), Some(path)) = (guard, options.profile_flamegraph.as_deref()) else {
        return;
    };
    #[cfg(windows)]
    {
        let _ = (guard, path);
        return;
    }
    #[cfg(not(windows))]
    {
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

fn has_invalid_token(node: &SyntaxNode<YulangLanguage>) -> bool {
    node.kind() == SyntaxKind::InvalidToken
        || node.children().any(|child| has_invalid_token(&child))
}

impl CliOptions {
    fn requests_semantic_pipeline(&self) -> bool {
        self.infer || self.requests_runtime_pipeline()
    }

    fn requests_runtime_pipeline(&self) -> bool {
        self.core_ir
            || self.runtime_ir
            || self.hygiene_ir
            || self.run_interpreter
            || self.control_vm
            || self.control_vm_load.is_some()
            || self.native_compare_i64
            || self.native_abi_lanes
            || self.native_object.is_some()
            || self.native_exe.is_some()
            || self.native_value_exe.is_some()
            || self.native_run.is_some()
            || self.native_run_exe.is_some()
            || self.native_run_value_exe.is_some()
            || self.native_run_cps_repr_exe.is_some()
            || self.native_run_mmtk_cps_repr_exe.is_some()
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
    let (source_set, collect_duration) = collect_infer_source_set_or_exit(path, source, options);
    if source_set_has_invalid_tokens(&source_set) {
        eprintln!("error: invalid token in source");
        process::exit(1);
    }
    if emit_output
        && can_use_yuir_source_cache(options)
        && let Some((module, load_duration)) = read_yuir_source_cache(&source_set)
    {
        run_cached_control_vm_module_or_exit(module, load_duration, options);
        return;
    }

    let InferLowerOutput {
        mut state,
        diagnostic_source,
        lower_profile,
        runtime_dependencies,
        mut pipeline_timings,
    } = lower_infer_sources(
        path,
        root,
        source,
        options,
        Some((&source_set, collect_duration)),
    );

    let finalized = with_infer_profile_enabled(options.infer_phase_timings, || {
        state.finalize_compact_results_profiled()
    });

    let type_errors_start = pipeline_timings.start();
    let errors = state.infer.type_errors();
    pipeline_timings.type_errors = InferPipelineTimings::elapsed(type_errors_start);
    let surface_diagnostics_start = pipeline_timings.start();
    let surface_diagnostics = collect_infer_surface_diagnostics(&state);
    pipeline_timings.surface_diagnostics = InferPipelineTimings::elapsed(surface_diagnostics_start);
    let requests_runtime_pipeline = options.requests_runtime_pipeline();

    let (rendered, render_duration) = if options.infer {
        let render_start = Instant::now();
        let rendered = collect_infer_compact_results(&state);
        let render_duration = render_start.elapsed();
        (Some(rendered), render_duration)
    } else {
        (None, Duration::ZERO)
    };
    pipeline_timings.render = render_duration;

    let (binding_names, quantified_counts) = if options.infer || options.infer_phase_timings {
        let binding_names_start = pipeline_timings.start();
        let binding_names = state
            .ctx
            .collect_binding_paths()
            .into_iter()
            .map(|(path, def)| (def, format_infer_path(&path)))
            .collect::<HashMap<_, _>>();
        pipeline_timings.binding_names = InferPipelineTimings::elapsed(binding_names_start);
        let quantified_counts_start = pipeline_timings.start();
        let quantified_counts = state
            .infer
            .frozen_schemes
            .borrow()
            .iter()
            .map(|(k, v)| (*k, v.quantified.len()))
            .collect::<HashMap<_, _>>();
        pipeline_timings.quantified_counts = InferPipelineTimings::elapsed(quantified_counts_start);
        (Some(binding_names), Some(quantified_counts))
    } else {
        (None, None)
    };

    let infer_program =
        if errors.is_empty() && surface_diagnostics.is_empty() && requests_runtime_pipeline {
            let core_export_start = pipeline_timings.start();
            let program = export_core_program(&mut state);
            pipeline_timings.core_export = InferPipelineTimings::elapsed(core_export_start);
            let runtime_dependency_merge_start = pipeline_timings.start();
            let program =
                merge_runtime_dependencies_or_exit(program, runtime_dependencies.as_ref());
            pipeline_timings.runtime_dependency_merge =
                InferPipelineTimings::elapsed(runtime_dependency_merge_start);
            Some(program)
        } else {
            None
        };

    if emit_output {
        for error in &errors {
            print_infer_type_error(&state, &error, &diagnostic_source);
        }
        for diagnostic in &surface_diagnostics {
            print_infer_surface_diagnostic(diagnostic, &diagnostic_source);
        }
        if requests_runtime_pipeline && (!errors.is_empty() || !surface_diagnostics.is_empty()) {
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
                &diagnostic_source,
            );
            print_runtime_module(&lowered.module, options.verbose_ir);
            if options.runtime_phase_timings {
                print_runtime_phase_timings(&lowered.profile, None, None);
            }
        }
        if options.hygiene_ir {
            if options.infer || options.core_ir || options.runtime_ir {
                println!();
            }
            println!("hygiene-ir:");
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            print!("{}", runtime::format_hygiene_module(&lowered.module));
            if options.runtime_phase_timings {
                print_runtime_phase_timings(&lowered.profile, None, None);
            }
        }
        if options.run_interpreter {
            if options.infer || options.core_ir || options.runtime_ir || options.hygiene_ir {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
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
            let mut results = Vec::new();
            let mut host_stdout = String::new();
            for index in 0..module.module().root_exprs.len() {
                let result =
                    match runtime::eval_root_with_basic_host(&module, index, &mut host_stdout) {
                        Ok(result) => result,
                        Err(err) => {
                            eprintln!("failed to evaluate runtime IR: {err}");
                            process::exit(1);
                        }
                    };
                if !host_stdout.is_empty() {
                    print!("{host_stdout}");
                    host_stdout.clear();
                }
                results.push(result.0);
            }
            let eval_duration = eval_start.elapsed();
            if options.runtime_phase_timings {
                print_runtime_phase_timings(
                    &lowered.profile,
                    Some(compile_duration),
                    Some(eval_duration),
                );
            }
            if options.print_roots {
                for (index, result) in results.iter().enumerate() {
                    println!("[{index}] {}", format_runtime_vm_result(result));
                }
            }
        }
        if options.native_compare_i64 {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.control_vm
                || options.native_abi_lanes
                || options.native_object.is_some()
                || options.native_exe.is_some()
                || options.native_value_exe.is_some()
                || options.native_run.is_some()
                || options.native_run_exe.is_some()
                || options.native_run_value_exe.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let compare_start = Instant::now();
            if let Err(err) = yulang_native::compare_module_i64(&lowered.module) {
                eprintln!("native compare failed: {err}");
                process::exit(1);
            }
            let compare_duration = compare_start.elapsed();
            if options.runtime_phase_timings {
                print_runtime_phase_timings(&lowered.profile, None, None);
                eprintln!(
                    "    native_compare_i64: {}",
                    format_duration(compare_duration)
                );
            }
            println!("native-compare-i64: ok");
        }
        if options.control_vm {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.native_compare_i64
                || options.native_abi_lanes
                || options.native_object.is_some()
                || options.native_exe.is_some()
                || options.native_value_exe.is_some()
                || options.native_run.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let compile_start = Instant::now();
            let module = match runtime::compile_control_vm_module(lowered.module) {
                Ok(module) => module,
                Err(err) => {
                    eprintln!("failed to compile control VM: {err}");
                    process::exit(1);
                }
            };
            let compile_duration = compile_start.elapsed();
            if can_write_yuir_source_cache(options) {
                write_yuir_source_cache(&source_set, &module);
            }
            if let Some(path) = &options.control_vm_emit {
                let path = yuir_artifact_output_path(path, options.path.as_deref());
                ensure_parent_dir_or_exit(&path, "YUIR artifact");
                if let Err(err) = module.write_artifact_file(&path) {
                    eprintln!("failed to write YUIR artifact {}: {err}", path.display());
                    process::exit(1);
                }
                if options.runtime_phase_timings {
                    print_runtime_phase_timings(&lowered.profile, Some(compile_duration), None);
                }
                if options.infer_phase_timings {
                    print_infer_phase_timings(
                        &lower_profile,
                        &finalized.profile,
                        &pipeline_timings,
                        finalized.finalized_defs.len(),
                        binding_names.as_ref().expect("binding names"),
                        quantified_counts.as_ref().expect("quantified counts"),
                    );
                }
                if !options.print_roots {
                    println!("build: {}", path.display());
                }
                return;
            }
            let eval_start = Instant::now();
            let mut results = Vec::new();
            let mut profile = runtime::VmProfile::default();
            let mut host_stdout = String::new();
            for index in 0..module.root_count() {
                match module.eval_root_expr_with_basic_host_profiled(index, &mut host_stdout) {
                    Ok((result, item_profile)) => {
                        profile.merge(item_profile);
                        if !host_stdout.is_empty() {
                            print!("{host_stdout}");
                            host_stdout.clear();
                        }
                        results.push(result);
                    }
                    Err(err) => {
                        eprintln!("failed to evaluate control VM: {err}");
                        process::exit(1);
                    }
                }
            }
            let eval_duration = eval_start.elapsed();
            if options.runtime_phase_timings {
                print_runtime_phase_timings(
                    &lowered.profile,
                    Some(compile_duration),
                    Some(eval_duration),
                );
                eprintln!(
                    "    vm_profile: eval_expr_calls={} max_eval_depth={} continuation_steps={} max_continuation_frames={}",
                    profile.eval_expr_calls,
                    profile.max_eval_depth,
                    profile.continuation_steps,
                    profile.max_continuation_frames
                );
            }
            if options.print_roots {
                for (index, result) in results.iter().enumerate() {
                    println!("[{index}] {}", format_runtime_vm_result(result));
                }
            }
        }
        if options.native_abi_lanes {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.control_vm
                || options.native_compare_i64
                || options.native_object.is_some()
                || options.native_exe.is_some()
                || options.native_value_exe.is_some()
                || options.native_run.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            print_native_abi_lanes_or_exit(&lowered.module);
        }
        if let Some(path) = &options.native_object {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.native_compare_i64
                || options.native_abi_lanes
                || options.native_exe.is_some()
                || options.native_value_exe.is_some()
                || options.native_run.is_some()
                || options.native_run_exe.is_some()
                || options.native_run_value_exe.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let path = native_object_output_path(path, options.path.as_deref());
            write_native_object_or_exit(&lowered.module, &path);
        }
        if let Some(path) = &options.native_exe {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.native_compare_i64
                || options.native_abi_lanes
                || options.native_object.is_some()
                || options.native_value_exe.is_some()
                || options.native_run.is_some()
                || options.native_run_exe.is_some()
                || options.native_run_value_exe.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let path = native_executable_output_path(path, options.path.as_deref());
            write_native_executable_or_exit(&lowered.module, &path, options.print_roots);
        }
        if let Some(path) = &options.native_value_exe {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.native_compare_i64
                || options.native_abi_lanes
                || options.native_object.is_some()
                || options.native_exe.is_some()
                || options.native_run.is_some()
                || options.native_run_exe.is_some()
                || options.native_run_value_exe.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let path = native_value_executable_output_path(path, options.path.as_deref());
            write_native_value_executable_or_exit(&lowered.module, &path, options.print_roots);
        }
        if let Some(path) = &options.native_run {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.native_compare_i64
                || options.native_abi_lanes
                || options.native_object.is_some()
                || options.native_exe.is_some()
                || options.native_value_exe.is_some()
                || options.native_run_exe.is_some()
                || options.native_run_value_exe.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let path = native_run_executable_output_path(path, options.path.as_deref());
            write_native_run_executable_or_exit(&lowered.module, &path, options.print_roots);
            run_native_executable_or_exit(&path, "native-run");
        }
        if let Some(path) = &options.native_run_exe {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.native_compare_i64
                || options.native_abi_lanes
                || options.native_object.is_some()
                || options.native_exe.is_some()
                || options.native_value_exe.is_some()
                || options.native_run.is_some()
                || options.native_run_value_exe.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let path = native_executable_output_path(path, options.path.as_deref());
            write_native_executable_or_exit(&lowered.module, &path, options.print_roots);
            run_native_executable_or_exit(&path, "native-run-exe");
        }
        if let Some(path) = &options.native_run_value_exe {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.native_compare_i64
                || options.native_abi_lanes
                || options.native_object.is_some()
                || options.native_exe.is_some()
                || options.native_value_exe.is_some()
                || options.native_run.is_some()
                || options.native_run_exe.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let path = native_value_executable_output_path(path, options.path.as_deref());
            write_native_value_executable_or_exit(&lowered.module, &path, options.print_roots);
            run_native_executable_or_exit(&path, "native-run-pure-exe");
        }
        if let Some(path) = &options.native_run_cps_repr_exe {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.native_compare_i64
                || options.native_abi_lanes
                || options.native_object.is_some()
                || options.native_exe.is_some()
                || options.native_value_exe.is_some()
                || options.native_run.is_some()
                || options.native_run_exe.is_some()
                || options.native_run_value_exe.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let path = native_cps_repr_executable_output_path(path, options.path.as_deref());
            write_native_cps_repr_executable_or_exit(&lowered.module, &path, options.print_roots);
            run_native_executable_or_exit(&path, "native-run");
        }
        if let Some(path) = &options.native_run_mmtk_cps_repr_exe {
            if options.infer
                || options.core_ir
                || options.runtime_ir
                || options.hygiene_ir
                || options.run_interpreter
                || options.native_compare_i64
                || options.native_abi_lanes
                || options.native_object.is_some()
                || options.native_exe.is_some()
                || options.native_value_exe.is_some()
                || options.native_run.is_some()
                || options.native_run_exe.is_some()
                || options.native_run_value_exe.is_some()
                || options.native_run_cps_repr_exe.is_some()
            {
                println!();
            }
            let lowered = lower_runtime_module_or_exit(
                infer_program.as_ref().expect("core program"),
                options.runtime_phase_timings,
                &diagnostic_source,
            );
            let path = native_mmtk_cps_repr_executable_output_path(path, options.path.as_deref());
            write_native_mmtk_cps_repr_executable_or_exit(
                &lowered.module,
                &path,
                options.print_roots,
            );
            run_native_executable_or_exit(&path, "native-run-mmtk");
        }
        if options.infer_phase_timings {
            print_infer_phase_timings(
                &lower_profile,
                &finalized.profile,
                &pipeline_timings,
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
    program: &typed_ir::CoreProgram,
    print_timings: bool,
    source: &str,
) -> RuntimeLowerOutput {
    let lower_start = Instant::now();
    let (module, lower_profile) = if print_timings {
        match runtime::lower_core_program_profiled(program.clone()) {
            Ok(output) => (output.module, output.profile),
            Err(err) => {
                eprintln!("error: {err}");
                if let Some(frame) = runtime_error_source_frame(&err, program, source) {
                    eprint!("{frame}");
                }
                process::exit(1);
            }
        }
    } else {
        match runtime::lower_core_program(program.clone()) {
            Ok(module) => (module, runtime::RuntimeLowerProfile::default()),
            Err(err) => {
                eprintln!("error: {err}");
                if let Some(frame) = runtime_error_source_frame(&err, program, source) {
                    eprint!("{frame}");
                }
                process::exit(1);
            }
        }
    };
    let lower = lower_start.elapsed();
    let mono_start = Instant::now();
    let (module, monomorphize_profile) = if print_timings {
        match runtime::monomorphize_module_profiled(module) {
            Ok(output) => output,
            Err(err) => {
                eprintln!("error: {err}");
                process::exit(1);
            }
        }
    } else {
        match runtime::monomorphize_module(module) {
            Ok(module) => (module, runtime::MonomorphizeProfile::default()),
            Err(err) => {
                eprintln!("error: {err}");
                process::exit(1);
            }
        }
    };
    let monomorphize = mono_start.elapsed();
    let profile = RuntimePhaseProfile {
        lower,
        lower_profile,
        monomorphize,
        monomorphize_profile,
    };
    RuntimeLowerOutput { module, profile }
}

fn print_native_abi_lanes_or_exit(module: &runtime::Module) {
    let native = match yulang_native::lower_module(module) {
        Ok(module) => module,
        Err(err) => {
            eprintln!("failed to lower native control IR: {err}");
            process::exit(1);
        }
    };
    let closure = yulang_native::closure_convert_module(&native);
    let abi = yulang_native::lower_closure_module_to_abi(&closure);
    let reprs = yulang_native::analyze_abi_reprs(&abi);
    let mut entries = reprs.functions.into_iter().collect::<Vec<_>>();
    entries.sort_by(|(left, _), (right, _)| left.cmp(right));
    println!("native-abi-reprs:");
    for (name, repr) in entries {
        println!("  {name}: {}", format_native_abi_repr(&repr));
    }
}

fn write_native_object_or_exit(module: &runtime::Module, path: &Path) {
    let (object, _) = compile_native_object_or_exit(module);
    ensure_parent_dir_or_exit(path, "native object");
    if let Err(err) = fs::write(path, object.bytes()) {
        eprintln!("failed to write native object {}: {err}", path.display());
        process::exit(1);
    }
    println!(
        "native-object: wrote {} bytes to {}",
        object.bytes().len(),
        path.display()
    );
}

fn write_native_executable_or_exit(module: &runtime::Module, path: &Path, print_roots: bool) {
    let (object, roots) = compile_native_object_or_exit(module);
    ensure_parent_dir_or_exit(path, "native executable");
    let temp_dir = native_link_temp_dir();
    if let Err(err) = fs::create_dir_all(&temp_dir) {
        eprintln!(
            "failed to create native link temp dir {}: {err}",
            temp_dir.display()
        );
        process::exit(1);
    }
    let object_path = temp_dir.join("module.o");
    let harness_path = temp_dir.join("main.rs");
    let cleanup = || {
        let _ = fs::remove_dir_all(&temp_dir);
    };
    if let Err(err) = fs::write(&object_path, object.bytes()) {
        eprintln!(
            "failed to write native object {}: {err}",
            object_path.display()
        );
        cleanup();
        process::exit(1);
    }
    let harness = native_executable_harness(&roots, print_roots);
    if let Err(err) = fs::write(&harness_path, harness) {
        eprintln!(
            "failed to write native executable harness {}: {err}",
            harness_path.display()
        );
        cleanup();
        process::exit(1);
    }
    let output = match Command::new("cc")
        .arg(&harness_path)
        .arg(&object_path)
        .arg("-o")
        .arg(path)
        .output()
    {
        Ok(output) => output,
        Err(err) => {
            eprintln!("failed to run cc for native executable: {err}");
            cleanup();
            process::exit(1);
        }
    };
    if !output.status.success() {
        eprintln!("failed to link native executable with cc");
        if !output.stdout.is_empty() {
            eprintln!("{}", String::from_utf8_lossy(&output.stdout));
        }
        if !output.stderr.is_empty() {
            eprintln!("{}", String::from_utf8_lossy(&output.stderr));
        }
        cleanup();
        process::exit(1);
    }
    cleanup();
    eprintln!("native-exe: wrote {}", path.display());
}

fn write_native_run_executable_or_exit(module: &runtime::Module, path: &Path, print_roots: bool) {
    if let Err(cps_error) =
        write_native_cps_repr_executable(module, path, "native-run(effects)", print_roots)
    {
        eprintln!("failed to compile native-run executable");
        eprintln!("  effects backend: {cps_error}");
        process::exit(1);
    }
}

fn write_native_value_executable_or_exit(module: &runtime::Module, path: &Path, print_roots: bool) {
    if let Err(err) = write_native_value_executable(module, path, "native-pure-exe", print_roots) {
        eprintln!("{err}");
        process::exit(1);
    }
}

fn write_native_value_executable(
    module: &runtime::Module,
    path: &Path,
    label: &str,
    print_roots: bool,
) -> Result<(), NativeValueExecutableError> {
    let object = compile_native_value_object(module)?;
    let support_library = build_native_runtime_staticlib_or_exit();
    ensure_parent_dir_or_exit(path, "native pure-subset executable");
    let temp_dir = native_link_temp_dir();
    if let Err(err) = fs::create_dir_all(&temp_dir) {
        return Err(NativeValueExecutableError::Fatal(format!(
            "failed to create native value link temp dir {}: {err}",
            temp_dir.display()
        )));
    }
    let object_path = temp_dir.join("module.o");
    let harness_path = temp_dir.join("main.c");
    let cleanup = || {
        let _ = fs::remove_dir_all(&temp_dir);
    };
    if let Err(err) = fs::write(&object_path, object.bytes()) {
        let message = format!(
            "failed to write native value object {}: {err}",
            object_path.display()
        );
        cleanup();
        return Err(NativeValueExecutableError::Fatal(message));
    }
    let harness = native_value_executable_harness(object.roots(), print_roots);
    if let Err(err) = fs::write(&harness_path, harness) {
        let message = format!(
            "failed to write native pure-subset executable harness {}: {err}",
            harness_path.display()
        );
        cleanup();
        return Err(NativeValueExecutableError::Fatal(message));
    }
    let output = match Command::new("cc")
        .arg(&harness_path)
        .arg(&object_path)
        .arg(&support_library)
        .arg("-pthread")
        .arg("-ldl")
        .arg("-lm")
        .arg("-o")
        .arg(path)
        .output()
    {
        Ok(output) => output,
        Err(err) => {
            cleanup();
            return Err(NativeValueExecutableError::Fatal(format!(
                "failed to run cc for native pure-subset executable: {err}"
            )));
        }
    };
    if !output.status.success() {
        let message = command_failure_message(
            "failed to link native pure-subset executable with cc",
            &output,
        );
        cleanup();
        return Err(NativeValueExecutableError::Fatal(message));
    }
    cleanup();
    eprintln!("{label}: wrote {}", path.display());
    Ok(())
}

fn write_native_cps_repr_executable_or_exit(
    module: &runtime::Module,
    path: &Path,
    print_roots: bool,
) {
    if let Err(err) = write_native_cps_repr_executable_with_options(
        module,
        path,
        "native-run",
        print_roots,
        yulang_native::CpsReprCraneliftOptions::default(),
    ) {
        eprintln!("{err}");
        process::exit(1);
    }
}

fn write_native_mmtk_cps_repr_executable_or_exit(
    module: &runtime::Module,
    path: &Path,
    print_roots: bool,
) {
    if let Err(err) = write_native_cps_repr_executable_with_options(
        module,
        path,
        "native-run-mmtk",
        print_roots,
        yulang_native::CpsReprCraneliftOptions::mmtk_yvalue_primitives(),
    ) {
        eprintln!("{err}");
        process::exit(1);
    }
}

fn write_native_cps_repr_executable(
    module: &runtime::Module,
    path: &Path,
    label: &str,
    print_roots: bool,
) -> Result<(), String> {
    write_native_cps_repr_executable_with_options(
        module,
        path,
        label,
        print_roots,
        yulang_native::CpsReprCraneliftOptions::default(),
    )
}

fn write_native_cps_repr_executable_with_options(
    module: &runtime::Module,
    path: &Path,
    label: &str,
    print_roots: bool,
    options: yulang_native::CpsReprCraneliftOptions,
) -> Result<(), String> {
    let compile_module = module;
    let object = compile_native_cps_repr_object_with_options(compile_module, options)?;
    let support_library = build_native_runtime_staticlib_or_exit();
    ensure_parent_dir_or_exit(path, "native effects executable");
    let temp_dir = native_link_temp_dir();
    if let Err(err) = fs::create_dir_all(&temp_dir) {
        return Err(format!(
            "failed to create native effects link temp dir {}: {err}",
            temp_dir.display()
        ));
    }
    let object_path = temp_dir.join("module.o");
    let harness_path = temp_dir.join("main.rs");
    let cleanup = || {
        let _ = fs::remove_dir_all(&temp_dir);
    };
    if let Err(err) = fs::write(&object_path, object.bytes()) {
        let message = format!(
            "failed to write native effects object {}: {err}",
            object_path.display()
        );
        cleanup();
        return Err(message);
    }
    let roots = native_cps_root_harness_entries(compile_module, &object, options);
    let harness = native_cps_repr_executable_harness(&roots, print_roots, options);
    if let Err(err) = fs::write(&harness_path, harness) {
        let message = format!(
            "failed to write native effects executable harness {}: {err}",
            harness_path.display()
        );
        cleanup();
        return Err(message);
    }
    let output = match Command::new("rustc")
        .arg("--edition=2024")
        .arg(&harness_path)
        .arg("-C")
        .arg("relocation-model=static")
        .arg("-C")
        .arg("link-arg=-no-pie")
        .arg("-C")
        .arg(format!("link-arg={}", object_path.display()))
        .arg("-C")
        .arg(format!("link-arg={}", support_library.display()))
        .arg("-o")
        .arg(path)
        .output()
    {
        Ok(output) => output,
        Err(err) => {
            cleanup();
            return Err(format!(
                "failed to run rustc for native effects executable: {err}"
            ));
        }
    };
    if !output.status.success() {
        let message = command_failure_message(
            "failed to link native effects executable with rustc",
            &output,
        );
        cleanup();
        return Err(message);
    }
    cleanup();
    eprintln!("{label}: wrote {}", path.display());
    Ok(())
}

fn native_cps_root_harness_entries(
    module: &runtime::Module,
    object: &yulang_native::CpsReprObjectModule,
    options: yulang_native::CpsReprCraneliftOptions,
) -> Vec<NativeRootHarnessEntry> {
    let root_prints = native_root_print_entries_from_runtime(module);
    object
        .roots()
        .iter()
        .enumerate()
        .map(|(index, name)| {
            let lane = object
                .root_lanes()
                .get(index)
                .copied()
                .unwrap_or(yulang_native::CpsReprAbiLane::Unknown);
            let runtime_kind = root_prints
                .get(index)
                .map(|root| root.print)
                .unwrap_or(NativeRootPrintKind::RuntimeValueI64);
            let print = if options.mmtk_yvalue_primitives {
                native_root_print_kind_from_mmtk_cps_lane(lane)
            } else {
                native_root_print_kind_from_cps_lane_and_runtime_type(lane, runtime_kind)
            };
            NativeRootHarnessEntry {
                name: name.clone(),
                function_id: object.root_function_ids().get(index).copied(),
                print,
            }
        })
        .collect()
}

fn command_failure_message(message: &str, output: &std::process::Output) -> String {
    let mut result = message.to_string();
    if !output.stdout.is_empty() {
        result.push('\n');
        result.push_str(&String::from_utf8_lossy(&output.stdout));
    }
    if !output.stderr.is_empty() {
        result.push('\n');
        result.push_str(&String::from_utf8_lossy(&output.stderr));
    }
    result
}

#[derive(Debug)]
enum NativeValueExecutableError {
    Unsupported(String),
    Fatal(String),
}

impl std::fmt::Display for NativeValueExecutableError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NativeValueExecutableError::Unsupported(message)
            | NativeValueExecutableError::Fatal(message) => write!(f, "{message}"),
        }
    }
}

fn run_native_executable_or_exit(path: &Path, label: &str) {
    let output = match Command::new(path).output() {
        Ok(output) => output,
        Err(err) => {
            eprintln!("failed to run native executable {}: {err}", path.display());
            process::exit(1);
        }
    };
    if !output.stdout.is_empty() {
        print!("{}", String::from_utf8_lossy(&output.stdout));
    }
    if !output.stderr.is_empty() {
        eprint!("{}", String::from_utf8_lossy(&output.stderr));
    }
    if !output.status.success() {
        eprintln!("{label}: executable exited with {}", output.status);
        process::exit(output.status.code().unwrap_or(1));
    }
}

fn native_object_output_path(output: &NativeOutput, input_path: Option<&str>) -> PathBuf {
    match output {
        NativeOutput::Path(path) => PathBuf::from(path),
        NativeOutput::Default => yulang_sources::YulangCachePaths::for_project(workspace_root())
            .project_obj
            .join(format!("{}.o", native_output_stem(input_path))),
    }
}

fn native_executable_output_path(output: &NativeOutput, input_path: Option<&str>) -> PathBuf {
    match output {
        NativeOutput::Path(path) => PathBuf::from(path),
        NativeOutput::Default => yulang_sources::YulangCachePaths::for_project(workspace_root())
            .project_bin
            .join(native_output_stem(input_path)),
    }
}

fn native_run_executable_output_path(output: &NativeOutput, input_path: Option<&str>) -> PathBuf {
    match output {
        NativeOutput::Path(path) => PathBuf::from(path),
        NativeOutput::Default => yulang_sources::YulangCachePaths::for_project(workspace_root())
            .project_bin
            .join(format!("{}-native", native_output_stem(input_path))),
    }
}

fn native_value_executable_output_path(output: &NativeOutput, input_path: Option<&str>) -> PathBuf {
    match output {
        NativeOutput::Path(path) => PathBuf::from(path),
        NativeOutput::Default => yulang_sources::YulangCachePaths::for_project(workspace_root())
            .project_bin
            .join(format!("{}-pure", native_output_stem(input_path))),
    }
}

fn native_cps_repr_executable_output_path(
    output: &NativeOutput,
    input_path: Option<&str>,
) -> PathBuf {
    match output {
        NativeOutput::Path(path) => PathBuf::from(path),
        NativeOutput::Default => yulang_sources::YulangCachePaths::for_project(workspace_root())
            .project_bin
            .join(format!("{}-effects", native_output_stem(input_path))),
    }
}

fn native_mmtk_cps_repr_executable_output_path(
    output: &NativeOutput,
    input_path: Option<&str>,
) -> PathBuf {
    match output {
        NativeOutput::Path(path) => PathBuf::from(path),
        NativeOutput::Default => yulang_sources::YulangCachePaths::for_project(workspace_root())
            .project_bin
            .join(format!("{}-mmtk", native_output_stem(input_path))),
    }
}

fn yuir_artifact_output_path(output: &NativeOutput, input_path: Option<&str>) -> PathBuf {
    match output {
        NativeOutput::Path(path) => PathBuf::from(path),
        NativeOutput::Default => yulang_sources::YulangCachePaths::for_project(workspace_root())
            .project_target_root
            .join("yuir")
            .join(format!("{}.yuir", native_output_stem(input_path))),
    }
}

fn is_yuir_artifact_path(path: &str) -> bool {
    Path::new(path)
        .extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extension.eq_ignore_ascii_case("yuir"))
}

fn native_output_stem(input_path: Option<&str>) -> String {
    let stem = input_path
        .and_then(|path| Path::new(path).file_stem())
        .and_then(|stem| stem.to_str())
        .unwrap_or("stdin");
    let sanitized = stem
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || matches!(ch, '_' | '-' | '.') {
                ch
            } else {
                '_'
            }
        })
        .collect::<String>();
    if sanitized.is_empty() {
        "main".to_string()
    } else {
        sanitized
    }
}

fn build_native_runtime_staticlib_or_exit() -> PathBuf {
    let workspace = workspace_root();
    if let Some(path) = env::var_os("YULANG_NATIVE_RUNTIME_LIB").map(PathBuf::from) {
        if path.is_file() {
            return path;
        }
        eprintln!(
            "YULANG_NATIVE_RUNTIME_LIB points to a missing file: {}",
            path.display()
        );
        process::exit(1);
    }
    let path = native_runtime_staticlib_path(&workspace);
    if native_runtime_support_is_fresh(&workspace, &path) {
        return path;
    }
    let output = match Command::new("cargo")
        .arg("build")
        .arg("-q")
        .arg("-p")
        .arg("yulang-native")
        .current_dir(&workspace)
        .output()
    {
        Ok(output) => output,
        Err(err) => {
            eprintln!("failed to run cargo build for native runtime support: {err}");
            process::exit(1);
        }
    };
    if !output.status.success() {
        eprintln!("failed to build native runtime support static library");
        if !output.stdout.is_empty() {
            eprintln!("{}", String::from_utf8_lossy(&output.stdout));
        }
        if !output.stderr.is_empty() {
            eprintln!("{}", String::from_utf8_lossy(&output.stderr));
        }
        process::exit(1);
    }
    if !path.is_file() {
        eprintln!(
            "native runtime support static library was not produced at {}",
            path.display()
        );
        process::exit(1);
    }
    path
}

fn native_runtime_staticlib_path(workspace: &Path) -> PathBuf {
    native_target_dir(workspace).join("debug/libyulang_native.a")
}

fn native_target_dir(workspace: &Path) -> PathBuf {
    match env::var_os("CARGO_TARGET_DIR").map(PathBuf::from) {
        Some(path) if path.is_absolute() => path,
        Some(path) => workspace.join(path),
        None => workspace.join("target"),
    }
}

fn native_runtime_support_is_fresh(workspace: &Path, library: &Path) -> bool {
    let Ok(library_modified) = file_modified(library) else {
        return false;
    };
    let source_roots = [
        workspace.join("Cargo.lock"),
        workspace.join("crates/yulang-native/Cargo.toml"),
        workspace.join("crates/yulang-native/src"),
        workspace.join("crates/yulang-runtime/Cargo.toml"),
        workspace.join("crates/yulang-runtime/src"),
        workspace.join("crates/yulang-typed-ir/Cargo.toml"),
        workspace.join("crates/yulang-typed-ir/src"),
    ];
    let newest_source = source_roots
        .iter()
        .filter_map(|path| newest_modified(path).ok())
        .max();
    newest_source.is_some_and(|modified| modified <= library_modified)
}

fn newest_modified(path: &Path) -> io::Result<SystemTime> {
    let metadata = fs::metadata(path)?;
    if metadata.is_file() {
        return metadata.modified();
    }
    let mut newest = metadata.modified()?;
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let modified = newest_modified(&entry.path())?;
        if modified > newest {
            newest = modified;
        }
    }
    Ok(newest)
}

fn file_modified(path: &Path) -> io::Result<SystemTime> {
    fs::metadata(path)?.modified()
}

fn compile_native_object_or_exit(
    module: &runtime::Module,
) -> (
    yulang_native::NativeObjectModule,
    Vec<NativeRootHarnessEntry>,
) {
    let native = match yulang_native::lower_module(module) {
        Ok(module) => module,
        Err(err) => {
            eprintln!("failed to lower native control IR: {err}");
            process::exit(1);
        }
    };
    let closure = yulang_native::closure_convert_module(&native);
    let abi = yulang_native::lower_closure_module_to_abi(&closure);
    let reprs = yulang_native::analyze_abi_reprs(&abi);
    let roots = abi
        .roots
        .iter()
        .map(|root| NativeRootHarnessEntry {
            name: root.name.clone(),
            function_id: None,
            print: reprs
                .function_repr(&root.name)
                .map(native_root_print_kind_from_abi_repr)
                .unwrap_or(NativeRootPrintKind::I64),
        })
        .collect::<Vec<_>>();
    let object = match yulang_native::compile_abi_module_to_object(&abi) {
        Ok(object) => object,
        Err(err) => {
            eprintln!("failed to compile native object: {err}");
            process::exit(1);
        }
    };
    (object, roots)
}

fn compile_native_value_object(
    module: &runtime::Module,
) -> Result<yulang_native::NativeValueObjectModule, NativeValueExecutableError> {
    let native = yulang_native::lower_module(module).map_err(classify_native_value_lower_error)?;
    let closure = yulang_native::closure_convert_module(&native);
    let abi = yulang_native::lower_closure_module_to_abi(&closure);
    yulang_native::compile_value_abi_module_to_object(&abi)
        .map_err(classify_native_value_cranelift_error)
}

fn compile_native_cps_repr_object_with_options(
    module: &runtime::Module,
    options: yulang_native::CpsReprCraneliftOptions,
) -> Result<yulang_native::CpsReprObjectModule, String> {
    yulang_native::compile_runtime_module_to_cps_repr_object_with_options(module, options)
        .map_err(|err| format!("failed to compile native effects object: {err}"))
}

fn classify_native_value_lower_error(
    err: yulang_native::NativeLowerError,
) -> NativeValueExecutableError {
    use yulang_native::NativeLowerError;
    let message = format!("failed to lower native control IR: {err}");
    match err {
        NativeLowerError::UnsupportedRoot { .. }
        | NativeLowerError::UnsupportedExpr { .. }
        | NativeLowerError::UnsupportedPattern { .. }
        | NativeLowerError::UnsupportedBinding { .. } => {
            NativeValueExecutableError::Unsupported(message)
        }
        NativeLowerError::MissingRootExpr { .. }
        | NativeLowerError::PrimitiveArityMismatch { .. }
        | NativeLowerError::CallArityMismatch { .. }
        | NativeLowerError::Archived => NativeValueExecutableError::Fatal(message),
    }
}

fn classify_native_value_cranelift_error(
    err: yulang_native::NativeValueCraneliftError,
) -> NativeValueExecutableError {
    use yulang_native::NativeValueCraneliftError;
    let message = format!("failed to compile native value object: {err}");
    match err {
        NativeValueCraneliftError::UnsupportedFunction { .. }
        | NativeValueCraneliftError::UnsupportedStmt { .. }
        | NativeValueCraneliftError::UnsupportedLiteral { .. } => {
            NativeValueExecutableError::Unsupported(message)
        }
        NativeValueCraneliftError::AbiInvalid(_)
        | NativeValueCraneliftError::MissingBlock { .. }
        | NativeValueCraneliftError::MissingValue { .. }
        | NativeValueCraneliftError::InvalidReturnArity { .. }
        | NativeValueCraneliftError::Cranelift(_)
        | NativeValueCraneliftError::Archived => NativeValueExecutableError::Fatal(message),
    }
}

fn ensure_parent_dir_or_exit(path: &Path, kind: &str) {
    let Some(parent) = path.parent() else {
        return;
    };
    if parent.as_os_str().is_empty() {
        return;
    }
    if let Err(err) = fs::create_dir_all(parent) {
        eprintln!(
            "failed to create {kind} output directory {}: {err}",
            parent.display()
        );
        process::exit(1);
    }
}

fn native_link_temp_dir() -> PathBuf {
    let millis = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis();
    yulang_sources::YulangCachePaths::for_project(workspace_root())
        .project_build
        .join(format!("native-link-{}-{millis}", process::id()))
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../.."))
}

fn native_executable_harness(roots: &[NativeRootHarnessEntry], print_roots: bool) -> String {
    let mut source = String::from("#include <stdio.h>\n#include <stdint.h>\n\n");
    native_abi_executable_harness(roots, print_roots, &mut source);
    source
}

fn native_abi_executable_harness(
    roots: &[NativeRootHarnessEntry],
    print_roots: bool,
    source: &mut String,
) {
    for root in roots {
        let name = &root.name;
        if !is_c_identifier(name) {
            eprintln!("native root symbol `{name}` cannot be called from the C harness");
            process::exit(1);
        }
        source.push_str(root.print.c_abi_return_type());
        source.push(' ');
        source.push_str(name);
        source.push_str("(void);\n");
    }
    source.push_str("\nint main(void) {\n");
    for root in roots {
        let name = &root.name;
        if print_roots {
            root.print.push_c_print_call(source, name);
        } else {
            source.push_str("    (void)");
            source.push_str(name);
            source.push_str("();\n");
        }
    }
    source.push_str("    return 0;\n}\n");
}

fn native_value_executable_harness(roots: &[String], print_roots: bool) -> String {
    let mut source = String::from(
        r#"#include <stdint.h>
#include <stdio.h>

void *yulang_native_context_new(void);
void yulang_native_context_free(void *context);
void yulang_native_print_value(void *value);

"#,
    );
    for root in roots {
        if !is_c_identifier(root) {
            eprintln!("native root symbol `{root}` cannot be called from the C harness");
            process::exit(1);
        }
        source.push_str("void *");
        source.push_str(root);
        source.push_str("(void *context);\n");
    }
    source.push_str("\nint main(void) {\n    void *context = yulang_native_context_new();\n");
    for root in roots {
        if print_roots {
            source.push_str("    yulang_native_print_value(");
            source.push_str(root);
            source.push_str("(context));\n    putchar('\\n');\n    fflush(stdout);\n");
        } else {
            source.push_str("    (void)");
            source.push_str(root);
            source.push_str("(context);\n");
        }
    }
    source.push_str("    yulang_native_context_free(context);\n    return 0;\n}\n");
    source
}

fn native_cps_repr_executable_harness(
    roots: &[NativeRootHarnessEntry],
    print_roots: bool,
    options: yulang_native::CpsReprCraneliftOptions,
) -> String {
    let mut source = String::from("unsafe extern \"C\" {\n");
    source.push_str("    fn yulang_cps_reset_i64();\n");
    source.push_str("    fn yulang_cps_dump_stats_i64();\n");
    source.push_str("    fn yulang_cps_set_root_function_ids_i64(ids: *const u64, len: usize);\n");
    source.push_str("    fn yulang_cps_take_root_result_i64(value: i64) -> i64;\n");
    let uses_mmtk_yvalue_lane = options.mmtk_yvalue_primitives;
    if uses_mmtk_yvalue_lane {
        source.push_str("    fn yulang_mmtk_cps_reset_i64();\n");
        source.push_str("    fn yulang_mmtk_cps_dump_heap_stats_i64();\n");
    }
    if print_roots {
        source.push_str("    fn yulang_cps_print_i64(value: i64);\n");
        source.push_str("    fn yulang_cps_print_debug_i64(value: i64);\n");
        if uses_mmtk_yvalue_lane {
            source.push_str("    fn yulang_mmtk_cps_print_debug_i64(value: i64);\n");
        }
        if roots
            .iter()
            .any(|root| root.print == NativeRootPrintKind::Float)
        {
            source.push_str("    fn yulang_cps_float_to_string_f64(value: f64) -> i64;\n");
        }
    }
    for root in roots {
        let name = &root.name;
        if !is_c_identifier(name) {
            eprintln!("native effects root symbol `{name}` cannot be called from the Rust harness");
            process::exit(1);
        }
        source.push_str("    fn ");
        source.push_str(name);
        source.push_str("() -> ");
        source.push_str(root.print.rust_abi_return_type());
        source.push_str(";\n");
    }
    source.push_str("}\n\n");
    source.push_str("static YULANG_CPS_ROOT_FUNCTION_IDS: [u64; ");
    source.push_str(&roots.len().to_string());
    source.push_str("] = [");
    for (index, root) in roots.iter().enumerate() {
        if index > 0 {
            source.push_str(", ");
        }
        source.push_str(&root.function_id.unwrap_or(0).to_string());
    }
    source.push_str("];\n\nfn main() {\n");
    for root in roots {
        let name = &root.name;
        source.push_str("    unsafe {\n");
        source.push_str("        yulang_cps_reset_i64();\n");
        if uses_mmtk_yvalue_lane {
            source.push_str("        yulang_mmtk_cps_reset_i64();\n");
        }
        source.push_str(
            "        yulang_cps_set_root_function_ids_i64(YULANG_CPS_ROOT_FUNCTION_IDS.as_ptr(), YULANG_CPS_ROOT_FUNCTION_IDS.len());\n",
        );
        if print_roots {
            root.print.push_rust_print_call(&mut source, name);
        } else {
            root.print.push_rust_discard_call(&mut source, name);
        }
        source.push_str("        yulang_cps_dump_stats_i64();\n");
        if uses_mmtk_yvalue_lane {
            source.push_str("        yulang_mmtk_cps_dump_heap_stats_i64();\n");
        }
        source.push_str("    }\n");
    }
    source.push_str("}\n");
    source
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NativeRootHarnessEntry {
    name: String,
    function_id: Option<u64>,
    print: NativeRootPrintKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeRootPrintKind {
    I64,
    Bool,
    Unit,
    Float,
    RuntimeValueI64,
    MmtkYValueI64,
}

impl NativeRootPrintKind {
    fn c_abi_return_type(self) -> &'static str {
        match self {
            NativeRootPrintKind::Float => "double",
            NativeRootPrintKind::I64
            | NativeRootPrintKind::Bool
            | NativeRootPrintKind::Unit
            | NativeRootPrintKind::RuntimeValueI64
            | NativeRootPrintKind::MmtkYValueI64 => "int64_t",
        }
    }

    fn rust_abi_return_type(self) -> &'static str {
        match self {
            NativeRootPrintKind::Float => "f64",
            NativeRootPrintKind::I64
            | NativeRootPrintKind::Bool
            | NativeRootPrintKind::Unit
            | NativeRootPrintKind::RuntimeValueI64
            | NativeRootPrintKind::MmtkYValueI64 => "i64",
        }
    }

    fn push_c_print_call(self, source: &mut String, name: &str) {
        match self {
            NativeRootPrintKind::I64 | NativeRootPrintKind::RuntimeValueI64 => {
                source.push_str("    printf(\"%lld\\n\", (long long)");
                source.push_str(name);
                source.push_str("());\n");
            }
            NativeRootPrintKind::MmtkYValueI64 => {
                source.push_str("    printf(\"%lld\\n\", (long long)");
                source.push_str(name);
                source.push_str("());\n");
            }
            NativeRootPrintKind::Bool => {
                source.push_str("    printf(\"%s\\n\", ");
                source.push_str(name);
                source.push_str("() ? \"true\" : \"false\");\n");
            }
            NativeRootPrintKind::Unit => {
                source.push_str("    (void)");
                source.push_str(name);
                source.push_str("();\n    puts(\"()\");\n");
            }
            NativeRootPrintKind::Float => {
                source.push_str("    printf(\"%.17g\\n\", ");
                source.push_str(name);
                source.push_str("());\n");
            }
        }
    }

    fn push_rust_print_call(self, source: &mut String, name: &str) {
        match self {
            NativeRootPrintKind::I64 => {
                source.push_str("        let value = yulang_cps_take_root_result_i64(");
                source.push_str(name);
                source.push_str("());\n        println!(\"{}\", value);\n");
            }
            NativeRootPrintKind::Bool => {
                source.push_str("        let value = yulang_cps_take_root_result_i64(");
                source.push_str(name);
                source.push_str("());\n        println!(\"{}\", value != 0);\n");
            }
            NativeRootPrintKind::Unit => {
                source.push_str("        let _ = yulang_cps_take_root_result_i64(");
                source.push_str(name);
                source.push_str("());\n        println!(\"()\");\n");
            }
            NativeRootPrintKind::Float => {
                source.push_str("        let text = yulang_cps_float_to_string_f64(");
                source.push_str(name);
                source.push_str("());\n        yulang_cps_print_i64(text);\n        println!();\n");
            }
            NativeRootPrintKind::RuntimeValueI64 => {
                source.push_str("        let value = yulang_cps_take_root_result_i64(");
                source.push_str(name);
                source.push_str(
                    "());\n        yulang_cps_print_debug_i64(value);\n        println!();\n",
                );
            }
            NativeRootPrintKind::MmtkYValueI64 => {
                source.push_str("        let value = yulang_cps_take_root_result_i64(");
                source.push_str(name);
                source.push_str(
                    "());\n        yulang_mmtk_cps_print_debug_i64(value);\n        println!();\n",
                );
            }
        }
    }

    fn push_rust_discard_call(self, source: &mut String, name: &str) {
        match self {
            NativeRootPrintKind::Float => {
                source.push_str("        let _ = ");
                source.push_str(name);
                source.push_str("();\n");
            }
            NativeRootPrintKind::I64
            | NativeRootPrintKind::Bool
            | NativeRootPrintKind::Unit
            | NativeRootPrintKind::RuntimeValueI64
            | NativeRootPrintKind::MmtkYValueI64 => {
                source.push_str("        let _ = yulang_cps_take_root_result_i64(");
                source.push_str(name);
                source.push_str("());\n");
            }
        }
    }
}

fn native_root_print_kind_from_abi_repr(
    repr: &yulang_native::NativeAbiRepr,
) -> NativeRootPrintKind {
    match repr {
        yulang_native::NativeAbiRepr::Unit => NativeRootPrintKind::Unit,
        yulang_native::NativeAbiRepr::Bool => NativeRootPrintKind::Bool,
        yulang_native::NativeAbiRepr::Float => NativeRootPrintKind::Float,
        yulang_native::NativeAbiRepr::Int => NativeRootPrintKind::I64,
        yulang_native::NativeAbiRepr::List(_)
        | yulang_native::NativeAbiRepr::Tuple(_)
        | yulang_native::NativeAbiRepr::Record(_)
        | yulang_native::NativeAbiRepr::Variant(_)
        | yulang_native::NativeAbiRepr::RuntimeValuePtr(_)
        | yulang_native::NativeAbiRepr::ClosurePtr
        | yulang_native::NativeAbiRepr::Unknown => NativeRootPrintKind::RuntimeValueI64,
    }
}

fn native_root_print_entries_from_runtime(module: &runtime::Module) -> Vec<NativeRootHarnessEntry> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (&binding.name, &binding.body))
        .collect::<std::collections::HashMap<_, _>>();
    module
        .roots
        .iter()
        .enumerate()
        .map(|(index, root)| {
            let ty = match root {
                runtime::Root::Expr(expr_index) => {
                    module.root_exprs.get(*expr_index).map(|expr| &expr.ty)
                }
                runtime::Root::Binding(path) => bindings.get(path).map(|expr| &expr.ty),
            };
            NativeRootHarnessEntry {
                name: format!("root_{index}"),
                function_id: None,
                print: ty
                    .map(native_root_print_kind_from_runtime_type)
                    .unwrap_or(NativeRootPrintKind::RuntimeValueI64),
            }
        })
        .collect()
}

fn native_root_print_kind_from_runtime_type(ty: &runtime::Type) -> NativeRootPrintKind {
    match ty {
        runtime::Type::Core(core) => native_root_print_kind_from_core_type(core),
        runtime::Type::Thunk { .. } | runtime::Type::Fun { .. } | runtime::Type::Unknown => {
            NativeRootPrintKind::RuntimeValueI64
        }
    }
}

fn native_root_print_kind_from_cps_lane_and_runtime_type(
    lane: yulang_native::CpsReprAbiLane,
    runtime_kind: NativeRootPrintKind,
) -> NativeRootPrintKind {
    if runtime_kind == NativeRootPrintKind::Unit {
        return NativeRootPrintKind::Unit;
    }
    if runtime_kind == NativeRootPrintKind::Bool {
        return NativeRootPrintKind::Bool;
    }
    match lane {
        yulang_native::CpsReprAbiLane::NativeFloat => NativeRootPrintKind::Float,
        yulang_native::CpsReprAbiLane::ScalarI64 => match runtime_kind {
            NativeRootPrintKind::Bool => NativeRootPrintKind::Bool,
            NativeRootPrintKind::Unit => NativeRootPrintKind::Unit,
            NativeRootPrintKind::I64 => NativeRootPrintKind::I64,
            NativeRootPrintKind::Float
            | NativeRootPrintKind::RuntimeValueI64
            | NativeRootPrintKind::MmtkYValueI64 => NativeRootPrintKind::RuntimeValueI64,
        },
        yulang_native::CpsReprAbiLane::RuntimeValuePtr
        | yulang_native::CpsReprAbiLane::ClosurePtr
        | yulang_native::CpsReprAbiLane::ThunkPtr
        | yulang_native::CpsReprAbiLane::ResumptionPtr
        | yulang_native::CpsReprAbiLane::OpaqueI64
        | yulang_native::CpsReprAbiLane::Conflict
        | yulang_native::CpsReprAbiLane::Unknown => NativeRootPrintKind::RuntimeValueI64,
    }
}

fn native_root_print_kind_from_mmtk_cps_lane(
    lane: yulang_native::CpsReprAbiLane,
) -> NativeRootPrintKind {
    match lane {
        yulang_native::CpsReprAbiLane::NativeFloat => NativeRootPrintKind::Float,
        _ => NativeRootPrintKind::MmtkYValueI64,
    }
}

fn native_root_print_kind_from_core_type(ty: &typed_ir::Type) -> NativeRootPrintKind {
    let typed_ir::Type::Named { path, args } = ty else {
        return NativeRootPrintKind::RuntimeValueI64;
    };
    if !args.is_empty() {
        return NativeRootPrintKind::RuntimeValueI64;
    }
    match path.segments.last().map(|name| name.0.as_str()) {
        Some("int") => NativeRootPrintKind::I64,
        Some("bool") => NativeRootPrintKind::Bool,
        Some("unit") => NativeRootPrintKind::Unit,
        Some("float") => NativeRootPrintKind::Float,
        _ => NativeRootPrintKind::RuntimeValueI64,
    }
}

fn is_c_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn format_native_abi_repr(repr: &yulang_native::NativeAbiRepr) -> String {
    match repr {
        yulang_native::NativeAbiRepr::Unit => "unit".to_string(),
        yulang_native::NativeAbiRepr::Bool => "bool".to_string(),
        yulang_native::NativeAbiRepr::Int => "int".to_string(),
        yulang_native::NativeAbiRepr::Float => "float".to_string(),
        yulang_native::NativeAbiRepr::List(element) => {
            format!("list<{}>", format_native_abi_repr(element))
        }
        yulang_native::NativeAbiRepr::Tuple(items) => format!(
            "tuple<{}>",
            items
                .iter()
                .map(format_native_abi_repr)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        yulang_native::NativeAbiRepr::Record(fields) => format!(
            "record<{}>",
            fields
                .iter()
                .map(|field| format!("{}: {}", field.name.0, format_native_abi_repr(&field.value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        yulang_native::NativeAbiRepr::Variant(cases) => format!(
            "variant<{}>",
            cases
                .iter()
                .map(|case| match &case.value {
                    Some(value) => format!(":{} {}", case.tag.0, format_native_abi_repr(value)),
                    None => format!(":{}", case.tag.0),
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        yulang_native::NativeAbiRepr::RuntimeValuePtr(kind) => match kind {
            yulang_native::NativeRuntimePtrKind::String => "ptr:str".to_string(),
            yulang_native::NativeRuntimePtrKind::RuntimeValue => "ptr:value".to_string(),
        },
        yulang_native::NativeAbiRepr::ClosurePtr => "ptr:closure".to_string(),
        yulang_native::NativeAbiRepr::Unknown => "unknown".to_string(),
    }
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
    let core_shape = &profile.lower_profile.core_shape;
    eprintln!(
        "    core_shape: exprs={}, applies={}, apply_complete={}, apply_partial={}, apply_missing_evidence={}, apply_missing_context={}, apply_missing_principal={}, apply_with_principal={}, apply_with_substitutions={}, apply_with_substitution_candidates={}, apply_with_principal_elaboration={}, apply_principal_elaboration_complete={}, apply_principal_elaboration_incomplete={}",
        core_shape.exprs,
        core_shape.applies,
        core_shape.apply_complete,
        core_shape.apply_partial,
        core_shape.apply_missing_evidence,
        core_shape.apply_missing_context,
        core_shape.apply_missing_principal,
        core_shape.apply_with_principal,
        core_shape.apply_with_substitutions,
        core_shape.apply_with_substitution_candidates,
        core_shape.apply_with_principal_elaboration,
        core_shape.apply_principal_elaboration_complete,
        core_shape.apply_principal_elaboration_incomplete,
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
            "        {}: duration={}, bindings {}->{}, roots {}->{}, changed_bindings={}, changed_roots={}, added_specializations={}, queue_attempted={}, queue_pushed={}, added=[{}]",
            pass.name,
            format_duration(pass.duration),
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
        print_principal_elaborate_profile(pass);
    }
    if let Some(duration) = vm_compile {
        eprintln!("    vm_compile: {}", format_duration(duration));
    }
    if let Some(duration) = vm_eval {
        eprintln!("    vm_eval: {}", format_duration(duration));
    }
}

fn print_principal_elaborate_profile(profile: &runtime::MonomorphizePassProfile) {
    let subst = &profile.principal_elaborate;
    if subst.stats.is_empty()
        && subst.timings.is_empty()
        && subst.target_skips.is_empty()
        && subst.target_rewrites.is_empty()
    {
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
    eprintln!("            principal_elaborate: {stats}");
    if !subst.timings.is_empty() {
        let mut timings = subst.timings.iter().collect::<Vec<_>>();
        timings.sort_by(|(left_key, left_duration), (right_key, right_duration)| {
            right_duration
                .cmp(left_duration)
                .then_with(|| left_key.cmp(right_key))
        });
        let timings = timings
            .into_iter()
            .take(12)
            .map(|(key, duration)| format!("{key}={}", format_duration(*duration)))
            .collect::<Vec<_>>()
            .join(", ");
        eprintln!("                timings: {timings}");
    }
    let surviving_actionable_skips = subst
        .target_skips
        .iter()
        .filter(|target| target.actionable && target.survives_final_prune == Some(true))
        .count();
    let surviving_benign_skips = subst
        .target_skips
        .iter()
        .filter(|target| !target.actionable && target.survives_final_prune == Some(true))
        .count();
    if surviving_actionable_skips > 0 || surviving_benign_skips > 0 {
        eprintln!(
            "                skip_reachability surviving_actionable_targets={} surviving_benign_targets={}",
            surviving_actionable_skips, surviving_benign_skips
        );
    }
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
            "                skip_target {} total={} survives_final_prune={} actionable={} reasons=[{}] missing_vars=[{}] no_complete_causes=[{}]",
            format_core_path(&target.target),
            total,
            survives_final_prune,
            if target.actionable { "yes" } else { "no" },
            reasons,
            missing_vars,
            no_complete_causes,
        );
    }
    for target in subst.target_rewrites.iter().take(12) {
        let contexts = target
            .contexts
            .iter()
            .take(6)
            .map(|context| format!("{}={}", context.context, context.count))
            .collect::<Vec<_>>()
            .join(", ");
        let phases = target
            .phases
            .iter()
            .take(4)
            .map(|phase| format!("{}={}", phase.phase, format_duration(phase.duration)))
            .collect::<Vec<_>>()
            .join(", ");
        eprintln!(
            "                rewrite_target {} visits={} rewrites={} cached_incomplete={} incomplete={} max_depth={} contexts=[{}] phases=[{}]",
            format_core_path(&target.target),
            target.total_apply_visits,
            target.rewrites,
            target.cached_incomplete,
            target.incomplete,
            target.max_specialization_depth,
            contexts,
            phases,
        );
    }
    let mut phase_targets = subst
        .target_rewrites
        .iter()
        .filter(|target| !target.phases.is_empty())
        .map(|target| {
            let total = target
                .phases
                .iter()
                .map(|phase| phase.duration)
                .sum::<Duration>();
            (target, total)
        })
        .collect::<Vec<_>>();
    phase_targets.sort_by(|(left, left_total), (right, right_total)| {
        right_total
            .cmp(left_total)
            .then_with(|| format_core_path(&left.target).cmp(&format_core_path(&right.target)))
    });
    for (target, total) in phase_targets.into_iter().take(12) {
        let phases = target
            .phases
            .iter()
            .take(4)
            .map(|phase| format!("{}={}", phase.phase, format_duration(phase.duration)))
            .collect::<Vec<_>>()
            .join(", ");
        eprintln!(
            "                rewrite_phase_target {} total={} rewrites={} phases=[{}]",
            format_core_path(&target.target),
            format_duration(total),
            target.rewrites,
            phases,
        );
    }
    let mut expr_kind_targets = subst
        .target_rewrites
        .iter()
        .filter(|target| !target.expr_kinds.is_empty())
        .map(|target| {
            let total = target
                .expr_kinds
                .iter()
                .map(|kind| kind.duration)
                .sum::<Duration>();
            (target, total)
        })
        .collect::<Vec<_>>();
    expr_kind_targets.sort_by(|(left, left_total), (right, right_total)| {
        right_total
            .cmp(left_total)
            .then_with(|| format_core_path(&left.target).cmp(&format_core_path(&right.target)))
    });
    for (target, total) in expr_kind_targets.into_iter().take(12) {
        let kinds = target
            .expr_kinds
            .iter()
            .take(8)
            .map(|kind| {
                format!(
                    "{}={}({})",
                    kind.kind,
                    format_duration(kind.duration),
                    kind.count
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        eprintln!(
            "                rewrite_expr_kind_target {} total={} kinds=[{}]",
            format_core_path(&target.target),
            format_duration(total),
            kinds,
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
    finalize: &InferFinalizeCompactProfile,
    pipeline: &InferPipelineTimings,
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
    eprintln!(
        "    files: {}  (entry={}, std={}, user={})",
        lower.files, lower.entry_files, lower.std_files, lower.user_files
    );
    eprintln!(
        "    entry: parse={} lower_roots={}",
        format_duration(lower.entry.parse),
        format_duration(lower.entry.lower_roots)
    );
    eprintln!(
        "    std: parse={} lower_roots={}",
        format_duration(lower.std.parse),
        format_duration(lower.std.lower_roots)
    );
    eprintln!(
        "    user: parse={} lower_roots={}",
        format_duration(lower.user.parse),
        format_duration(lower.user.lower_roots)
    );
    eprintln!(
        "    std_cache: hits={} misses={} disabled={} clone={} build={}",
        lower.std_cache.hits,
        lower.std_cache.misses,
        lower.std_cache.disabled,
        format_duration(lower.std_cache.clone),
        format_duration(lower.std_cache.build)
    );
    eprintln!(
        "    incremental_cache: candidates={} bundle_hits={} unit_hits={} selected={} writes={}",
        pipeline.incremental_cache_candidates,
        pipeline.incremental_cache_bundle_hits,
        pipeline.incremental_cache_unit_hits,
        pipeline.incremental_cache_selected_units,
        pipeline.incremental_cache_writes
    );
    eprintln!(
        "    compiled_unit_artifacts: manifests={} reads={} writes={}",
        pipeline.std_artifact_manifests, pipeline.std_artifact_reads, pipeline.std_artifact_writes
    );
    eprintln!(
        "      manifest: {}",
        format_duration(pipeline.std_artifact_manifest)
    );
    eprintln!(
        "      read: {}",
        format_duration(pipeline.std_artifact_read)
    );
    eprintln!(
        "      import: {}",
        format_duration(pipeline.std_artifact_import)
    );
    eprintln!(
        "      prepare_finalize: {}",
        format_duration(pipeline.std_artifact_prepare_finalize)
    );
    eprintln!(
        "      build: {}",
        format_duration(pipeline.std_artifact_build)
    );
    eprintln!(
        "      write: {}",
        format_duration(pipeline.std_artifact_write)
    );
    eprintln!("  type_errors: {}", format_duration(pipeline.type_errors));
    eprintln!(
        "  surface_diagnostics: {}",
        format_duration(pipeline.surface_diagnostics)
    );
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
    eprintln!("  render: {}", format_duration(pipeline.render));
    eprintln!(
        "  binding_names: {}",
        format_duration(pipeline.binding_names)
    );
    eprintln!(
        "  quantified_counts: {}",
        format_duration(pipeline.quantified_counts)
    );
    eprintln!("  core_export: {}", format_duration(pipeline.core_export));
    eprintln!(
        "  runtime_dependency_merge: {}",
        format_duration(pipeline.runtime_dependency_merge)
    );
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

struct InferLowerOutput {
    state: InferLowerState,
    diagnostic_source: String,
    lower_profile: InferSourceLowerProfile,
    runtime_dependencies: Option<CompiledRuntimeBundle>,
    pipeline_timings: InferPipelineTimings,
}

#[derive(Default)]
struct InferPipelineTimings {
    enabled: bool,
    std_artifact_manifest: Duration,
    std_artifact_read: Duration,
    std_artifact_import: Duration,
    std_artifact_prepare_finalize: Duration,
    std_artifact_build: Duration,
    std_artifact_write: Duration,
    std_artifact_manifests: usize,
    std_artifact_reads: usize,
    std_artifact_writes: usize,
    incremental_cache_candidates: usize,
    incremental_cache_bundle_hits: usize,
    incremental_cache_unit_hits: usize,
    incremental_cache_selected_units: usize,
    incremental_cache_writes: usize,
    type_errors: Duration,
    surface_diagnostics: Duration,
    render: Duration,
    binding_names: Duration,
    quantified_counts: Duration,
    core_export: Duration,
    runtime_dependency_merge: Duration,
}

impl InferPipelineTimings {
    fn new(enabled: bool) -> Self {
        Self {
            enabled,
            ..Self::default()
        }
    }

    fn start(&self) -> Option<Instant> {
        self.enabled.then(Instant::now)
    }

    fn elapsed(start: Option<Instant>) -> Duration {
        start.map_or(Duration::ZERO, |start| start.elapsed())
    }
}

fn source_set_has_invalid_tokens(source_set: &SourceSet) -> bool {
    source_set.files.iter().any(|file| {
        let green = parse_module_to_green_with_ops(&file.source, file.op_table.clone());
        let root = SyntaxNode::<YulangLanguage>::new_root(green);
        has_invalid_token(&root)
    })
}

fn lower_infer_sources(
    path: Option<&str>,
    _root: &SyntaxNode<YulangLanguage>,
    source: &str,
    options: &CliOptions,
    collected: Option<(&SourceSet, Duration)>,
) -> InferLowerOutput {
    if let Some((source_set, collect)) = collected {
        return lower_infer_source_set_with_cache(source_set, source, collect, options);
    }
    let (source_set, collect) = collect_infer_source_set_or_exit(path, source, options);
    lower_infer_source_set_with_cache(&source_set, source, collect, options)
}

fn collect_infer_source_set_or_exit(
    path: Option<&str>,
    source: &str,
    options: &CliOptions,
) -> (SourceSet, Duration) {
    let collect_start = Instant::now();
    let source_set = match path {
        Some(path) => {
            collect_source_files_with_options(path, source_options(options, path_base_dir(path)))
        }
        None => {
            let base_dir = env::current_dir().ok();
            collect_virtual_source_files_with_options(
                source,
                base_dir.clone(),
                source_options(options, base_dir.as_deref()),
            )
        }
    };
    let source_set = match source_set {
        Ok(source_set) => source_set,
        Err(err) => {
            eprintln!("{err}");
            process::exit(1);
        }
    };
    let collect = collect_start.elapsed();
    (source_set, collect)
}

fn lower_infer_source_set_with_cache(
    source_set: &SourceSet,
    fallback_diagnostic_source: &str,
    collect: Duration,
    options: &CliOptions,
) -> InferLowerOutput {
    let mut pipeline_timings = InferPipelineTimings::new(options.infer_phase_timings);
    let cache = CompiledUnitArtifactCache::from_paths(
        &yulang_sources::YulangCachePaths::for_project(workspace_root()),
    );
    if !options.no_cache
        && let Some(bundle) =
            read_cached_dependency_unit_artifact_bundle(source_set, &cache, &mut pipeline_timings)
    {
        let import_start = pipeline_timings.start();
        let lowered = lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled(
            source_set, &bundle,
        );
        pipeline_timings.std_artifact_import = InferPipelineTimings::elapsed(import_start);
        let mut profile = lowered.lowered.profile;
        profile.collect = collect;
        return infer_lower_output(
            lowered.lowered.lowered,
            fallback_diagnostic_source,
            profile,
            Some(lowered.runtime),
            pipeline_timings,
        );
    }

    let mut lowered = if options.infer_phase_timings {
        lower_source_set_profiled(source_set)
    } else {
        InferProfiledLoweredSources {
            lowered: lower_source_set(source_set),
            profile: InferSourceLowerProfile::default(),
        }
    };
    lowered.profile.collect = collect;
    let prepare_finalize_start = pipeline_timings.start();
    lowered.lowered.state.finalize_compact_results_profiled();
    pipeline_timings.std_artifact_prepare_finalize =
        InferPipelineTimings::elapsed(prepare_finalize_start);
    if !options.no_cache {
        write_dependency_unit_artifact_bundle(
            source_set,
            &lowered.lowered.state,
            &cache,
            &mut pipeline_timings,
        );
    }
    let profile = lowered.profile;
    infer_lower_output(
        lowered.lowered,
        fallback_diagnostic_source,
        profile,
        None,
        pipeline_timings,
    )
}

fn can_use_yuir_source_cache(options: &CliOptions) -> bool {
    options.control_vm
        && !options.no_cache
        && !options.infer
        && !options.infer_phase_timings
        && !options.core_ir
        && !options.runtime_ir
        && !options.hygiene_ir
        && !options.run_interpreter
        && !options.native_compare_i64
        && !options.native_abi_lanes
        && options.native_object.is_none()
        && options.native_exe.is_none()
        && options.native_value_exe.is_none()
        && options.native_run.is_none()
        && options.native_run_exe.is_none()
        && options.native_run_value_exe.is_none()
        && options.native_run_cps_repr_exe.is_none()
        && options.native_run_mmtk_cps_repr_exe.is_none()
}

fn can_write_yuir_source_cache(options: &CliOptions) -> bool {
    can_use_yuir_source_cache(options)
}

fn read_yuir_source_cache(source_set: &SourceSet) -> Option<(runtime::ControlVmModule, Duration)> {
    let path = yuir_source_cache_path(source_set);
    let load_start = Instant::now();
    let module = runtime::ControlVmModule::read_artifact_file(&path).ok()?;
    Some((module, load_start.elapsed()))
}

fn write_yuir_source_cache(source_set: &SourceSet, module: &runtime::ControlVmModule) {
    let path = yuir_source_cache_path(source_set);
    if let Some(parent) = path.parent() {
        if fs::create_dir_all(parent).is_err() {
            return;
        }
    }
    let _ = module.write_artifact_file(&path);
}

fn yuir_source_cache_path(source_set: &SourceSet) -> PathBuf {
    let paths = yulang_sources::YulangCachePaths::for_project(workspace_root());
    paths
        .user_cache_root
        .join("yuir-source")
        .join(format!("v{YUIR_SOURCE_CACHE_VERSION}"))
        .join(format!(
            "yuir{}-{:016x}.yuir",
            runtime::CONTROL_VM_ARTIFACT_VERSION,
            yuir_source_cache_key(source_set)
        ))
}

fn yuir_source_cache_key(source_set: &SourceSet) -> u64 {
    let mut hasher = DefaultHasher::new();
    YUIR_SOURCE_CACHE_VERSION.hash(&mut hasher);
    runtime::CONTROL_VM_ARTIFACT_VERSION.hash(&mut hasher);
    for artifact in source_set.compiled_unit_syntax_artifacts() {
        hash_compiled_unit_manifest(&artifact.manifest, &mut hasher);
    }
    hasher.finish()
}

fn hash_compiled_unit_manifest(
    manifest: &yulang_sources::CompiledUnitManifest,
    hasher: &mut impl Hasher,
) {
    manifest.artifact_format_version.hash(hasher);
    manifest.parser_format_version.hash(hasher);
    manifest.unit_index.hash(hasher);
    source_compilation_unit_origin_key(manifest.origin).hash(hasher);
    for realm in &manifest.realms {
        realm.identity.hash(hasher);
        realm.version.hash(hasher);
    }
    for band in &manifest.bands {
        band.realm.identity.hash(hasher);
        band.realm.version.hash(hasher);
        band.band.segments.hash(hasher);
    }
    manifest.source_hash.hash(hasher);
    manifest.syntax_hash.hash(hasher);
    manifest.interface_hash.hash(hasher);
    for file in &manifest.files {
        file.path.hash(hasher);
        file.module_path.segments.hash(hasher);
        file.origin.hash(hasher);
        file.source_len.hash(hasher);
        file.source_hash.hash(hasher);
    }
    for dependency in &manifest.dependencies {
        dependency.unit_index.hash(hasher);
        dependency.source_hash.hash(hasher);
        dependency.interface_hash.hash(hasher);
    }
}

fn source_compilation_unit_origin_key(origin: SourceCompilationUnitOrigin) -> u8 {
    match origin {
        SourceCompilationUnitOrigin::Entry => 0,
        SourceCompilationUnitOrigin::Std => 1,
        SourceCompilationUnitOrigin::User => 2,
        SourceCompilationUnitOrigin::Mixed => 3,
    }
}

fn infer_lower_output(
    lowered: yulang_infer::LoweredSources,
    fallback_diagnostic_source: &str,
    lower_profile: InferSourceLowerProfile,
    runtime_dependencies: Option<CompiledRuntimeBundle>,
    pipeline_timings: InferPipelineTimings,
) -> InferLowerOutput {
    InferLowerOutput {
        state: lowered.state,
        diagnostic_source: if lowered.diagnostic_source.is_empty() {
            fallback_diagnostic_source.to_string()
        } else {
            lowered.diagnostic_source
        },
        lower_profile,
        runtime_dependencies,
        pipeline_timings,
    }
}

fn read_cached_dependency_unit_artifact_bundle(
    source_set: &SourceSet,
    cache: &CompiledUnitArtifactCache,
    timings: &mut InferPipelineTimings,
) -> Option<CompiledUnitArtifactBundle> {
    let manifest_start = timings.start();
    let manifests = cacheable_dependency_manifests(source_set);
    timings.std_artifact_manifest += InferPipelineTimings::elapsed(manifest_start);
    if timings.enabled {
        timings.std_artifact_manifests = manifests.len();
        timings.incremental_cache_candidates = manifests.len();
    }
    if manifests.is_empty() {
        return None;
    }

    let read_start = timings.start();
    if let Ok(bundle) = cache.read_bundle_for_manifests(&manifests) {
        timings.std_artifact_read += InferPipelineTimings::elapsed(read_start);
        if timings.enabled {
            timings.std_artifact_reads += 1;
            timings.incremental_cache_bundle_hits += 1;
            timings.incremental_cache_selected_units = bundle.manifests.len();
        }
        return Some(bundle);
    }
    timings.std_artifact_read += InferPipelineTimings::elapsed(read_start);

    let mut artifacts_by_unit = BTreeMap::new();
    for manifest in &manifests {
        let read_start = timings.start();
        if let Ok(artifact) = cache.read_for_manifest(manifest) {
            artifacts_by_unit.insert(manifest.unit_index, artifact);
            if timings.enabled {
                timings.incremental_cache_unit_hits += 1;
            }
        }
        timings.std_artifact_read += InferPipelineTimings::elapsed(read_start);
        if timings.enabled {
            timings.std_artifact_reads += 1;
        }
    }
    let selected_units = dependency_closed_cached_units(&manifests, artifacts_by_unit.keys());
    if selected_units.is_empty() {
        return None;
    }
    if timings.enabled {
        timings.incremental_cache_selected_units = selected_units.len();
    }
    let artifacts = artifacts_by_unit
        .into_iter()
        .filter_map(|(unit_idx, artifact)| selected_units.contains(&unit_idx).then_some(artifact))
        .collect::<Vec<_>>();
    let build_start = timings.start();
    let bundle = build_compiled_unit_artifact_bundle(&artifacts).ok()?;
    timings.std_artifact_build += InferPipelineTimings::elapsed(build_start);
    let write_start = timings.start();
    let _ = cache.write_bundle(&bundle);
    timings.std_artifact_write += InferPipelineTimings::elapsed(write_start);
    if timings.enabled {
        timings.std_artifact_writes += 1;
        timings.incremental_cache_writes += 1;
    }
    Some(bundle)
}

fn write_dependency_unit_artifact_bundle(
    source_set: &SourceSet,
    state: &InferLowerState,
    cache: &CompiledUnitArtifactCache,
    timings: &mut InferPipelineTimings,
) {
    let build_start = timings.start();
    let artifacts = build_compiled_unit_artifacts(source_set, state)
        .into_iter()
        .filter(|artifact| is_cacheable_dependency_manifest(&artifact.manifest))
        .collect::<Vec<_>>();
    let bundle = if artifacts.is_empty() {
        None
    } else {
        build_compiled_unit_artifact_bundle(&artifacts).ok()
    };
    timings.std_artifact_build += InferPipelineTimings::elapsed(build_start);
    for artifact in &artifacts {
        let write_start = timings.start();
        let _ = cache.write(artifact);
        timings.std_artifact_write += InferPipelineTimings::elapsed(write_start);
        if timings.enabled {
            timings.std_artifact_writes += 1;
            timings.incremental_cache_writes += 1;
        }
    }
    if let Some(bundle) = bundle {
        let write_start = timings.start();
        let _ = cache.write_bundle(&bundle);
        timings.std_artifact_write += InferPipelineTimings::elapsed(write_start);
        if timings.enabled {
            timings.std_artifact_writes += 1;
            timings.incremental_cache_writes += 1;
        }
    }
}

fn cacheable_dependency_manifests(
    source_set: &SourceSet,
) -> Vec<yulang_sources::CompiledUnitManifest> {
    source_set
        .compiled_unit_syntax_artifacts()
        .into_iter()
        .map(|artifact| artifact.manifest)
        .filter(is_cacheable_dependency_manifest)
        .collect()
}

fn is_cacheable_dependency_manifest(manifest: &yulang_sources::CompiledUnitManifest) -> bool {
    manifest.origin != SourceCompilationUnitOrigin::Entry
        && manifest
            .files
            .iter()
            .all(|file| file.origin != yulang_sources::SourceOrigin::Entry)
}

fn dependency_closed_cached_units<'a>(
    manifests: &'a [yulang_sources::CompiledUnitManifest],
    cached_units: impl Iterator<Item = &'a usize>,
) -> BTreeSet<usize> {
    let manifests_by_unit = manifests
        .iter()
        .map(|manifest| (manifest.unit_index, manifest))
        .collect::<BTreeMap<_, _>>();
    let mut selected = cached_units.copied().collect::<BTreeSet<_>>();
    loop {
        let before = selected.len();
        let previous = selected.clone();
        selected.retain(|unit_idx| {
            let Some(manifest) = manifests_by_unit.get(unit_idx) else {
                return false;
            };
            manifest
                .dependencies
                .iter()
                .all(|dependency| previous.contains(&dependency.unit_index))
        });
        if selected.len() == before {
            return selected;
        }
    }
}

fn merge_runtime_dependencies_or_exit(
    program: typed_ir::CoreProgram,
    dependencies: Option<&CompiledRuntimeBundle>,
) -> typed_ir::CoreProgram {
    let Some(dependencies) = dependencies else {
        return program;
    };
    match dependencies.merge_with_user_program(program) {
        Ok(program) => program,
        Err(err) => {
            eprintln!("failed to merge cached runtime dependencies: {err:?}");
            process::exit(1);
        }
    }
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
    if let Some(source_range) = evidence.source_range {
        parts.push(format!(
            "source-range={}",
            format_source_range(source_range)
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
    if let Some(source_range) = evidence.source_range {
        parts.push(format!(
            "source-range={}",
            format_source_range(source_range)
        ));
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

fn print_infer_program(program: &typed_ir::CoreProgram, verbose: bool) {
    print_core_ir_module(&program.program);
    print_infer_graph(&program.graph, verbose);
    print_core_principal_evidence(&program.evidence, verbose);
}

fn print_core_ir_module(module: &typed_ir::PrincipalModule) {
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

fn print_infer_graph(graph: &typed_ir::CoreGraphView, verbose: bool) {
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

fn print_core_principal_evidence(evidence: &typed_ir::PrincipalEvidence, verbose: bool) {
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

fn format_core_expected_edge_evidence(evidence: &typed_ir::ExpectedEdgeEvidence) -> String {
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
    if let Some(source_range) = evidence.source_range {
        parts.push(format!(
            "source-range={}",
            format_source_range(source_range)
        ));
    }
    parts.push(format!("closed={}", evidence.closed));
    parts.push(format!("informative={}", evidence.informative));
    parts.push(format!("runtime-usable={}", evidence.runtime_usable));
    parts.join(" ")
}

fn format_source_range(range: typed_ir::SourceRange) -> String {
    format!("{}..{}", range.start, range.end)
}

fn format_core_expected_adapter_edge_evidence(
    evidence: &typed_ir::ExpectedAdapterEdgeEvidence,
) -> String {
    let mut parts = vec![format!(
        "#{} {}",
        evidence.id,
        format_core_expected_adapter_edge_kind(evidence.kind)
    )];
    if let Some(source_expected_edge) = evidence.source_expected_edge {
        parts.push(format!("source-expected-edge=#{source_expected_edge}"));
    }
    if let Some(source_range) = evidence.source_range {
        parts.push(format!(
            "source-range={}",
            format_source_range(source_range)
        ));
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
    evidence: &typed_ir::DerivedExpectedEdgeEvidence,
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

fn format_core_expected_edge_kind(kind: typed_ir::ExpectedEdgeKind) -> &'static str {
    match kind {
        typed_ir::ExpectedEdgeKind::IfCondition => "if-condition",
        typed_ir::ExpectedEdgeKind::IfBranch => "if-branch",
        typed_ir::ExpectedEdgeKind::MatchGuard => "match-guard",
        typed_ir::ExpectedEdgeKind::MatchBranch => "match-branch",
        typed_ir::ExpectedEdgeKind::CatchGuard => "catch-guard",
        typed_ir::ExpectedEdgeKind::CatchBranch => "catch-branch",
        typed_ir::ExpectedEdgeKind::ApplicationCallee => "application-callee",
        typed_ir::ExpectedEdgeKind::ApplicationArgument => "application-argument",
        typed_ir::ExpectedEdgeKind::Annotation => "annotation",
        typed_ir::ExpectedEdgeKind::RecordField => "record-field",
        typed_ir::ExpectedEdgeKind::VariantPayload => "variant-payload",
        typed_ir::ExpectedEdgeKind::AssignmentValue => "assignment-value",
        typed_ir::ExpectedEdgeKind::RepresentationCoerce => "representation-coerce",
    }
}

fn format_core_edge_polarity(polarity: typed_ir::EdgePolarity) -> &'static str {
    match polarity {
        typed_ir::EdgePolarity::Covariant => "covariant",
        typed_ir::EdgePolarity::Contravariant => "contravariant",
        typed_ir::EdgePolarity::Invariant => "invariant",
    }
}

fn format_core_derived_expected_edge_kind(kind: typed_ir::DerivedExpectedEdgeKind) -> &'static str {
    match kind {
        typed_ir::DerivedExpectedEdgeKind::RecordField => "record-field",
        typed_ir::DerivedExpectedEdgeKind::TupleItem => "tuple-item",
        typed_ir::DerivedExpectedEdgeKind::VariantPayload => "variant-payload",
        typed_ir::DerivedExpectedEdgeKind::FunctionParam => "function-param",
        typed_ir::DerivedExpectedEdgeKind::FunctionReturn => "function-return",
    }
}

fn format_core_edge_path(path: &[typed_ir::EdgePathSegment]) -> String {
    path.iter()
        .map(|segment| match segment {
            typed_ir::EdgePathSegment::Field(name) => format!(".{}", name.0),
            typed_ir::EdgePathSegment::TupleIndex(index) => format!("[{index}]"),
            typed_ir::EdgePathSegment::VariantCase(name) => format!(":{}", name.0),
            typed_ir::EdgePathSegment::PayloadIndex(index) => format!("({index})"),
            typed_ir::EdgePathSegment::FunctionParam => ".param".to_string(),
            typed_ir::EdgePathSegment::FunctionReturn => ".return".to_string(),
        })
        .collect::<Vec<_>>()
        .join("")
}

fn format_core_expected_adapter_edge_kind(kind: typed_ir::ExpectedAdapterEdgeKind) -> &'static str {
    match kind {
        typed_ir::ExpectedAdapterEdgeKind::EffectOperationArgument => "effect-operation-argument",
        typed_ir::ExpectedAdapterEdgeKind::ValueToThunk => "value-to-thunk",
        typed_ir::ExpectedAdapterEdgeKind::ThunkToValue => "thunk-to-value",
        typed_ir::ExpectedAdapterEdgeKind::BindHere => "bind-here",
        typed_ir::ExpectedAdapterEdgeKind::HandlerResidual => "handler-residual",
        typed_ir::ExpectedAdapterEdgeKind::HandlerReturn => "handler-return",
        typed_ir::ExpectedAdapterEdgeKind::ResumeArgument => "resume-argument",
    }
}

fn format_runtime_symbol_kind(kind: typed_ir::RuntimeSymbolKind) -> &'static str {
    match kind {
        typed_ir::RuntimeSymbolKind::Value => "value",
        typed_ir::RuntimeSymbolKind::RoleMethod => "role-method",
        typed_ir::RuntimeSymbolKind::EffectOperation => "effect-op",
    }
}

fn print_core_ir_binding(binding: &typed_ir::PrincipalBinding) {
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
        runtime::VmValue::Bytes(value) => format!("<bytes len={}>", value.len()),
        runtime::VmValue::Path(value) => format!("{:?}", value.display().to_string()),
        runtime::VmValue::Bool(value) => value.to_string(),
        runtime::VmValue::Unit => "()".to_string(),
        runtime::VmValue::List(items) => format!(
            "[{}]",
            items
                .to_vec()
                .iter()
                .map(|value| format_runtime_vm_value(value))
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

fn format_primitive_op(op: typed_ir::PrimitiveOp) -> &'static str {
    match op {
        typed_ir::PrimitiveOp::YadaYada => "...",
        typed_ir::PrimitiveOp::BoolNot => "std::bool::not",
        typed_ir::PrimitiveOp::BoolEq => "std::bool::eq",
        typed_ir::PrimitiveOp::ListEmpty => "std::list::empty",
        typed_ir::PrimitiveOp::ListSingleton => "std::list::singleton",
        typed_ir::PrimitiveOp::ListLen => "std::list::len",
        typed_ir::PrimitiveOp::ListMerge => "std::list::merge",
        typed_ir::PrimitiveOp::ListIndex => "std::list::index_raw",
        typed_ir::PrimitiveOp::ListIndexRange => "std::list::index_range",
        typed_ir::PrimitiveOp::ListSplice => "std::list::splice",
        typed_ir::PrimitiveOp::ListIndexRangeRaw => "std::list::index_range_raw",
        typed_ir::PrimitiveOp::ListSpliceRaw => "std::list::splice_raw",
        typed_ir::PrimitiveOp::ListViewRaw => "std::list::view_raw",
        typed_ir::PrimitiveOp::StringLen => "std::str::len",
        typed_ir::PrimitiveOp::StringIndex => "std::str::index_raw",
        typed_ir::PrimitiveOp::StringIndexRange => "std::str::index_range",
        typed_ir::PrimitiveOp::StringSplice => "std::str::splice",
        typed_ir::PrimitiveOp::StringIndexRangeRaw => "std::str::index_range_raw",
        typed_ir::PrimitiveOp::StringSpliceRaw => "std::str::splice_raw",
        typed_ir::PrimitiveOp::IntAdd => "std::int::add",
        typed_ir::PrimitiveOp::IntSub => "std::int::sub",
        typed_ir::PrimitiveOp::IntMul => "std::int::mul",
        typed_ir::PrimitiveOp::IntDiv => "std::int::div",
        typed_ir::PrimitiveOp::IntMod => "std::int::mod",
        typed_ir::PrimitiveOp::IntEq => "std::int::eq",
        typed_ir::PrimitiveOp::IntLt => "std::int::lt",
        typed_ir::PrimitiveOp::IntLe => "std::int::le",
        typed_ir::PrimitiveOp::IntGt => "std::int::gt",
        typed_ir::PrimitiveOp::IntGe => "std::int::ge",
        typed_ir::PrimitiveOp::FloatAdd => "std::float::add",
        typed_ir::PrimitiveOp::FloatSub => "std::float::sub",
        typed_ir::PrimitiveOp::FloatMul => "std::float::mul",
        typed_ir::PrimitiveOp::FloatDiv => "std::float::div",
        typed_ir::PrimitiveOp::FloatEq => "std::float::eq",
        typed_ir::PrimitiveOp::FloatLt => "std::float::lt",
        typed_ir::PrimitiveOp::FloatLe => "std::float::le",
        typed_ir::PrimitiveOp::FloatGt => "std::float::gt",
        typed_ir::PrimitiveOp::FloatGe => "std::float::ge",
        typed_ir::PrimitiveOp::StringEq => "std::str::eq",
        typed_ir::PrimitiveOp::StringConcat => "std::str::concat",
        typed_ir::PrimitiveOp::StringToBytes => "std::str::to_bytes",
        typed_ir::PrimitiveOp::CharEq => "std::char::eq",
        typed_ir::PrimitiveOp::CharToString => "std::char::to_string",
        typed_ir::PrimitiveOp::CharIsWhitespace => "std::char::is_whitespace",
        typed_ir::PrimitiveOp::CharIsPunctuation => "std::char::is_punctuation",
        typed_ir::PrimitiveOp::CharIsWord => "std::char::is_word",
        typed_ir::PrimitiveOp::BytesLen => "std::bytes::len",
        typed_ir::PrimitiveOp::BytesEq => "std::bytes::eq",
        typed_ir::PrimitiveOp::BytesConcat => "std::bytes::concat",
        typed_ir::PrimitiveOp::BytesIndex => "std::bytes::index_raw",
        typed_ir::PrimitiveOp::BytesIndexRange => "std::bytes::index_range",
        typed_ir::PrimitiveOp::BytesToUtf8Raw => "std::bytes::to_utf8_raw",
        typed_ir::PrimitiveOp::BytesToPath => "std::path::of_bytes_raw",
        typed_ir::PrimitiveOp::PathToBytes => "std::path::to_bytes",
        typed_ir::PrimitiveOp::IntToString => "std::int::to_string",
        typed_ir::PrimitiveOp::IntToHex => "std::int::to_hex",
        typed_ir::PrimitiveOp::IntToUpperHex => "std::int::to_upper_hex",
        typed_ir::PrimitiveOp::FloatToString => "std::float::to_string",
        typed_ir::PrimitiveOp::BoolToString => "std::bool::to_string",
    }
}

fn format_core_scheme(scheme: &typed_ir::Scheme) -> String {
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

fn format_core_requirement(requirement: &typed_ir::RoleRequirement) -> String {
    let args = requirement
        .args
        .iter()
        .map(format_core_requirement_arg)
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}<{args}>", format_core_path(&requirement.role))
}

fn format_core_requirement_arg(arg: &typed_ir::RoleRequirementArg) -> String {
    match arg {
        typed_ir::RoleRequirementArg::Input(bounds) => format_core_bounds(bounds),
        typed_ir::RoleRequirementArg::Associated { name, bounds } => {
            format!("{} = {}", name.0, format_core_bounds(bounds))
        }
    }
}

fn format_core_bounds(bounds: &typed_ir::TypeBounds) -> String {
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

fn bounds_exact_type(bounds: &typed_ir::TypeBounds) -> Option<&typed_ir::Type> {
    match (&bounds.lower, &bounds.upper) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower),
        _ => None,
    }
}

fn format_graph_owner(owner: &typed_ir::GraphOwner) -> String {
    match owner {
        typed_ir::GraphOwner::RootExpr(index) => format!("root[{index}]"),
    }
}

fn format_core_type(ty: &typed_ir::Type) -> String {
    match ty {
        typed_ir::Type::Unknown => "?".to_string(),
        typed_ir::Type::Never => "⊥".to_string(),
        typed_ir::Type::Any => "⊤".to_string(),
        typed_ir::Type::Var(var) => var.0.clone(),
        typed_ir::Type::Named { path, args } => {
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
        typed_ir::Type::Fun {
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
        typed_ir::Type::Tuple(items) => {
            let items = items
                .iter()
                .map(format_core_type)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        typed_ir::Type::Record(record) => format_core_record_type(record),
        typed_ir::Type::Variant(variant) => format_core_variant_type(variant),
        typed_ir::Type::Row { items, tail } => format_core_row_type(items, tail),
        typed_ir::Type::Union(items) => items
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
        typed_ir::Type::Inter(items) => items
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
        typed_ir::Type::Recursive { var, body } => {
            format!("rec {}. {}", var.0, format_core_type(body))
        }
    }
}

fn format_core_type_arg(arg: &typed_ir::TypeArg) -> String {
    match arg {
        typed_ir::TypeArg::Type(ty) => format_core_type(ty),
        typed_ir::TypeArg::Bounds(bounds) => format_core_bounds(bounds),
    }
}

fn format_core_record_type(record: &typed_ir::RecordType) -> String {
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

fn format_core_record_spread_type(spread: &typed_ir::RecordSpread) -> String {
    match spread {
        typed_ir::RecordSpread::Head(ty) => format!("..{}", format_core_type(ty)),
        typed_ir::RecordSpread::Tail(ty) => format!("{}..", format_core_type(ty)),
    }
}

fn format_core_variant_type(variant: &typed_ir::VariantType) -> String {
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
    format!(":{{{}}}", items.join(" | "))
}

fn format_core_row_type(items: &[typed_ir::Type], tail: &typed_ir::Type) -> String {
    let mut parts = Vec::new();
    flatten_core_row_parts(items, tail, &mut parts);
    match parts.as_slice() {
        [] => "[]".to_string(),
        [single] => single.clone(),
        _ => format!("[{}]", parts.join("; ")),
    }
}

fn flatten_core_row_parts(
    items: &[typed_ir::Type],
    tail: &typed_ir::Type,
    parts: &mut Vec<String>,
) {
    parts.extend(items.iter().map(format_core_type));
    match tail {
        typed_ir::Type::Never => {}
        typed_ir::Type::Row { items, tail } => flatten_core_row_parts(items, tail, parts),
        other => parts.push(format_core_type(other)),
    }
}

fn format_core_fun_side(ty: &typed_ir::Type) -> String {
    match ty {
        typed_ir::Type::Fun { .. } => format!("({})", format_core_type(ty)),
        _ => format_core_type(ty),
    }
}

fn format_core_expr(expr: &typed_ir::Expr) -> String {
    match expr {
        typed_ir::Expr::Var(path) => format_core_path(path),
        typed_ir::Expr::PrimitiveOp(op) => format!("<primitive {}>", format_primitive_op(*op)),
        typed_ir::Expr::Lit(lit) => format_core_lit(lit),
        typed_ir::Expr::Lambda { param, body, .. } => {
            format!("fun {} -> {}", param.0, format_core_expr(body))
        }
        typed_ir::Expr::Apply {
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
        typed_ir::Expr::If {
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
        typed_ir::Expr::Tuple(items) => {
            let items = items
                .iter()
                .map(format_core_expr)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        typed_ir::Expr::Record { fields, spread } => {
            let mut items = fields
                .iter()
                .map(|field| format!("{}: {}", field.name.0, format_core_expr(&field.value)))
                .collect::<Vec<_>>();
            if let Some(spread) = spread {
                items.push(format_core_record_spread_expr(spread));
            }
            format!("{{{}}}", items.join(", "))
        }
        typed_ir::Expr::Variant { tag, value, .. } => match value {
            Some(value) => format!(":{} {}", tag.0, format_core_expr_atom(value)),
            None => format!(":{}", tag.0),
        },
        typed_ir::Expr::Select { base, field } => {
            format!("{}.{}", format_core_expr_atom(base), field.0)
        }
        typed_ir::Expr::Match {
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
        typed_ir::Expr::Block { stmts, tail } => {
            let mut parts = stmts.iter().map(format_core_stmt).collect::<Vec<_>>();
            if let Some(tail) = tail {
                parts.push(format_core_expr(tail));
            }
            format!("do {{ {} }}", parts.join("; "))
        }
        typed_ir::Expr::BindHere { expr } => {
            format!("bind_here {}", format_core_expr_atom(expr))
        }
        typed_ir::Expr::Handle {
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
        typed_ir::Expr::Coerce { expr, evidence } => {
            let mut text = format!("coerce {}", format_core_expr_atom(expr));
            if let Some(evidence) = evidence {
                text.push_str(&format!(" :: {}", format_coerce_evidence(evidence)));
            }
            text
        }
        typed_ir::Expr::Pack { var, expr } => {
            format!("pack {} in {}", var.0, format_core_expr(expr))
        }
    }
}

fn format_core_expr_atom(expr: &typed_ir::Expr) -> String {
    match expr {
        typed_ir::Expr::Var(_)
        | typed_ir::Expr::Lit(_)
        | typed_ir::Expr::Select { .. }
        | typed_ir::Expr::Record { .. }
        | typed_ir::Expr::Variant { .. }
        | typed_ir::Expr::BindHere { .. } => format_core_expr(expr),
        _ => format!("({})", format_core_expr(expr)),
    }
}

fn format_core_record_spread_expr(spread: &typed_ir::RecordSpreadExpr) -> String {
    match spread {
        typed_ir::RecordSpreadExpr::Head(expr) => format!("..{}", format_core_expr(expr)),
        typed_ir::RecordSpreadExpr::Tail(expr) => format!("{}..", format_core_expr(expr)),
    }
}

fn format_core_match_arm(arm: &typed_ir::MatchArm) -> String {
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

fn format_core_handle_arm(arm: &typed_ir::HandleArm) -> String {
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

fn format_core_stmt(stmt: &typed_ir::Stmt) -> String {
    match stmt {
        typed_ir::Stmt::Let { pattern, value } => {
            format!(
                "let {} = {}",
                format_core_pattern(pattern),
                format_core_expr(value)
            )
        }
        typed_ir::Stmt::Expr(expr) => format_core_expr(expr),
        typed_ir::Stmt::Module { def, body } => {
            format!(
                "module {} = {}",
                format_core_path(def),
                format_core_expr(body)
            )
        }
    }
}

fn format_core_pattern(pattern: &typed_ir::Pattern) -> String {
    match pattern {
        typed_ir::Pattern::Wildcard => "_".to_string(),
        typed_ir::Pattern::Bind(name) => name.0.clone(),
        typed_ir::Pattern::Lit(lit) => format_core_lit(lit),
        typed_ir::Pattern::Tuple(items) => {
            let items = items
                .iter()
                .map(format_core_pattern)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        typed_ir::Pattern::List {
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
        typed_ir::Pattern::Record { fields, spread } => {
            let mut items = fields
                .iter()
                .map(|field| match &field.default {
                    Some(default) if matches!(&field.pattern, typed_ir::Pattern::Bind(name) if name == &field.name) => {
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
        typed_ir::Pattern::Variant { tag, value } => match value {
            Some(value) => format!(":{} {}", tag.0, format_core_pattern(value)),
            None => format!(":{}", tag.0),
        },
        typed_ir::Pattern::Or { left, right } => {
            format!(
                "{} | {}",
                format_core_pattern(left),
                format_core_pattern(right)
            )
        }
        typed_ir::Pattern::As { pattern, name } => {
            format!("{} as {}", format_core_pattern(pattern), name.0)
        }
    }
}

fn format_core_record_spread_pattern(spread: &typed_ir::RecordSpreadPattern) -> String {
    match spread {
        typed_ir::RecordSpreadPattern::Head(pattern) => {
            format!("..{}", format_core_pattern(pattern))
        }
        typed_ir::RecordSpreadPattern::Tail(pattern) => {
            format!("{}..", format_core_pattern(pattern))
        }
    }
}

fn format_core_lit(lit: &typed_ir::Lit) -> String {
    match lit {
        typed_ir::Lit::Int(value) => value.clone(),
        typed_ir::Lit::Float(value) => value.clone(),
        typed_ir::Lit::String(value) => format!("{value:?}"),
        typed_ir::Lit::Bool(value) => value.to_string(),
        typed_ir::Lit::Unit => "()".to_string(),
    }
}

fn format_apply_evidence(evidence: &typed_ir::ApplyEvidence) -> String {
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
    candidate: &typed_ir::PrincipalSubstitutionCandidate,
) -> String {
    let relation = match candidate.relation {
        typed_ir::PrincipalCandidateRelation::Lower => "<=",
        typed_ir::PrincipalCandidateRelation::Upper => ">=",
        typed_ir::PrincipalCandidateRelation::Exact => "=",
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

fn format_principal_slot_path_segment(segment: &typed_ir::PrincipalSlotPathSegment) -> String {
    match segment {
        typed_ir::PrincipalSlotPathSegment::Callee => "callee".to_string(),
        typed_ir::PrincipalSlotPathSegment::Arg => "arg".to_string(),
        typed_ir::PrincipalSlotPathSegment::Result => "result".to_string(),
        typed_ir::PrincipalSlotPathSegment::Field(name) => format!("field({})", name.0),
        typed_ir::PrincipalSlotPathSegment::TupleIndex(index) => format!("tuple({index})"),
        typed_ir::PrincipalSlotPathSegment::VariantCase(name) => format!("case({})", name.0),
        typed_ir::PrincipalSlotPathSegment::PayloadIndex(index) => format!("payload({index})"),
        typed_ir::PrincipalSlotPathSegment::FunctionParam => "param".to_string(),
        typed_ir::PrincipalSlotPathSegment::FunctionReturn => "return".to_string(),
    }
}

fn format_join_evidence(evidence: &typed_ir::JoinEvidence) -> String {
    format!("join[{}]", format_core_bounds(&evidence.result))
}

fn format_coerce_evidence(evidence: &typed_ir::CoerceEvidence) -> String {
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
        runtime::Type::Unknown => "_".to_string(),
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

fn format_runtime_core_type(ty: &typed_ir::Type) -> String {
    format_runtime_core_type_inner(ty, false)
}

fn format_runtime_core_type_inner(ty: &typed_ir::Type, nested_fun_as_thunk: bool) -> String {
    match ty {
        typed_ir::Type::Named { path, args } => {
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
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } if nested_fun_as_thunk => {
            let param = format_runtime_effected_core_value(param, param_effect, false);
            let ret = format_runtime_effected_core_value(ret, ret_effect, true);
            format!("{param} -> {ret}")
        }
        typed_ir::Type::Fun {
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
        typed_ir::Type::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| format_runtime_core_type_inner(item, true))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        typed_ir::Type::Record(record) => format_core_record_type(record),
        typed_ir::Type::Variant(variant) => format_core_variant_type(variant),
        typed_ir::Type::Union(items) => items
            .iter()
            .map(format_runtime_core_type)
            .collect::<Vec<_>>()
            .join(" | "),
        typed_ir::Type::Inter(items) => items
            .iter()
            .map(format_runtime_core_type)
            .collect::<Vec<_>>()
            .join(" & "),
        other => format_core_type(other),
    }
}

fn format_runtime_core_type_arg(arg: &typed_ir::TypeArg) -> String {
    match arg {
        typed_ir::TypeArg::Type(ty) => format_runtime_core_type_inner(ty, true),
        typed_ir::TypeArg::Bounds(bounds) => format_core_bounds(bounds),
    }
}

fn format_runtime_effected_core_value(
    value: &typed_ir::Type,
    effect: &typed_ir::Type,
    force_thunk: bool,
) -> String {
    let value = format_runtime_core_type_inner(value, true);
    if force_thunk || !is_empty_effect(effect) {
        format!("Thunk[{}, {}]", format_core_type(effect), value)
    } else {
        value
    }
}

fn format_runtime_core_fun_side(ty: &typed_ir::Type) -> String {
    match ty {
        typed_ir::Type::Fun { .. } => format!("({})", format_runtime_core_type(ty)),
        _ => format_runtime_core_type(ty),
    }
}

fn format_runtime_type_atom(ty: &runtime::Type) -> String {
    match ty {
        runtime::Type::Core(typed_ir::Type::Fun { .. })
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
        runtime::ExprKind::AddId {
            id, allowed, thunk, ..
        } => {
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

fn format_core_path(path: &typed_ir::Path) -> String {
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

fn is_top_type(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Any)
}

fn is_implicit_fun_effect(param_effect: &typed_ir::Type, ret_effect: &typed_ir::Type) -> bool {
    is_top_type(param_effect) && (is_top_type(ret_effect) || is_pure_row(ret_effect))
}

fn is_empty_effect(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Never) || is_pure_row(ty)
}

fn is_pure_row(ty: &typed_ir::Type) -> bool {
    matches!(
        ty,
        typed_ir::Type::Row { items, tail }
            if items.is_empty() && matches!(tail.as_ref(), typed_ir::Type::Never)
    )
}

fn is_std_prelude_path(path: &typed_ir::Path) -> bool {
    matches!(
        path.segments.as_slice(),
        [typed_ir::Name(std), typed_ir::Name(prelude), ..] if std == "std" && prelude == "prelude"
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
        InferTypeErrorKind::UnknownRecordField { name } => {
            format!("unknown record field `{name}`")
        }
        InferTypeErrorKind::ExpectedShape { expected } => match expected {
            InferExpectedShape::Function => "expected function".to_string(),
            InferExpectedShape::Tuple => "expected tuple".to_string(),
            InferExpectedShape::Record => "expected record".to_string(),
            InferExpectedShape::Constructor => "expected constructor".to_string(),
        },
        InferTypeErrorKind::MissingImpl { role, args } => {
            if role.ends_with("Cast") && args.len() >= 2 {
                return format!("no implicit cast from {} to {}", args[0], args[1]);
            }
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
            if role.ends_with("Cast") && args.len() >= 2 {
                return format!(
                    "ambiguous implicit cast from {} to {} ({} candidates)",
                    args[0], args[1], candidates
                );
            }
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

fn runtime_error_source_frame(
    error: &runtime::RuntimeError,
    program: &typed_ir::CoreProgram,
    source: &str,
) -> Option<String> {
    let range = runtime_error_source_range(error, &program.evidence)?;
    source_frame(source, range)
}

fn runtime_error_source_range(
    error: &runtime::RuntimeError,
    evidence: &typed_ir::PrincipalEvidence,
) -> Option<typed_ir::SourceRange> {
    let runtime::RuntimeError::TypeMismatch {
        context: Some(context),
        ..
    } = error
    else {
        return None;
    };
    let first_edge = match context.phase {
        runtime::diagnostic::TypeMismatchPhase::ApplyCallee => context.callee_source_edge,
        runtime::diagnostic::TypeMismatchPhase::ApplyArgument => context.arg_source_edge,
        runtime::diagnostic::TypeMismatchPhase::ApplyResult => {
            context.arg_source_edge.or(context.callee_source_edge)
        }
        runtime::diagnostic::TypeMismatchPhase::Expected => {
            context.arg_source_edge.or(context.callee_source_edge)
        }
    };
    let edge = first_edge.and_then(|id| evidence.expected_edge(id))?;
    edge.source_range
}

fn source_frame(source: &str, range: typed_ir::SourceRange) -> Option<String> {
    let start = usize::try_from(range.start).ok()?.min(source.len());
    let end = usize::try_from(range.end)
        .ok()?
        .min(source.len())
        .max(start);
    let (line, col) = line_col(source, start);
    let line_start = source[..start].rfind('\n').map_or(0, |idx| idx + 1);
    let line_end = source[start..]
        .find('\n')
        .map_or(source.len(), |idx| start + idx);
    let line_text = &source[line_start..line_end];
    let caret_start = source[line_start..start].chars().count();
    let caret_end = source[start..end.min(line_end)].chars().count();
    let caret_len = caret_end.max(1);
    Some(format!(
        "  at {line}:{col}\n{line:>4} | {line_text}\n     | {}{}\n",
        " ".repeat(caret_start),
        "^".repeat(caret_len)
    ))
}

fn source_options(options: &CliOptions, base_dir: Option<&Path>) -> SourceOptions {
    let std_root = options
        .std_root
        .as_ref()
        .map(PathBuf::from)
        .filter(|_| !options.no_prelude)
        .and_then(|explicit| {
            resolve_or_install_std_root(Some(explicit), base_dir)
                .ok()
                .flatten()
        })
        .or_else(|| {
            (!options.no_prelude)
                .then(|| resolve_or_install_std_root(None, base_dir).ok().flatten())
                .flatten()
        });
    SourceOptions {
        implicit_prelude: !options.no_prelude && std_root.is_some(),
        std_root,
        search_paths: source_search_paths(base_dir),
    }
}

fn source_search_paths(base_dir: Option<&Path>) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let Some(base_dir) = base_dir else {
        return paths;
    };
    push_unique_search_path(&mut paths, base_dir.to_path_buf());
    if let Some(parent) = base_dir.parent() {
        push_unique_search_path(&mut paths, parent.to_path_buf());
    }
    paths
}

fn push_unique_search_path(paths: &mut Vec<PathBuf>, path: PathBuf) {
    if !paths.iter().any(|existing| existing == &path) {
        paths.push(path);
    }
}

fn path_base_dir(path: &str) -> Option<&Path> {
    Path::new(path).parent()
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_infer::{Name as InferName, RecordField as InferRecordField};
    use yulang_sources::{InlineSource, SourceOrigin};

    fn test_cli_options() -> CliOptions {
        CliOptions {
            show_cst: false,
            parse_mode: None,
            infer: true,
            core_ir: false,
            runtime_ir: false,
            hygiene_ir: false,
            run_interpreter: false,
            control_vm: false,
            control_vm_emit: None,
            control_vm_load: None,
            native_compare_i64: false,
            native_abi_lanes: false,
            native_object: None,
            native_exe: None,
            native_value_exe: None,
            native_run: None,
            native_run_exe: None,
            native_run_value_exe: None,
            native_run_cps_repr_exe: None,
            native_run_mmtk_cps_repr_exe: None,
            print_roots: false,
            verbose_ir: false,
            infer_phase_timings: false,
            runtime_phase_timings: false,
            path: None,
            no_prelude: true,
            no_cache: false,
            std_root: None,
            profile_flamegraph: None,
            profile_repeat: 1,
            install_std: false,
            cache_op: None,
            lock_op: None,
            realm_op: None,
            server: false,
        }
    }

    fn test_realm_band_source_set() -> SourceSet {
        yulang_sources::collect_inline_source_files_with_options(
            "use util::*\nx\n",
            [
                InlineSource {
                    path: PathBuf::from("<util>.yu"),
                    module_path: typed_ir::Path {
                        segments: vec![typed_ir::Name("util".to_string())],
                    },
                    origin: SourceOrigin::User,
                    source: "mod extra;\npub x = extra::x\n".to_string(),
                    meta: None,
                },
                InlineSource {
                    path: PathBuf::from("<util/extra>.yu"),
                    module_path: typed_ir::Path {
                        segments: vec![
                            typed_ir::Name("util".to_string()),
                            typed_ir::Name("extra".to_string()),
                        ],
                    },
                    origin: SourceOrigin::User,
                    source: "pub x = 1\n".to_string(),
                    meta: None,
                },
            ],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
    }

    #[test]
    fn semantic_pipeline_rejects_invalid_tokens() {
        let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green("2 ** 10"));

        assert!(has_invalid_token(&root));
    }

    #[test]
    fn source_options_searches_entry_dir_and_parent_for_local_realms() {
        let options = test_cli_options();
        let source_options = source_options(&options, Some(Path::new("workspace/app")));

        assert_eq!(
            source_options.search_paths,
            vec![PathBuf::from("workspace/app"), PathBuf::from("workspace")]
        );
    }

    #[test]
    fn lock_output_defaults_to_entry_realm_root() {
        let mut options = test_cli_options();
        options.path = Some("workspace/app/main.yu".to_string());
        let op = LockOp {
            check: false,
            out: None,
        };

        assert_eq!(
            lock_output_path(&op, &options),
            PathBuf::from("workspace/app/yulang.lock")
        );
    }

    #[test]
    fn cst_only_does_not_request_semantic_pipeline() {
        let mut options = test_cli_options();
        options.infer = false;
        options.show_cst = true;

        assert!(!options.requests_semantic_pipeline());
    }

    #[test]
    fn no_cache_disables_yuir_source_cache() {
        let mut options = test_cli_options();
        options.infer = false;
        options.control_vm = true;
        assert!(can_use_yuir_source_cache(&options));

        options.no_cache = true;
        assert!(!can_use_yuir_source_cache(&options));
        assert!(!can_write_yuir_source_cache(&options));
    }

    #[test]
    fn cacheable_dependency_manifests_cover_non_entry_band_sccs() {
        let source_set = test_realm_band_source_set();
        let manifests = cacheable_dependency_manifests(&source_set);
        let modules = manifests
            .iter()
            .flat_map(|manifest| &manifest.files)
            .map(|file| {
                file.module_path
                    .segments
                    .iter()
                    .map(|segment| segment.0.as_str())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        assert_eq!(manifests.len(), 2);
        assert!(modules.contains(&vec!["util"]));
        assert!(modules.contains(&vec!["util", "extra"]));
        assert!(
            manifests
                .iter()
                .all(|manifest| is_cacheable_dependency_manifest(manifest))
        );
        assert!(manifests.iter().all(|manifest| manifest.bands.len() == 1));
    }

    #[test]
    fn dependency_closed_cached_units_drop_sccs_with_missing_dependencies() {
        let source_set = test_realm_band_source_set();
        let manifests = cacheable_dependency_manifests(&source_set);
        let util = manifests
            .iter()
            .find(|manifest| {
                manifest.files.iter().any(|file| {
                    file.module_path
                        .segments
                        .iter()
                        .map(|segment| segment.0.as_str())
                        .collect::<Vec<_>>()
                        == vec!["util"]
                })
            })
            .expect("util manifest");
        let extra = manifests
            .iter()
            .find(|manifest| {
                manifest.files.iter().any(|file| {
                    file.module_path
                        .segments
                        .iter()
                        .map(|segment| segment.0.as_str())
                        .collect::<Vec<_>>()
                        == vec!["util", "extra"]
                })
            })
            .expect("util::extra manifest");

        assert!(
            util.dependencies
                .iter()
                .any(|dependency| dependency.unit_index == extra.unit_index)
        );
        assert!(
            dependency_closed_cached_units(&manifests, [&util.unit_index].into_iter()).is_empty()
        );
        assert_eq!(
            dependency_closed_cached_units(
                &manifests,
                [&util.unit_index, &extra.unit_index].into_iter()
            )
            .len(),
            2
        );
    }

    #[test]
    fn native_default_output_paths_use_target_yulang() {
        let object = native_object_output_path(&NativeOutput::Default, Some("examples/hello.yu"));
        let executable =
            native_executable_output_path(&NativeOutput::Default, Some("examples/hello.yu"));
        let run_executable =
            native_run_executable_output_path(&NativeOutput::Default, Some("examples/hello.yu"));
        let pure_executable =
            native_value_executable_output_path(&NativeOutput::Default, Some("examples/hello.yu"));
        let effects_executable = native_cps_repr_executable_output_path(
            &NativeOutput::Default,
            Some("examples/hello.yu"),
        );

        assert!(object.ends_with("target/yulang/obj/hello.o"));
        assert!(executable.ends_with("target/yulang/bin/hello"));
        assert!(run_executable.ends_with("target/yulang/bin/hello-native"));
        assert!(pure_executable.ends_with("target/yulang/bin/hello-pure"));
        assert!(effects_executable.ends_with("target/yulang/bin/hello-effects"));
    }

    #[test]
    fn yuir_default_output_path_uses_target_yulang() {
        let artifact = yuir_artifact_output_path(&NativeOutput::Default, Some("examples/hello.yu"));

        assert!(artifact.ends_with("target/yulang/yuir/hello.yuir"));
        assert!(is_yuir_artifact_path("target/yulang/yuir/hello.yuir"));
        assert!(is_yuir_artifact_path("target/yulang/yuir/hello.YUIR"));
        assert!(!is_yuir_artifact_path("examples/hello.yu"));
    }

    #[test]
    fn native_harnesses_discard_roots_by_default() {
        let roots = vec![NativeRootHarnessEntry {
            name: "root_0".to_string(),
            function_id: Some(7),
            print: NativeRootPrintKind::I64,
        }];

        let abi_harness = native_executable_harness(&roots, false);
        assert!(abi_harness.contains("(void)root_0();"));
        assert!(!abi_harness.contains("printf("));

        let root_names = vec!["root_0".to_string()];
        let value_harness = native_value_executable_harness(&root_names, false);
        assert!(value_harness.contains("(void)root_0(context);"));
        assert!(!value_harness.contains("yulang_native_print_value(root_0(context));"));

        let cps_harness = native_cps_repr_executable_harness(
            &roots,
            false,
            yulang_native::CpsReprCraneliftOptions::default(),
        );
        assert!(cps_harness.contains("yulang_cps_reset_i64();"));
        assert!(cps_harness.contains("YULANG_CPS_ROOT_FUNCTION_IDS: [u64; 1] = [7];"));
        assert!(cps_harness.contains("let _ = yulang_cps_take_root_result_i64(root_0());"));
        assert!(!cps_harness.contains("yulang_cps_print_i64"));
    }

    #[test]
    fn native_harnesses_print_roots_when_requested() {
        let roots = vec![NativeRootHarnessEntry {
            name: "root_0".to_string(),
            function_id: Some(7),
            print: NativeRootPrintKind::I64,
        }];

        let abi_harness = native_executable_harness(&roots, true);
        assert!(abi_harness.contains("printf(\"%lld\\n\", (long long)root_0());"));

        let root_names = vec!["root_0".to_string()];
        let value_harness = native_value_executable_harness(&root_names, true);
        assert!(value_harness.contains("yulang_native_print_value(root_0(context));"));

        let cps_harness = native_cps_repr_executable_harness(
            &roots,
            true,
            yulang_native::CpsReprCraneliftOptions::default(),
        );
        assert!(cps_harness.contains("let value = yulang_cps_take_root_result_i64(root_0());"));
        assert!(cps_harness.contains("println!(\"{}\", value);"));
    }

    #[test]
    fn native_effects_harness_prints_scalar_roots_by_kind() {
        let roots = vec![
            NativeRootHarnessEntry {
                name: "root_0".to_string(),
                function_id: Some(7),
                print: NativeRootPrintKind::Float,
            },
            NativeRootHarnessEntry {
                name: "root_1".to_string(),
                function_id: Some(8),
                print: NativeRootPrintKind::Unit,
            },
            NativeRootHarnessEntry {
                name: "root_2".to_string(),
                function_id: Some(9),
                print: NativeRootPrintKind::Bool,
            },
        ];

        let harness = native_cps_repr_executable_harness(
            &roots,
            true,
            yulang_native::CpsReprCraneliftOptions::default(),
        );
        assert!(harness.contains("fn root_0() -> f64;"));
        assert!(harness.contains("yulang_cps_float_to_string_f64(root_0())"));
        assert!(harness.contains("let _ = yulang_cps_take_root_result_i64(root_1());"));
        assert!(harness.contains("println!(\"()\");"));
        assert!(harness.contains("println!(\"{}\", value != 0);"));
    }

    #[test]
    fn native_effects_root_print_keeps_runtime_bool_hint_for_unknown_cps_lane() {
        assert_eq!(
            native_root_print_kind_from_cps_lane_and_runtime_type(
                yulang_native::CpsReprAbiLane::Unknown,
                NativeRootPrintKind::Bool,
            ),
            NativeRootPrintKind::Bool
        );
    }

    #[test]
    fn native_output_stem_sanitizes_input_name() {
        assert_eq!(
            native_output_stem(Some("dir/hello world.yu")),
            "hello_world"
        );
        assert_eq!(native_output_stem(None), "stdin");
    }

    #[test]
    fn runtime_error_source_frame_uses_apply_source_edge() {
        let program = typed_ir::CoreProgram {
            program: typed_ir::PrincipalModule {
                path: typed_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: typed_ir::CoreGraphView::default(),
            evidence: typed_ir::PrincipalEvidence {
                expected_edges: vec![typed_ir::ExpectedEdgeEvidence {
                    id: 7,
                    kind: typed_ir::ExpectedEdgeKind::ApplicationArgument,
                    source_range: Some(typed_ir::SourceRange { start: 4, end: 8 }),
                    actual: typed_ir::TypeBounds::exact(core_type("bool")),
                    expected: typed_ir::TypeBounds::exact(core_type("int")),
                    actual_effect: None,
                    expected_effect: None,
                    closed: true,
                    informative: true,
                    runtime_usable: true,
                }],
                expected_adapter_edges: Vec::new(),
                derived_expected_edges: Vec::new(),
                handler_matches: Vec::new(),
            },
        };
        let error = runtime::RuntimeError::TypeMismatch {
            expected: core_type("int"),
            actual: core_type("bool"),
            source: runtime::TypeSource::ApplyArgumentEvidence,
            context: Some(runtime::diagnostic::TypeMismatchContext {
                callee: None,
                phase: runtime::diagnostic::TypeMismatchPhase::ApplyArgument,
                callee_source_edge: None,
                arg_source_edge: Some(7),
            }),
        };

        let frame = runtime_error_source_frame(&error, &program, "1 + true\n")
            .expect("source frame from apply argument edge");

        assert!(frame.contains("at 1:5"));
        assert!(frame.contains("1 | 1 + true"));
        assert!(frame.contains("^^^^"));
    }

    fn core_type(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path {
                segments: vec![typed_ir::Name(name.to_string())],
            },
            args: Vec::new(),
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
        let mut state = lower_infer_sources(None, &root, source, &options, None).state;
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
    fn infer_error_headline_reports_missing_implicit_cast() {
        let source = concat!(
            "role Cast 'from:\n    type to\n    our from.cast: to\n\n",
            "struct user_id { raw: int }\n",
            "my id: user_id = 1\n",
        );
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let state = lower_infer_sources(None, &root, source, &options, None).state;
        let errors = state.infer.type_errors();
        let error = errors
            .iter()
            .find(|error| matches!(error.kind, InferTypeErrorKind::MissingImpl { .. }))
            .expect("missing Cast impl error should be reported");

        assert!(infer_error_headline(&state, error).starts_with("no implicit cast from int to "));
    }

    #[test]
    fn infer_error_context_reports_annotation_edge() {
        let source = "my x: int = \"s\"\n";
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let state = lower_infer_sources(None, &root, source, &options, None).state;
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
        let state = lower_infer_sources(None, &root, source, &options, None).state;
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
        let state = lower_infer_sources(None, &root, source, &options, None).state;
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
        let mut state = lower_infer_sources(None, &root, source, &options, None).state;
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
    fn infer_error_headline_reports_ambiguous_implicit_cast() {
        let source = concat!(
            "role Cast 'from:\n    type to\n    our from.cast: to\n\n",
            "struct user_id { raw: int }\n",
            "cast(x: int): user_id = user_id { raw: x }\n",
            "cast(x: int): user_id = user_id { raw: x + 1 }\n",
            "my id: user_id = 1\n",
        );
        let options = test_cli_options();
        let root = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(source, Default::default()),
        );
        let state = lower_infer_sources(None, &root, source, &options, None).state;
        let errors = state.infer.type_errors();
        let error = errors
            .iter()
            .find(|error| matches!(error.kind, InferTypeErrorKind::AmbiguousImpl { .. }))
            .expect("ambiguous Cast impl error should be reported");

        assert!(
            infer_error_headline(&state, error).starts_with("ambiguous implicit cast from int to ")
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
        let mut state = lower_infer_sources(None, &root, source, &options, None).state;
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
        let mut state = lower_infer_sources(None, &root, source, &options, None).state;
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
        let evidence = typed_ir::ApplyEvidence {
            callee_source_edge: None,
            expected_callee: None,
            arg_source_edge: None,
            callee: typed_ir::TypeBounds {
                lower: None,
                upper: Some(Box::new(typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Named {
                        path: typed_ir::Path {
                            segments: vec![typed_ir::Name("int".to_string())],
                        },
                        args: vec![],
                    }),
                    param_effect: Box::new(typed_ir::Type::Any),
                    ret_effect: Box::new(typed_ir::Type::Row {
                        items: vec![],
                        tail: Box::new(typed_ir::Type::Never),
                    }),
                    ret: Box::new(typed_ir::Type::Named {
                        path: typed_ir::Path {
                            segments: vec![typed_ir::Name("int".to_string())],
                        },
                        args: vec![],
                    }),
                })),
            },
            arg: typed_ir::TypeBounds {
                lower: Some(Box::new(typed_ir::Type::Named {
                    path: typed_ir::Path {
                        segments: vec![typed_ir::Name("int".to_string())],
                    },
                    args: vec![],
                })),
                upper: Some(Box::new(typed_ir::Type::Named {
                    path: typed_ir::Path {
                        segments: vec![typed_ir::Name("int".to_string())],
                    },
                    args: vec![],
                })),
            },
            expected_arg: None,
            result: typed_ir::TypeBounds {
                lower: Some(Box::new(typed_ir::Type::Var(typed_ir::TypeVar(
                    "a".to_string(),
                )))),
                upper: Some(Box::new(typed_ir::Type::Named {
                    path: typed_ir::Path {
                        segments: vec![typed_ir::Name("int".to_string())],
                    },
                    args: vec![],
                })),
            },
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        };

        assert_eq!(
            format_apply_evidence(&evidence),
            "apply[callee=_ <: int -> int, arg=int, result=a <: _ <: int]"
        );
    }
}
