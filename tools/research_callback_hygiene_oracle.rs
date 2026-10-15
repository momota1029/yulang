// External research driver for frozen Oracle a58eefc31e22141574b6f20c6a5748151c6d79f1.
// Follows the web compact-stdlib source route, without automatic fallback.
// Native cache behavior is controlled by the caller's YULANG_CACHE_DIR.
use std::{env, fs, process::ExitCode};

fn run() -> Result<(), String> {
    let mut args = env::args_os().skip(1);
    let path = args.next().ok_or("expected the unchanged source file path")?;
    if args.next().is_some() {
        return Err("expected exactly one source file path".into());
    }
    let source = fs::read_to_string(&path)
        .map_err(|error| format!("source read failed: {error}"))?;
    if yulang::source_text_needs_full_embedded_std_for_playground(&source) {
        return Err("source is not eligible for the web compact-stdlib route".into());
    }
    eprintln!("stage: compact source-to-poly");
    let poly = yulang::build_poly_from_source_text_with_embedded_playground_std(
        "playground.yu", source,
    ).map_err(|error| format!("compact poly build failed: {error}"))?;
    if !poly.errors.is_empty() {
        for error in &poly.errors {
            eprintln!("lowering error: {error}");
        }
        return Err("compact poly build reported lowering errors; execution withheld".into());
    }
    poly.ensure_runtime_ready()
        .map_err(|error| format!("poly runtime readiness failed: {error}"))?;
    // Display only the user-exported g scheme; this does not modify the graph.
    for def in &poly.arena.roots {
        if poly.labels.def_label(*def) != Some("g") {
            continue;
        }
        if let Some(poly::expr::Def::Let { scheme: Some(scheme), vis, .. }) =
            poly.arena.defs.get(*def)
        {
            if matches!(vis, poly::expr::Vis::Pub | poly::expr::Vis::Our) {
                println!("type g: {}", poly::dump::format_scheme_public(
                    &poly.arena.typ, scheme,
                ).text);
            }
        }
    }
    eprintln!("stage: poly-to-control");
    let control = yulang::build_control_from_poly_output(&poly)
        .map_err(|error| format!("control build failed: {error}"))?;
    if !control.errors.is_empty() {
        return Err(format!("control build reported errors: {:?}", control.errors));
    }
    eprintln!("stage: evidence plan and VM");
    let plan = evidence_vm::build_plan(&control.program, &control.runtime_evidence);
    let output = evidence_vm::run_program_with_plan_print_nth_label(
        &control.program, &plan, "Out",
    ).map_err(|error| format!("evidence VM failed: {error} ({error:?})"))?;
    print!("{}", output.stdout);
    print!("{}", output.roots_text_with_labels(Some(&control.labels)));
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
