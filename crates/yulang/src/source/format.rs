use super::*;

pub fn format_run_mono_values(values: &[mono_runtime::Value]) -> String {
    let mut out = String::new();
    let _ = write!(out, "run roots [");
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            let _ = write!(out, ", ");
        }
        let _ = write!(out, "{}", format_runtime_value(value));
    }
    let _ = writeln!(out, "]");
    out
}

pub(super) fn format_runtime_value(value: &mono_runtime::Value) -> String {
    match value {
        mono_runtime::Value::Int(value) => value.to_string(),
        mono_runtime::Value::BigInt(value) => value.to_string(),
        mono_runtime::Value::Float(value) => value.to_string(),
        mono_runtime::Value::Str(value) => format!("{value:?}"),
        mono_runtime::Value::Bool(value) => value.to_string(),
        mono_runtime::Value::Unit => "()".to_string(),
        mono_runtime::Value::Tuple(values) => format_delimited_values("(", ")", values),
        mono_runtime::Value::List(values) => {
            let values = values
                .to_vec()
                .into_iter()
                .map(|value| (*value).clone())
                .collect::<Vec<_>>();
            format_delimited_values("[", "]", &values)
        }
        mono_runtime::Value::Record(fields) => {
            let mut out = String::new();
            out.push('{');
            for (index, field) in fields.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                let _ = write!(
                    out,
                    "{}: {}",
                    field.name,
                    format_runtime_value(&field.value)
                );
            }
            out.push('}');
            out
        }
        mono_runtime::Value::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                return tag.clone();
            }
            format!("{tag}{}", format_delimited_values("(", ")", payloads))
        }
        mono_runtime::Value::DataConstructor { def, payloads } => {
            if payloads.is_empty() {
                return format!("<ctor d{}>", def.0);
            }
            format!(
                "<ctor d{}>{}",
                def.0,
                format_delimited_values("(", ")", payloads)
            )
        }
        mono_runtime::Value::ConstructorFunction(constructor) => {
            format!(
                "<ctor-fn d{} {}/{}>",
                constructor.def.0,
                constructor.args.len(),
                constructor.arity
            )
        }
        mono_runtime::Value::PrimitiveOp(primitive) => {
            format!(
                "<prim {:?} {}/{}>",
                primitive.op,
                primitive.args.len(),
                primitive.op.arity()
            )
        }
        mono_runtime::Value::Closure(_) | mono_runtime::Value::RecursiveClosure { .. } => {
            "<closure>".to_string()
        }
        mono_runtime::Value::Thunk(_) => "<thunk>".to_string(),
        mono_runtime::Value::FunctionAdapter(_) => "<function-adapter>".to_string(),
        mono_runtime::Value::EffectOp { path } => format!("<effect-op {}>", path.join("::")),
        mono_runtime::Value::Continuation(id) => format!("<continuation {}>", id.0),
        mono_runtime::Value::Marked { value, .. } => format_runtime_value(value),
    }
}

pub(super) fn format_delimited_values(
    open: &str,
    close: &str,
    values: &[mono_runtime::Value],
) -> String {
    let mut out = String::new();
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_runtime_value(value));
    }
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}

pub(super) fn format_check_poly_output(
    file_count: usize,
    check: &infer::check::PolyCheckOutput,
    timing: &CheckPolyTimings,
    title: &str,
) -> String {
    let report = &check.report;
    let totals = &report.totals;
    let mut out = String::new();
    let _ = writeln!(out, "{title}");
    let _ = writeln!(out, "files: {file_count}");
    write_check_timing(&mut out, timing);
    let _ = writeln!(out, "summary:");
    let _ = writeln!(out, "  modules: {}", totals.modules);
    let _ = writeln!(out, "  module values: {}", totals.module_values);
    let _ = writeln!(out, "  type decls: {}", totals.type_decls);
    let _ = writeln!(out, "  child modules: {}", totals.child_modules);
    let _ = writeln!(out, "  let defs: {}", totals.let_defs);
    let _ = writeln!(out, "  typed lets: {}", totals.typed_lets);
    let _ = writeln!(out, "  missing schemes: {}", totals.missing_schemes);
    let _ = writeln!(out, "  bodyless declarations: {}", totals.bodyless_decls);
    let _ = writeln!(out, "  stack schemes: {}", totals.stack_schemes);
    let _ = writeln!(out, "  lowering errors: {}", totals.lowering_errors);
    if totals.unowned_errors > 0 {
        let _ = writeln!(out, "  unowned errors: {}", totals.unowned_errors);
    }

    let _ = writeln!(out, "modules:");
    for module in &report.modules {
        let _ = writeln!(
            out,
            "  {}: values {} typed {} missing_schemes {} bodyless {} stack_schemes {} errors {} types {} child_modules {}",
            infer::check::format_path(&module.path),
            module.value_count,
            module.typed_lets,
            module.missing_schemes,
            module.bodyless_decls,
            module.stack_schemes,
            module.local_errors,
            module.type_count,
            module.child_module_count
        );
    }

    if !report.missing_schemes.is_empty() {
        let _ = writeln!(out, "missing schemes:");
        for item in &report.missing_schemes {
            let _ = writeln!(out, "  d{}: {}", item.def.0, item.label);
        }
    }

    if !report.bodyless_decls.is_empty() {
        let _ = writeln!(out, "bodyless declarations:");
        for item in &report.bodyless_decls {
            let _ = writeln!(out, "  d{}: {}", item.def.0, item.label);
        }
    }

    write_check_diagnostics(&mut out, check, &report.diagnostics);

    out
}

pub(super) fn format_check_poly_module_output(
    file_count: usize,
    check: &infer::check::PolyCheckOutput,
    module: &infer::check::ModuleCheck,
    timing: &CheckPolyTimings,
    title: &str,
) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "{} {}", title, infer::check::format_path(&module.path));
    let _ = writeln!(out, "files: {file_count}");
    write_check_timing(&mut out, timing);
    let _ = writeln!(out, "summary:");
    let _ = writeln!(out, "  values: {}", module.value_count);
    let _ = writeln!(out, "  typed lets: {}", module.typed_lets);
    let _ = writeln!(out, "  missing schemes: {}", module.missing_schemes);
    let _ = writeln!(out, "  bodyless declarations: {}", module.bodyless_decls);
    let _ = writeln!(out, "  stack schemes: {}", module.stack_schemes);
    let _ = writeln!(
        out,
        "  lowering errors: {} local / {} total",
        module.local_errors, check.report.totals.lowering_errors
    );
    let _ = writeln!(out, "  types: {}", module.type_count);
    let _ = writeln!(out, "  child modules: {}", module.child_module_count);

    if !module.missing_scheme_defs.is_empty() {
        let _ = writeln!(out, "missing schemes:");
        for item in &module.missing_scheme_defs {
            let _ = writeln!(out, "  d{}: {}", item.def.0, item.label);
        }
    }

    if !module.bodyless_defs.is_empty() {
        let _ = writeln!(out, "bodyless declarations:");
        for item in &module.bodyless_defs {
            let _ = writeln!(out, "  d{}: {}", item.def.0, item.label);
        }
    }

    write_check_diagnostics(&mut out, check, &module.diagnostics);

    out
}

pub(super) fn write_check_timing(out: &mut String, timing: &CheckPolyTimings) {
    let _ = writeln!(out, "timing:");
    let _ = writeln!(out, "  collect: {}", format_duration(timing.collect));
    let _ = writeln!(out, "  load: {}", format_duration(timing.load));
    let _ = writeln!(out, "  infer: {}", format_duration(timing.infer));
    let _ = writeln!(out, "  summarize: {}", format_duration(timing.summarize));
    let _ = writeln!(out, "  total: {}", format_duration(timing.total));
}

pub(super) fn write_check_diagnostics(
    out: &mut String,
    check: &infer::check::PolyCheckOutput,
    diagnostics: &[infer::check::CheckDiagnostic],
) {
    if diagnostics.is_empty() {
        return;
    }
    let _ = writeln!(out, "lowering errors:");
    for diagnostic in diagnostics {
        let label = diagnostic.label.as_deref().unwrap_or("<unowned>");
        let error = &check.lowering.errors[diagnostic.error_index];
        let _ = writeln!(out, "  {label}: {}", format_body_lowering_error(error));
    }
}

pub(super) fn format_body_lowering_error(error: &infer::lowering::BodyLoweringError) -> String {
    match error {
        infer::lowering::BodyLoweringError::Expr {
            error: infer::lowering::LoweringError::TypeMismatch { actual, expected },
            ..
        } => format!("type mismatch: {actual} is not {expected}"),
        infer::lowering::BodyLoweringError::Expr {
            error:
                infer::lowering::LoweringError::AnnotationBuild {
                    error: infer::annotation::AnnBuildError::UnresolvedTypeName { path },
                },
            ..
        } => format!("unresolved type name: {}", format_name_path(path)),
        infer::lowering::BodyLoweringError::Expr {
            error:
                infer::lowering::LoweringError::NegSignatureBuild {
                    error: infer::lowering::NegSignatureBuildError::UnresolvedTypeName { path },
                },
            ..
        } => format!("unresolved type name: {}", format_name_path(path)),
        infer::lowering::BodyLoweringError::Expr {
            error: infer::lowering::LoweringError::UnresolvedName { name },
            ..
        } => format!("unresolved value name: {}", name.0),
        infer::lowering::BodyLoweringError::RootExpr {
            error: infer::lowering::LoweringError::UnresolvedName { name },
        } => format!("unresolved value name in root expression: {}", name.0),
        infer::lowering::BodyLoweringError::RootExpr { error } => {
            format!("root expression lowering error: {error:?}")
        }
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::ComputedFetchCycle {
                component,
                parent,
                target,
            },
        ) => format!(
            "computed value fetch in recursive component: component {}, edge d{} -> d{}",
            component
                .iter()
                .map(|def| format!("d{}", def.0))
                .collect::<Vec<_>>()
                .join(","),
            parent.0,
            target.0
        ),
        _ => format!("{error:?}"),
    }
}

pub(super) fn format_name_path(path: &[Name]) -> String {
    path.iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

pub(super) fn format_duration(duration: Duration) -> String {
    let seconds = duration.as_secs_f64();
    if seconds >= 1.0 {
        return format!("{seconds:.3}s");
    }
    let millis = seconds * 1000.0;
    if millis >= 1.0 {
        return format!("{millis:.1}ms");
    }
    let micros = seconds * 1_000_000.0;
    format!("{micros:.0}us")
}
