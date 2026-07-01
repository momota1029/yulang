use super::*;

pub fn format_run_mono_values(values: &[mono_runtime::Value]) -> String {
    format_run_mono_values_with_labels(values, None)
}

pub fn format_run_mono_values_with_labels(
    values: &[mono_runtime::Value],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    let mut out = String::new();
    let _ = write!(out, "run roots [");
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            let _ = write!(out, ", ");
        }
        let _ = write!(out, "{}", format_runtime_value_with_labels(value, labels));
    }
    let _ = writeln!(out, "]");
    out
}

fn format_runtime_value_with_labels(
    value: &mono_runtime::Value,
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    if let Some(fraction) = format_runtime_fraction_value(value) {
        return fraction;
    }

    match value {
        mono_runtime::Value::Int(value) => value.to_string(),
        mono_runtime::Value::BigInt(value) => value.to_string(),
        mono_runtime::Value::Float(value) => value.to_string(),
        mono_runtime::Value::Str(value) => format!("{:?}", value.to_flat_string()),
        mono_runtime::Value::Bytes(value) => format!("<bytes len={}>", value.len()),
        mono_runtime::Value::Bool(value) => value.to_string(),
        mono_runtime::Value::Unit => "()".to_string(),
        mono_runtime::Value::Tuple(values) => {
            format_delimited_mono_values("(", ")", values, labels)
        }
        mono_runtime::Value::List(values) => {
            let values = values
                .to_vec()
                .into_iter()
                .map(|value| (*value).clone())
                .collect::<Vec<_>>();
            format_delimited_mono_values("[", "]", &values, labels)
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
                    format_runtime_value_with_labels(&field.value, labels)
                );
            }
            out.push('}');
            out
        }
        mono_runtime::Value::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                return tag.clone();
            }
            format!("{tag}{}", format_mono_call_payloads(payloads, labels))
        }
        mono_runtime::Value::DataConstructor { def, payloads } => {
            let constructor = format_constructor_name(labels, def.0);
            if payloads.is_empty() {
                return constructor;
            }
            format!(
                "{}{}",
                constructor,
                format_mono_call_payloads(payloads, labels)
            )
        }
        mono_runtime::Value::ConstructorFunction(constructor) => {
            let name = format_constructor_name(labels, constructor.def.0);
            format!(
                "<ctor-fn {} {}/{}>",
                name,
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
        mono_runtime::Value::Marked { value, .. } => {
            format_runtime_value_with_labels(value, labels)
        }
    }
}

pub(super) fn format_run_control_values_with_labels(
    values: &[control_vm::Value],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    let mut out = String::new();
    let _ = write!(out, "run roots [");
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            let _ = write!(out, ", ");
        }
        let _ = write!(out, "{}", format_control_value_with_labels(value, labels));
    }
    let _ = writeln!(out, "]");
    out
}

fn format_control_value_with_labels(
    value: &control_vm::Value,
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    if let Some(fraction) = format_control_fraction_value(value) {
        return fraction;
    }

    match value {
        control_vm::Value::Int(value) => value.to_string(),
        control_vm::Value::BigInt(value) => value.to_string(),
        control_vm::Value::Float(value) => value.to_string(),
        control_vm::Value::Str(value) => format!("{:?}", value.to_flat_string()),
        control_vm::Value::Bytes(value) => format!("<bytes len={}>", value.len()),
        control_vm::Value::Bool(value) => value.to_string(),
        control_vm::Value::Unit => "()".to_string(),
        control_vm::Value::Tuple(values) => {
            format_delimited_control_values("(", ")", values, labels)
        }
        control_vm::Value::List(values) => {
            let values = values
                .to_vec()
                .into_iter()
                .map(|value| (*value).clone())
                .collect::<Vec<_>>();
            format_delimited_control_values("[", "]", &values, labels)
        }
        control_vm::Value::Record(fields) => {
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
                    format_control_value_with_labels(&field.value, labels)
                );
            }
            out.push('}');
            out
        }
        control_vm::Value::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                return tag.clone();
            }
            format!("{tag}{}", format_control_call_payloads(payloads, labels))
        }
        control_vm::Value::DataConstructor { def, payloads } => {
            let constructor = format_constructor_name(labels, def.0);
            if payloads.is_empty() {
                return constructor;
            }
            format!(
                "{}{}",
                constructor,
                format_control_call_payloads(payloads, labels)
            )
        }
        control_vm::Value::ConstructorFunction(constructor) => {
            let name = format_constructor_name(labels, constructor.def.0);
            format!(
                "<ctor-fn {} {}/{}>",
                name,
                constructor.args.len(),
                constructor.arity
            )
        }
        control_vm::Value::PrimitiveOp(primitive) => {
            format!(
                "<prim {:?} {}/{}>",
                primitive.op,
                primitive.args.len(),
                primitive.op.arity()
            )
        }
        control_vm::Value::Closure(_) | control_vm::Value::RecursiveClosure { .. } => {
            "<closure>".to_string()
        }
        control_vm::Value::Thunk(_) => "<thunk>".to_string(),
        control_vm::Value::FunctionAdapter(_) => "<function-adapter>".to_string(),
        control_vm::Value::EffectOp { path, .. } => format!("<effect-op {}>", path.join("::")),
        control_vm::Value::Continuation(id) => format!("<continuation {}>", id.0),
        control_vm::Value::Marked { value, .. } => format_control_value_with_labels(value, labels),
    }
}

fn format_runtime_fraction_value(value: &mono_runtime::Value) -> Option<String> {
    // Runtime values erase struct identity, so raw root formatting recognizes
    // std::num::frac by its canonical lowered shape.
    match value {
        mono_runtime::Value::Record(fields) => format_runtime_fraction_record(fields),
        mono_runtime::Value::DataConstructor { payloads, .. } if payloads.len() == 1 => {
            format_runtime_fraction_payload(&payloads[0])
        }
        mono_runtime::Value::Marked { value, .. } => format_runtime_fraction_value(value),
        _ => None,
    }
}

fn format_runtime_fraction_payload(value: &mono_runtime::Value) -> Option<String> {
    match value {
        mono_runtime::Value::Record(fields) => format_runtime_fraction_record(fields),
        mono_runtime::Value::Marked { value, .. } => format_runtime_fraction_payload(value),
        _ => None,
    }
}

fn format_runtime_fraction_record(fields: &[mono_runtime::ValueField]) -> Option<String> {
    if fields.len() != 2 {
        return None;
    }

    let num = runtime_int_field(fields, "num")?;
    let den = runtime_int_field(fields, "den")?;
    if den == 1 {
        Some(num.to_string())
    } else {
        Some(format!("{num}/{den}"))
    }
}

fn runtime_int_field(fields: &[mono_runtime::ValueField], name: &str) -> Option<i64> {
    fields
        .iter()
        .find(|field| field.name.as_str() == name)
        .and_then(|field| runtime_int_value(&field.value))
}

fn runtime_int_value(value: &mono_runtime::Value) -> Option<i64> {
    match value {
        mono_runtime::Value::Int(value) => Some(*value),
        mono_runtime::Value::Marked { value, .. } => runtime_int_value(value),
        _ => None,
    }
}

fn format_control_fraction_value(value: &control_vm::Value) -> Option<String> {
    // Runtime values erase struct identity, so raw root formatting recognizes
    // std::num::frac by its canonical lowered shape.
    match value {
        control_vm::Value::Record(fields) => format_control_fraction_record(fields),
        control_vm::Value::DataConstructor { payloads, .. } if payloads.len() == 1 => {
            format_control_fraction_payload(&payloads[0])
        }
        control_vm::Value::Marked { value, .. } => format_control_fraction_value(value),
        _ => None,
    }
}

fn format_control_fraction_payload(value: &control_vm::Value) -> Option<String> {
    match value {
        control_vm::Value::Record(fields) => format_control_fraction_record(fields),
        control_vm::Value::Marked { value, .. } => format_control_fraction_payload(value),
        _ => None,
    }
}

fn format_control_fraction_record(fields: &[control_vm::ValueField]) -> Option<String> {
    if fields.len() != 2 {
        return None;
    }

    let num = control_int_field(fields, "num")?;
    let den = control_int_field(fields, "den")?;
    if den == 1 {
        Some(num.to_string())
    } else {
        Some(format!("{num}/{den}"))
    }
}

fn control_int_field(fields: &[control_vm::ValueField], name: &str) -> Option<i64> {
    fields
        .iter()
        .find(|field| field.name.as_str() == name)
        .and_then(|field| control_int_value(&field.value))
}

fn control_int_value(value: &control_vm::Value) -> Option<i64> {
    match value {
        control_vm::Value::Int(value) => Some(*value),
        control_vm::Value::Marked { value, .. } => control_int_value(value),
        _ => None,
    }
}

fn format_delimited_mono_values(
    open: &str,
    close: &str,
    values: &[mono_runtime::Value],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    let mut out = String::new();
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_runtime_value_with_labels(value, labels));
    }
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}

fn format_delimited_control_values(
    open: &str,
    close: &str,
    values: &[control_vm::Value],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    let mut out = String::new();
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_control_value_with_labels(value, labels));
    }
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}

fn format_mono_call_payloads(
    values: &[mono_runtime::Value],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    format_delimited_mono_values_without_single_tuple_marker("(", ")", values, labels)
}

fn format_control_call_payloads(
    values: &[control_vm::Value],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    format_delimited_control_values_without_single_tuple_marker("(", ")", values, labels)
}

fn format_delimited_mono_values_without_single_tuple_marker(
    open: &str,
    close: &str,
    values: &[mono_runtime::Value],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    let mut out = String::new();
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_runtime_value_with_labels(value, labels));
    }
    out.push_str(close);
    out
}

fn format_delimited_control_values_without_single_tuple_marker(
    open: &str,
    close: &str,
    values: &[control_vm::Value],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    let mut out = String::new();
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_control_value_with_labels(value, labels));
    }
    out.push_str(close);
    out
}

fn format_constructor_name(labels: Option<&poly::dump::DumpLabels>, def: u32) -> String {
    let Some(label) = labels.and_then(|labels| labels.def_label(poly::expr::DefId(def))) else {
        return format!("<ctor d{def}>");
    };
    shorten_constructor_label(label)
}

fn shorten_constructor_label(label: &str) -> String {
    let mut parts = label.rsplit('.').filter(|part| !part.is_empty());
    let Some(last) = parts.next() else {
        return label.to_string();
    };
    let Some(parent) = parts.next() else {
        return last.to_string();
    };
    format!("{parent}::{last}")
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
    let _ = writeln!(
        out,
        "  lower.index_csts: {}",
        format_duration(timing.lowering.index_csts)
    );
    let _ = writeln!(
        out,
        "  lower.module_map: {}",
        format_duration(timing.lowering.module_map)
    );
    let _ = writeln!(
        out,
        "  lower.init: {}",
        format_duration(timing.lowering.init_lowerer)
    );
    let _ = writeln!(
        out,
        "  lower.bodies: {}",
        format_duration(timing.lowering.lower_bodies)
    );
    let _ = writeln!(
        out,
        "  lower.synthetic: {}",
        format_duration(timing.lowering.synthetic_act_copy)
    );
    let _ = writeln!(
        out,
        "  lower.drain: {}",
        format_duration(timing.lowering.drain_analysis)
    );
    let _ = writeln!(
        out,
        "  lower.resolve: {}",
        format_duration(timing.lowering.resolve_selections)
    );
    let analysis = timing.lowering.analysis;
    write_check_hardening_metrics(out, timing);
    let _ = writeln!(
        out,
        "  analysis.route: {}",
        format_duration(analysis.route_constraints)
    );
    let _ = writeln!(
        out,
        "  analysis.route_scc_events: {}",
        format_duration(analysis.route_scc_events)
    );
    let _ = writeln!(
        out,
        "  analysis.route_scc_open_use: {}",
        format_duration(analysis.route_scc_open_use)
    );
    let _ = writeln!(
        out,
        "  analysis.route_scc_quantify: {}",
        format_duration(analysis.route_scc_quantify)
    );
    let _ = writeln!(
        out,
        "  analysis.route_scc_instantiate: {}",
        format_duration(analysis.route_scc_instantiate)
    );
    let _ = writeln!(
        out,
        "  analysis.route_scc_other: {}",
        format_duration(analysis.route_scc_other)
    );
    let _ = writeln!(
        out,
        "  analysis.scc_apply: {}",
        format_duration(analysis.scc_apply)
    );
    let _ = writeln!(
        out,
        "  analysis.work: {}",
        format_duration(analysis.work_total)
    );
    let _ = writeln!(
        out,
        "  analysis.work_resolve_ref: {}",
        format_duration(analysis.work_resolve_ref)
    );
    let _ = writeln!(
        out,
        "  analysis.work_probe_select: {}",
        format_duration(analysis.work_probe_select)
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_ref: {}",
        format_duration(analysis.work_apply_ref)
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select: {}",
        format_duration(analysis.work_apply_select)
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select_record_field: {}",
        format_duration(analysis.work_apply_select_record_field)
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select_method: {}",
        format_duration(analysis.work_apply_select_method)
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select_effect_method: {}",
        format_duration(analysis.work_apply_select_effect_method)
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select_typeclass_method: {}",
        format_duration(analysis.work_apply_select_typeclass_method)
    );
    let _ = writeln!(
        out,
        "  analysis.work_scc: {}",
        format_duration(analysis.work_scc)
    );
    let _ = writeln!(
        out,
        "  analysis.role: {}",
        format_duration(analysis.role_pass)
    );
    let _ = writeln!(
        out,
        "  analysis.taint: {}",
        format_duration(analysis.method_taint)
    );
    let _ = writeln!(
        out,
        "  analysis.role_solve: {}",
        format_duration(analysis.method_role_solve)
    );
    let _ = writeln!(
        out,
        "  analysis.unready_role_dependency_scan: {}",
        format_duration(analysis.unready_role_dependency_scan)
    );
    let _ = writeln!(
        out,
        "  analysis.quantify: {}",
        format_duration(analysis.quantify)
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_generalize: {}",
        format_duration(analysis.quantify_generalize)
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_prerequisites: {}",
        format_duration(analysis.quantify_prerequisites)
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_finalize: {}",
        format_duration(analysis.quantify_finalize)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact: {}",
        format_duration(analysis.generalize_compact)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_collect_roles: {}",
        format_duration(analysis.generalize_collect_roles)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_apply_merge: {}",
        format_duration(analysis.generalize_apply_merge)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_collect_dominance: {}",
        format_duration(analysis.generalize_collect_dominance)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_apply_subtype: {}",
        format_duration(analysis.generalize_apply_subtype)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_cast: {}",
        format_duration(analysis.generalize_cast)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_resolve_roles: {}",
        format_duration(analysis.generalize_resolve_roles)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_final_roles: {}",
        format_duration(analysis.generalize_final_roles)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_final_cleanup: {}",
        format_duration(analysis.generalize_final_cleanup)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_filter_roles: {}",
        format_duration(analysis.generalize_filter_roles)
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_prepared: {}",
        format_duration(analysis.generalize_prepared)
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate: {}",
        format_duration(analysis.instantiate)
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_clone_scheme: {}",
        format_duration(analysis.instantiate_clone_scheme)
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_subtype_predicate: {}",
        format_duration(analysis.instantiate_subtype_predicate)
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_insert_roles: {}",
        format_duration(analysis.instantiate_insert_roles)
    );
    let _ = writeln!(
        out,
        "  analysis.record_field: {}",
        format_duration(analysis.record_field_fallback)
    );
    let constraint = timing.lowering.constraint;
    let _ = writeln!(
        out,
        "  constraint.drain: {}",
        format_duration(constraint.drain)
    );
    let _ = writeln!(out, "  constraint.drains: {}", constraint.drains);
    let _ = writeln!(
        out,
        "  constraint.empty_drains: {}",
        constraint.empty_drains
    );
    let _ = writeln!(out, "  constraint.work_items: {}", constraint.work_items);
    let _ = writeln!(
        out,
        "  constraint.subtype_work_items: {}",
        constraint.subtype_work_items
    );
    let _ = writeln!(
        out,
        "  constraint.subtract_work_items: {}",
        constraint.subtract_work_items
    );
    let _ = writeln!(
        out,
        "  constraint.max_initial_queue: {}",
        constraint.max_initial_queue
    );
    let _ = writeln!(
        out,
        "  constraint.max_work_items: {}",
        constraint.max_work_items
    );
    let _ = writeln!(
        out,
        "  constraint.subtype_calls: {}",
        constraint.subtype_calls
    );
    let _ = writeln!(
        out,
        "  constraint.subtype_many_calls: {}",
        constraint.subtype_many_calls
    );
    let _ = writeln!(
        out,
        "  constraint.subtype_many_items: {}",
        constraint.subtype_many_items
    );
    let _ = writeln!(
        out,
        "  constraint.weighted_subtype_calls: {}",
        constraint.weighted_subtype_calls
    );
    let _ = writeln!(
        out,
        "  constraint.constrain_subtype_calls: {}",
        constraint.constrain_subtype_calls
    );
    let _ = writeln!(
        out,
        "  constraint.constrain_invariant_neu_calls: {}",
        constraint.constrain_invariant_neu_calls
    );
    let _ = writeln!(
        out,
        "  constraint.constrain_var_var_direct_calls: {}",
        constraint.constrain_var_var_direct_calls
    );
    let _ = writeln!(
        out,
        "  constraint.constrain_var_var_direct_pairs: {}",
        constraint.constrain_var_var_direct_pairs
    );
    let _ = writeln!(
        out,
        "  constraint.constrain_pos_var_direct_calls: {}",
        constraint.constrain_pos_var_direct_calls
    );
    let _ = writeln!(
        out,
        "  constraint.subtract_fact_calls: {}",
        constraint.subtract_fact_calls
    );
    let _ = writeln!(
        out,
        "  constraint.lower_bounds_added: {}",
        constraint.lower_bounds_added
    );
    let _ = writeln!(
        out,
        "  constraint.upper_bounds_added: {}",
        constraint.upper_bounds_added
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_inputs: {}",
        constraint.lower_replay_inputs
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_inputs: {}",
        constraint.upper_replay_inputs
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_enqueued: {}",
        constraint.lower_replay_enqueued
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_enqueued: {}",
        constraint.upper_replay_enqueued
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_accepted: {}",
        constraint.lower_replay_accepted
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_accepted: {}",
        constraint.upper_replay_accepted
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_evidence_only: {}",
        constraint.lower_replay_evidence_only
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_evidence_only: {}",
        constraint.upper_replay_evidence_only
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_duplicate: {}",
        constraint.lower_replay_duplicate
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_duplicate: {}",
        constraint.upper_replay_duplicate
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_trivial: {}",
        constraint.lower_replay_trivial
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_trivial: {}",
        constraint.upper_replay_trivial
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_prefiltered: {}",
        constraint.lower_replay_prefiltered
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_prefiltered: {}",
        constraint.upper_replay_prefiltered
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_prefilter_duplicate_exact_key: {}",
        constraint.lower_replay_prefilter_duplicate.exact_key
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_prefilter_duplicate_exact_key: {}",
        constraint.upper_replay_prefilter_duplicate.exact_key
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_prefilter_duplicate_var_var_key: {}",
        constraint.lower_replay_prefilter_duplicate.var_var_key
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_prefilter_duplicate_var_var_key: {}",
        constraint.upper_replay_prefilter_duplicate.var_var_key
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_prefilter_duplicate_terminal_erased: {}",
        constraint
            .lower_replay_prefilter_duplicate
            .terminal_weight_erased
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_prefilter_duplicate_terminal_erased: {}",
        constraint
            .upper_replay_prefilter_duplicate
            .terminal_weight_erased
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_prefilter_duplicate_row_tail: {}",
        constraint.lower_replay_prefilter_duplicate.row_tail
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_prefilter_duplicate_row_tail: {}",
        constraint.upper_replay_prefilter_duplicate.row_tail
    );
    let _ = writeln!(
        out,
        "  constraint.lower_replay_var_var: {}",
        constraint.lower_replay_var_var
    );
    let _ = writeln!(
        out,
        "  constraint.upper_replay_var_var: {}",
        constraint.upper_replay_var_var
    );
    let _ = writeln!(
        out,
        "  constraint.max_lower_replay_inputs: {}",
        constraint.max_lower_replay_inputs
    );
    let _ = writeln!(
        out,
        "  constraint.max_upper_replay_inputs: {}",
        constraint.max_upper_replay_inputs
    );
    let _ = writeln!(
        out,
        "  constraint.max_lower_replay_enqueued: {}",
        constraint.max_lower_replay_enqueued
    );
    let _ = writeln!(
        out,
        "  constraint.max_upper_replay_enqueued: {}",
        constraint.max_upper_replay_enqueued
    );
    let _ = writeln!(
        out,
        "  constraint.max_lower_replay_accepted: {}",
        constraint.max_lower_replay_accepted
    );
    let _ = writeln!(
        out,
        "  constraint.max_upper_replay_accepted: {}",
        constraint.max_upper_replay_accepted
    );
    let _ = writeln!(
        out,
        "  constraint.max_lower_replay_duplicate: {}",
        constraint.max_lower_replay_duplicate
    );
    let _ = writeln!(
        out,
        "  constraint.max_upper_replay_duplicate: {}",
        constraint.max_upper_replay_duplicate
    );
    let _ = writeln!(
        out,
        "  constraint.max_lower_replay_trivial: {}",
        constraint.max_lower_replay_trivial
    );
    let _ = writeln!(
        out,
        "  constraint.max_upper_replay_trivial: {}",
        constraint.max_upper_replay_trivial
    );
    let _ = writeln!(
        out,
        "  constraint.max_lower_replay_prefiltered: {}",
        constraint.max_lower_replay_prefiltered
    );
    let _ = writeln!(
        out,
        "  constraint.max_upper_replay_prefiltered: {}",
        constraint.max_upper_replay_prefiltered
    );
    let _ = writeln!(
        out,
        "  constraint.max_lower_replay_var_var: {}",
        constraint.max_lower_replay_var_var
    );
    let _ = writeln!(
        out,
        "  constraint.max_upper_replay_var_var: {}",
        constraint.max_upper_replay_var_var
    );
    let lower_frontier = constraint.replay_frontier_shadow_lower_var_var;
    let upper_frontier = constraint.replay_frontier_shadow_upper_var_var;
    let frontier_candidates = lower_frontier.candidates + upper_frontier.candidates;
    if frontier_candidates > 0 {
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_lower_var_var_candidates: {}",
            lower_frontier.candidates
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_upper_var_var_candidates: {}",
            upper_frontier.candidates
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_lower_var_var_hits: {}",
            lower_frontier.hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_upper_var_var_hits: {}",
            upper_frontier.hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_lower_var_var_safe_hits: {}",
            lower_frontier.safe_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_upper_var_var_safe_hits: {}",
            upper_frontier.safe_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_lower_var_var_unsafe_hits: {}",
            lower_frontier.unsafe_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_upper_var_var_unsafe_hits: {}",
            upper_frontier.unsafe_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_lower_var_var_unsafe_accepted: {}",
            lower_frontier.unsafe_accepted
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_upper_var_var_unsafe_accepted: {}",
            upper_frontier.unsafe_accepted
        );
    }
    let routing = constraint.replay_routing_shadow_var_var;
    if routing.accepted_edges > 0 {
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_accepted_edges: {}",
            routing.accepted_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_repeated_endpoint_edges: {}",
            routing.repeated_endpoint_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_reachable_before_edges: {}",
            routing.reachable_before_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_graph_nodes: {}",
            routing.graph_nodes
        );
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_graph_edges: {}",
            routing.graph_edges
        );
    }
    let weighted_routing = constraint.replay_weighted_routing_shadow_var_var;
    if weighted_routing.accepted_edges > 0 {
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_accepted_edges: {}",
            weighted_routing.accepted_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_reachable_before_edges: {}",
            weighted_routing.reachable_before_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_capped_searches: {}",
            weighted_routing.capped_searches
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_search_states: {}",
            weighted_routing.search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_max_search_states: {}",
            weighted_routing.max_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_inserted_edges: {}",
            weighted_routing.frontier_inserted_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_skipped_edges: {}",
            weighted_routing.frontier_skipped_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_capped_searches: {}",
            weighted_routing.frontier_capped_searches
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_search_states: {}",
            weighted_routing.frontier_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_max_search_states: {}",
            weighted_routing.frontier_max_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_queries: {}",
            weighted_routing.consequence_queries
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_known: {}",
            weighted_routing.consequence_known
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_known_unseen: {}",
            weighted_routing.consequence_known_unseen
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_unknown: {}",
            weighted_routing.consequence_unknown
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_unknown_seen: {}",
            weighted_routing.consequence_unknown_seen
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_capped_searches: {}",
            weighted_routing.consequence_capped_searches
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_search_states: {}",
            weighted_routing.consequence_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_max_search_states: {}",
            weighted_routing.consequence_max_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_known: {}",
            weighted_routing.consequence_frontier_known
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_known_unseen: {}",
            weighted_routing.consequence_frontier_known_unseen
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_unknown: {}",
            weighted_routing.consequence_frontier_unknown
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_unknown_seen: {}",
            weighted_routing.consequence_frontier_unknown_seen
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_capped_searches: {}",
            weighted_routing.consequence_frontier_capped_searches
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_search_states: {}",
            weighted_routing.consequence_frontier_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_max_search_states: {}",
            weighted_routing.consequence_frontier_max_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_graph_nodes: {}",
            weighted_routing.graph_nodes
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_graph_edges: {}",
            weighted_routing.graph_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_graph_nodes: {}",
            weighted_routing.frontier_graph_nodes
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_graph_edges: {}",
            weighted_routing.frontier_graph_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_route_cache_hits: {}",
            weighted_routing.route_cache_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_route_cache_hits: {}",
            weighted_routing.frontier_route_cache_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_route_cache_entries: {}",
            weighted_routing.route_cache_entries
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_route_cache_entries: {}",
            weighted_routing.frontier_route_cache_entries
        );
        if weighted_routing.summary_observed_edges > 0 {
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_observed_edges: {}",
                weighted_routing.summary_observed_edges
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_known_edges: {}",
                weighted_routing.summary_known_edges
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_new_edges: {}",
                weighted_routing.summary_new_edges
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_inserted_paths: {}",
                weighted_routing.summary_inserted_paths
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_duplicate_paths: {}",
                weighted_routing.summary_duplicate_paths
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_capped_insertions: {}",
                weighted_routing.summary_capped_insertions
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_max_queue: {}",
                weighted_routing.summary_max_queue
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_paths: {}",
                weighted_routing.summary_paths
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_outgoing_nodes: {}",
                weighted_routing.summary_outgoing_nodes
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_incoming_nodes: {}",
                weighted_routing.summary_incoming_nodes
            );
        }
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_weight_count: {}",
            weighted_routing.weight_count
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_compose_cache_hits: {}",
            weighted_routing.compose_cache_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_compose_cache_misses: {}",
            weighted_routing.compose_cache_misses
        );
    }
    let _ = writeln!(out, "  analysis.work_items: {}", analysis.work_items);
    let _ = writeln!(
        out,
        "  analysis.scc_event_batches: {}",
        analysis.scc_event_batches
    );
    let _ = writeln!(out, "  analysis.scc_events: {}", analysis.scc_events);
    let _ = writeln!(
        out,
        "  analysis.scc_open_use_events: {}",
        analysis.scc_open_use_events
    );
    let _ = writeln!(
        out,
        "  analysis.scc_quantify_events: {}",
        analysis.scc_quantify_events
    );
    let _ = writeln!(
        out,
        "  analysis.scc_instantiate_events: {}",
        analysis.scc_instantiate_events
    );
    let _ = writeln!(
        out,
        "  analysis.scc_other_events: {}",
        analysis.scc_other_events
    );
    let _ = writeln!(
        out,
        "  analysis.scc_reachability_calls: {}",
        analysis.scc_reachability_calls
    );
    let _ = writeln!(
        out,
        "  analysis.scc_reachability_nodes_visited: {}",
        analysis.scc_reachability_nodes_visited
    );
    let _ = writeln!(
        out,
        "  analysis.scc_reachability_edges_visited: {}",
        analysis.scc_reachability_edges_visited
    );
    let _ = writeln!(
        out,
        "  analysis.scc_merge_count: {}",
        analysis.scc_merge_count
    );
    let _ = writeln!(
        out,
        "  analysis.scc_merged_component_count: {}",
        analysis.scc_merged_component_count
    );
    let _ = writeln!(
        out,
        "  analysis.scc_rebuilt_edges: {}",
        analysis.scc_rebuilt_edges
    );
    let _ = writeln!(
        out,
        "  analysis.scc_rebuilt_edge_payloads: {}",
        analysis.scc_rebuilt_edge_payloads
    );
    let _ = writeln!(
        out,
        "  analysis.scc_duplicate_dependency_payloads: {}",
        analysis.scc_duplicate_dependency_payloads
    );
    let _ = writeln!(
        out,
        "  analysis.scc_payload_sorts: {}",
        analysis.scc_payload_sorts
    );
    let _ = writeln!(
        out,
        "  analysis.scc_payload_sort_total_len: {}",
        analysis.scc_payload_sort_total_len
    );
    let _ = writeln!(
        out,
        "  analysis.scc_pending_use_scans: {}",
        analysis.scc_pending_use_scans
    );
    let _ = writeln!(
        out,
        "  analysis.scc_pending_use_scan_count: {}",
        analysis.scc_pending_use_scan_count
    );
    let _ = writeln!(
        out,
        "  analysis.scc_ready_component_checks: {}",
        analysis.scc_ready_component_checks
    );
    let _ = writeln!(
        out,
        "  analysis.scc_ready_member_checks: {}",
        analysis.scc_ready_member_checks
    );
    let _ = writeln!(
        out,
        "  analysis.work_resolve_ref_items: {}",
        analysis.work_resolve_ref_items
    );
    let _ = writeln!(
        out,
        "  analysis.work_probe_select_items: {}",
        analysis.work_probe_select_items
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_ref_items: {}",
        analysis.work_apply_ref_items
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select_items: {}",
        analysis.work_apply_select_items
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select_record_field_items: {}",
        analysis.work_apply_select_record_field_items
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select_method_items: {}",
        analysis.work_apply_select_method_items
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select_effect_method_items: {}",
        analysis.work_apply_select_effect_method_items
    );
    let _ = writeln!(
        out,
        "  analysis.work_apply_select_typeclass_method_items: {}",
        analysis.work_apply_select_typeclass_method_items
    );
    let _ = writeln!(
        out,
        "  analysis.work_scc_items: {}",
        analysis.work_scc_items
    );
    let _ = writeln!(out, "  analysis.role_passes: {}", analysis.role_passes);
    let _ = writeln!(
        out,
        "  analysis.progressed_role_passes: {}",
        analysis.progressed_role_passes
    );
    let _ = writeln!(
        out,
        "  analysis.unready_role_dependency_scans: {}",
        analysis.unready_role_dependency_scans
    );
    let _ = writeln!(
        out,
        "  analysis.unready_role_dependency_inputs: {}",
        analysis.unready_role_dependency_inputs
    );
    let _ = writeln!(
        out,
        "  analysis.unready_role_dependency_edges: {}",
        analysis.unready_role_dependency_edges
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_iterations: {}",
        analysis.generalize_iterations
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_merge_restarts: {}",
        analysis.generalize_merge_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_subtype_restarts: {}",
        analysis.generalize_subtype_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_cast_restarts: {}",
        analysis.generalize_cast_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_role_restarts: {}",
        analysis.generalize_role_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_single_def_components: {}",
        analysis.quantify_single_def_components
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_multi_def_components: {}",
        analysis.quantify_multi_def_components
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_max_component_defs: {}",
        analysis.quantify_max_component_defs
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_generalize_roots_with_restarts: {}",
        analysis.quantify_generalize_roots_with_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_generalize_max_iterations_per_root: {}",
        analysis.quantify_generalize_max_iterations_per_root
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_generalize_max_restarts_per_root: {}",
        analysis.quantify_generalize_max_restarts_per_root
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_role_input_constraints: {}",
        analysis.generalize_role_input_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_reachable_role_constraints: {}",
        analysis.generalize_reachable_role_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_coalesced_role_constraints: {}",
        analysis.generalize_coalesced_role_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_dominance_role_constraints: {}",
        analysis.generalize_dominance_role_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_dominance_interval_inputs: {}",
        analysis.generalize_dominance_interval_inputs
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_dominance_polarity_vars: {}",
        analysis.generalize_dominance_polarity_vars
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_dominance_polarity_occurrences: {}",
        analysis.generalize_dominance_polarity_occurrences
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_dominance_subtype_constraints: {}",
        analysis.generalize_dominance_subtype_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_role_resolve_inputs: {}",
        analysis.generalize_role_resolve_inputs
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_root_compact_nodes: {}",
        analysis.generalize_root_compact_nodes
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_root_compact_vars: {}",
        analysis.generalize_root_compact_vars
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_component_unique_compact_vars: {}",
        analysis.generalize_component_unique_compact_vars
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact_iteration_nodes: {}",
        analysis.generalize_compact_iteration_nodes
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact_iteration_vars: {}",
        analysis.generalize_compact_iteration_vars
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_merge_constraints: {}",
        analysis.generalize_merge_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_subtype_constraints: {}",
        analysis.generalize_subtype_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_role_resolutions: {}",
        analysis.generalize_role_resolutions
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_cast_applications: {}",
        analysis.generalize_cast_applications
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_event_runs: {}",
        analysis.instantiate_event_runs
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_max_event_run: {}",
        analysis.instantiate_max_event_run
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_unique_targets: {}",
        analysis.instantiate_unique_targets
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_reused_target_events: {}",
        analysis.instantiate_reused_target_events
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_predicate_var: {}",
        analysis.instantiate_predicate_var
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_predicate_stack: {}",
        analysis.instantiate_predicate_stack
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_predicate_non_subtract: {}",
        analysis.instantiate_predicate_non_subtract
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_predicate_fun: {}",
        analysis.instantiate_predicate_fun
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_predicate_con: {}",
        analysis.instantiate_predicate_con
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_predicate_other: {}",
        analysis.instantiate_predicate_other
    );
    let _ = writeln!(
        out,
        "  analysis.instantiate_direct_lower_predicates: {}",
        analysis.instantiate_direct_lower_predicates
    );
    let _ = writeln!(
        out,
        "  analysis.record_field_selections: {}",
        analysis.record_field_selections
    );
    let _ = writeln!(
        out,
        "  analysis.record_field_constraints: {}",
        analysis.record_field_constraints
    );
    let _ = writeln!(out, "  analysis.max_queue: {}", analysis.max_queue);
    let _ = writeln!(
        out,
        "  lower.finish: {}",
        format_duration(timing.lowering.finish)
    );
    let _ = writeln!(out, "  summarize: {}", format_duration(timing.summarize));
    let _ = writeln!(out, "  total: {}", format_duration(timing.total));
}

fn write_check_hardening_metrics(out: &mut String, timing: &CheckPolyTimings) {
    let analysis = timing.lowering.analysis;
    let constraint = timing.lowering.constraint;
    let edge_count = constraint.lower_bounds_added + constraint.upper_bounds_added;
    let replay_enqueued = constraint.lower_replay_enqueued + constraint.upper_replay_enqueued;
    let replay_accepted = constraint.lower_replay_accepted + constraint.upper_replay_accepted;
    let replay_evidence_only =
        constraint.lower_replay_evidence_only + constraint.upper_replay_evidence_only;
    let replay_duplicate = constraint.lower_replay_duplicate + constraint.upper_replay_duplicate;
    let replay_trivial = constraint.lower_replay_trivial + constraint.upper_replay_trivial;
    let replay_prefiltered =
        constraint.lower_replay_prefiltered + constraint.upper_replay_prefiltered;
    let replay_prefilter_duplicate_exact_key =
        constraint.lower_replay_prefilter_duplicate.exact_key
            + constraint.upper_replay_prefilter_duplicate.exact_key;
    let replay_prefilter_duplicate_var_var_key =
        constraint.lower_replay_prefilter_duplicate.var_var_key
            + constraint.upper_replay_prefilter_duplicate.var_var_key;
    let replay_prefilter_duplicate_terminal_erased = constraint
        .lower_replay_prefilter_duplicate
        .terminal_weight_erased
        + constraint
            .upper_replay_prefilter_duplicate
            .terminal_weight_erased;
    let replay_prefilter_duplicate_row_tail = constraint.lower_replay_prefilter_duplicate.row_tail
        + constraint.upper_replay_prefilter_duplicate.row_tail;
    let max_replay_inputs = constraint
        .max_lower_replay_inputs
        .max(constraint.max_upper_replay_inputs);
    let max_replay_enqueued = constraint
        .max_lower_replay_enqueued
        .max(constraint.max_upper_replay_enqueued);
    let max_replay_accepted = constraint
        .max_lower_replay_accepted
        .max(constraint.max_upper_replay_accepted);
    let max_replay_evidence_only = constraint
        .max_lower_replay_evidence_only
        .max(constraint.max_upper_replay_evidence_only);
    let max_replay_duplicate = constraint
        .max_lower_replay_duplicate
        .max(constraint.max_upper_replay_duplicate);
    let max_replay_trivial = constraint
        .max_lower_replay_trivial
        .max(constraint.max_upper_replay_trivial);
    let max_replay_prefiltered = constraint
        .max_lower_replay_prefiltered
        .max(constraint.max_upper_replay_prefiltered);
    let max_replay_var_var = constraint
        .max_lower_replay_var_var
        .max(constraint.max_upper_replay_var_var);
    let lower_frontier = constraint.replay_frontier_shadow_lower_var_var;
    let upper_frontier = constraint.replay_frontier_shadow_upper_var_var;
    let replay_frontier_shadow_var_var_candidates =
        lower_frontier.candidates + upper_frontier.candidates;
    let replay_frontier_shadow_var_var_hits = lower_frontier.hits + upper_frontier.hits;
    let replay_frontier_shadow_var_var_safe_hits =
        lower_frontier.safe_hits + upper_frontier.safe_hits;
    let replay_frontier_shadow_var_var_unsafe_hits =
        lower_frontier.unsafe_hits + upper_frontier.unsafe_hits;
    let replay_frontier_shadow_var_var_unsafe_accepted =
        lower_frontier.unsafe_accepted + upper_frontier.unsafe_accepted;
    let routing = constraint.replay_routing_shadow_var_var;
    let weighted_routing = constraint.replay_weighted_routing_shadow_var_var;
    let role_demand_count = analysis.generalize_role_input_constraints
        + analysis.generalize_reachable_role_constraints
        + analysis.generalize_coalesced_role_constraints
        + analysis.generalize_dominance_role_constraints;
    let top_restart_root = analysis
        .generalize_top_restart_root
        .map(|root| root.0.to_string())
        .unwrap_or_else(|| "none".to_string());

    let _ = writeln!(out, "  infer.type_var_count: {}", constraint.type_var_count);
    let _ = writeln!(out, "  constraint.epoch: {}", constraint.epoch);
    let _ = writeln!(
        out,
        "  infer.row_tail_var_count: {}",
        constraint.row_tail_var_count
    );
    let _ = writeln!(
        out,
        "  infer.type_node_count: {}",
        constraint.type_node_count
    );
    let _ = writeln!(out, "  infer.pos_node_count: {}", constraint.pos_node_count);
    let _ = writeln!(out, "  infer.neg_node_count: {}", constraint.neg_node_count);
    let _ = writeln!(out, "  infer.neu_node_count: {}", constraint.neu_node_count);
    let _ = writeln!(out, "  constraint.edge_count: {edge_count}");
    let _ = writeln!(out, "  constraint.replay_generated: {replay_enqueued}");
    let _ = writeln!(out, "  constraint.replay_enqueued: {replay_enqueued}");
    let _ = writeln!(out, "  constraint.replay_accepted: {replay_accepted}");
    let _ = writeln!(
        out,
        "  constraint.replay_evidence_only: {replay_evidence_only}"
    );
    let _ = writeln!(out, "  constraint.replay_duplicate: {replay_duplicate}");
    let _ = writeln!(out, "  constraint.replay_trivial: {replay_trivial}");
    let _ = writeln!(out, "  constraint.replay_prefiltered: {replay_prefiltered}");
    let _ = writeln!(
        out,
        "  constraint.replay_prefilter_duplicate_exact_key: {replay_prefilter_duplicate_exact_key}"
    );
    let _ = writeln!(
        out,
        "  constraint.replay_prefilter_duplicate_var_var_key: {replay_prefilter_duplicate_var_var_key}"
    );
    let _ = writeln!(
        out,
        "  constraint.replay_prefilter_duplicate_terminal_erased: {replay_prefilter_duplicate_terminal_erased}"
    );
    let _ = writeln!(
        out,
        "  constraint.replay_prefilter_duplicate_row_tail: {replay_prefilter_duplicate_row_tail}"
    );
    let _ = writeln!(out, "  constraint.max_replay_inputs: {max_replay_inputs}");
    let _ = writeln!(
        out,
        "  constraint.max_replay_generated: {max_replay_enqueued}"
    );
    let _ = writeln!(
        out,
        "  constraint.max_replay_enqueued: {max_replay_enqueued}"
    );
    let _ = writeln!(
        out,
        "  constraint.max_replay_accepted: {max_replay_accepted}"
    );
    let _ = writeln!(
        out,
        "  constraint.max_replay_evidence_only: {max_replay_evidence_only}"
    );
    let _ = writeln!(
        out,
        "  constraint.max_replay_duplicate: {max_replay_duplicate}"
    );
    let _ = writeln!(out, "  constraint.max_replay_trivial: {max_replay_trivial}");
    let _ = writeln!(
        out,
        "  constraint.max_replay_prefiltered: {max_replay_prefiltered}"
    );
    let _ = writeln!(out, "  constraint.max_replay_var_var: {max_replay_var_var}");
    if replay_frontier_shadow_var_var_candidates > 0 {
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_var_var_candidates: {replay_frontier_shadow_var_var_candidates}"
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_var_var_hits: {replay_frontier_shadow_var_var_hits}"
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_var_var_safe_hits: {replay_frontier_shadow_var_var_safe_hits}"
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_var_var_unsafe_hits: {replay_frontier_shadow_var_var_unsafe_hits}"
        );
        let _ = writeln!(
            out,
            "  constraint.replay_frontier_shadow_var_var_unsafe_accepted: {replay_frontier_shadow_var_var_unsafe_accepted}"
        );
    }
    if routing.accepted_edges > 0 {
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_accepted_edges: {}",
            routing.accepted_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_repeated_endpoint_edges: {}",
            routing.repeated_endpoint_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_reachable_before_edges: {}",
            routing.reachable_before_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_graph_nodes: {}",
            routing.graph_nodes
        );
        let _ = writeln!(
            out,
            "  constraint.replay_routing_shadow_var_var_graph_edges: {}",
            routing.graph_edges
        );
    }
    if weighted_routing.accepted_edges > 0 {
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_accepted_edges: {}",
            weighted_routing.accepted_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_reachable_before_edges: {}",
            weighted_routing.reachable_before_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_capped_searches: {}",
            weighted_routing.capped_searches
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_search_states: {}",
            weighted_routing.search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_max_search_states: {}",
            weighted_routing.max_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_inserted_edges: {}",
            weighted_routing.frontier_inserted_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_skipped_edges: {}",
            weighted_routing.frontier_skipped_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_capped_searches: {}",
            weighted_routing.frontier_capped_searches
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_search_states: {}",
            weighted_routing.frontier_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_max_search_states: {}",
            weighted_routing.frontier_max_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_queries: {}",
            weighted_routing.consequence_queries
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_known: {}",
            weighted_routing.consequence_known
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_known_unseen: {}",
            weighted_routing.consequence_known_unseen
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_unknown: {}",
            weighted_routing.consequence_unknown
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_unknown_seen: {}",
            weighted_routing.consequence_unknown_seen
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_capped_searches: {}",
            weighted_routing.consequence_capped_searches
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_search_states: {}",
            weighted_routing.consequence_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_max_search_states: {}",
            weighted_routing.consequence_max_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_known: {}",
            weighted_routing.consequence_frontier_known
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_known_unseen: {}",
            weighted_routing.consequence_frontier_known_unseen
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_unknown: {}",
            weighted_routing.consequence_frontier_unknown
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_unknown_seen: {}",
            weighted_routing.consequence_frontier_unknown_seen
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_capped_searches: {}",
            weighted_routing.consequence_frontier_capped_searches
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_search_states: {}",
            weighted_routing.consequence_frontier_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_max_search_states: {}",
            weighted_routing.consequence_frontier_max_search_states
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_graph_nodes: {}",
            weighted_routing.graph_nodes
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_graph_edges: {}",
            weighted_routing.graph_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_graph_nodes: {}",
            weighted_routing.frontier_graph_nodes
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_graph_edges: {}",
            weighted_routing.frontier_graph_edges
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_route_cache_hits: {}",
            weighted_routing.route_cache_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_route_cache_hits: {}",
            weighted_routing.frontier_route_cache_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_route_cache_entries: {}",
            weighted_routing.route_cache_entries
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_frontier_route_cache_entries: {}",
            weighted_routing.frontier_route_cache_entries
        );
        if weighted_routing.summary_observed_edges > 0 {
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_observed_edges: {}",
                weighted_routing.summary_observed_edges
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_known_edges: {}",
                weighted_routing.summary_known_edges
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_new_edges: {}",
                weighted_routing.summary_new_edges
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_inserted_paths: {}",
                weighted_routing.summary_inserted_paths
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_duplicate_paths: {}",
                weighted_routing.summary_duplicate_paths
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_capped_insertions: {}",
                weighted_routing.summary_capped_insertions
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_max_queue: {}",
                weighted_routing.summary_max_queue
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_paths: {}",
                weighted_routing.summary_paths
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_outgoing_nodes: {}",
                weighted_routing.summary_outgoing_nodes
            );
            let _ = writeln!(
                out,
                "  constraint.replay_weighted_routing_shadow_var_var_summary_incoming_nodes: {}",
                weighted_routing.summary_incoming_nodes
            );
        }
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_weight_count: {}",
            weighted_routing.weight_count
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_compose_cache_hits: {}",
            weighted_routing.compose_cache_hits
        );
        let _ = writeln!(
            out,
            "  constraint.replay_weighted_routing_shadow_var_var_compose_cache_misses: {}",
            weighted_routing.compose_cache_misses
        );
    }
    let _ = writeln!(
        out,
        "  analysis.scc_component_count: {}",
        analysis.quantified_components
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_max_component_defs: {}",
        analysis.quantify_max_component_defs
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_generalize_roots_with_restarts: {}",
        analysis.quantify_generalize_roots_with_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_generalize_max_iterations_per_root: {}",
        analysis.quantify_generalize_max_iterations_per_root
    );
    let _ = writeln!(
        out,
        "  analysis.quantify_generalize_max_restarts_per_root: {}",
        analysis.quantify_generalize_max_restarts_per_root
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_root: {top_restart_root}"
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_iterations: {}",
        analysis.generalize_top_restart_iterations
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_constraint_epoch_start: {}",
        analysis.generalize_top_restart_constraint_epoch_start
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_constraint_epoch_end: {}",
        analysis.generalize_top_restart_constraint_epoch_end
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_constraint_epoch_delta: {}",
        analysis.generalize_top_restart_constraint_epoch_delta
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_role_epoch_start: {}",
        analysis.generalize_top_restart_role_epoch_start
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_role_epoch_end: {}",
        analysis.generalize_top_restart_role_epoch_end
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_role_epoch_delta: {}",
        analysis.generalize_top_restart_role_epoch_delta
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_total_restarts: {}",
        analysis.generalize_top_restart_total_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_merge_restarts: {}",
        analysis.generalize_top_restart_merge_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_subtype_restarts: {}",
        analysis.generalize_top_restart_subtype_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_cast_restarts: {}",
        analysis.generalize_top_restart_cast_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_role_restarts: {}",
        analysis.generalize_top_restart_role_restarts
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_first_compact_nodes: {}",
        analysis.generalize_top_restart_first_compact_nodes
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_first_compact_vars: {}",
        analysis.generalize_top_restart_first_compact_vars
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_compact_iteration_nodes: {}",
        analysis.generalize_top_restart_compact_iteration_nodes
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_compact_iteration_vars: {}",
        analysis.generalize_top_restart_compact_iteration_vars
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_role_input_constraints: {}",
        analysis.generalize_top_restart_role_input_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_reachable_role_constraints: {}",
        analysis.generalize_top_restart_reachable_role_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_coalesced_role_constraints: {}",
        analysis.generalize_top_restart_coalesced_role_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_dominance_role_constraints: {}",
        analysis.generalize_top_restart_dominance_role_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_dominance_interval_inputs: {}",
        analysis.generalize_top_restart_dominance_interval_inputs
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_dominance_polarity_vars: {}",
        analysis.generalize_top_restart_dominance_polarity_vars
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_dominance_polarity_occurrences: {}",
        analysis.generalize_top_restart_dominance_polarity_occurrences
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_dominance_subtype_constraints: {}",
        analysis.generalize_top_restart_dominance_subtype_constraints
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_role_resolve_inputs: {}",
        analysis.generalize_top_restart_role_resolve_inputs
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_top_restart_role_resolutions: {}",
        analysis.generalize_top_restart_role_resolutions
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact_shadow_requests: {}",
        analysis.generalize_compact_shadow_requests
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact_shadow_hits: {}",
        analysis.generalize_compact_shadow_hits
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact_shadow_misses: {}",
        analysis.generalize_compact_shadow_misses
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact_cache_requests: {}",
        analysis.generalize_compact_cache_requests
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact_cache_hits: {}",
        analysis.generalize_compact_cache_hits
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact_cache_misses: {}",
        analysis.generalize_compact_cache_misses
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_compact_cache_inserts: {}",
        analysis.generalize_compact_cache_inserts
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_role_view_shadow_requests: {}",
        analysis.generalize_role_view_shadow_requests
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_role_view_shadow_hits: {}",
        analysis.generalize_role_view_shadow_hits
    );
    let _ = writeln!(
        out,
        "  analysis.generalize_role_view_shadow_misses: {}",
        analysis.generalize_role_view_shadow_misses
    );
    let _ = writeln!(out, "  analysis.role_demand_count: {role_demand_count}");
    let _ = writeln!(
        out,
        "  analysis.role_resolve_demands: {}",
        analysis.role_resolve_demands
    );
    let _ = writeln!(
        out,
        "  analysis.role_resolve_candidate_scans: {}",
        analysis.role_resolve_candidate_scans
    );
    let _ = writeln!(
        out,
        "  analysis.role_resolve_candidate_matches: {}",
        analysis.role_resolve_candidate_matches
    );
    let _ = writeln!(
        out,
        "  analysis.role_resolve_ambiguous_demands: {}",
        analysis.role_resolve_ambiguous_demands
    );
    let _ = writeln!(
        out,
        "  analysis.role_resolve_already_applied: {}",
        analysis.role_resolve_already_applied
    );
    let _ = writeln!(
        out,
        "  analysis.role_resolve_prerequisite_demands: {}",
        analysis.role_resolve_prerequisite_demands
    );
    let _ = writeln!(
        out,
        "  analysis.role_resolve_prerequisite_candidate_scans: {}",
        analysis.role_resolve_prerequisite_candidate_scans
    );
    let _ = writeln!(
        out,
        "  analysis.role_resolve_prerequisite_candidate_matches: {}",
        analysis.role_resolve_prerequisite_candidate_matches
    );
    let _ = writeln!(
        out,
        "  analysis.role_resolve_candidate_cache_hits: {}",
        analysis.role_resolve_candidate_cache_hits
    );
    let _ = writeln!(
        out,
        "  analysis.role_resolve_candidate_cache_misses: {}",
        analysis.role_resolve_candidate_cache_misses
    );
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
        infer::lowering::BodyLoweringError::MissingBindingDecl { name } => {
            format!(
                "binding `{}` is declared but was not available during lowering",
                name.0
            )
        }
        infer::lowering::BodyLoweringError::MissingModuleDecl { name } => {
            format!(
                "module `{}` is declared but was not available during lowering",
                name.0
            )
        }
        infer::lowering::BodyLoweringError::MissingBody { name, .. } => {
            format!("binding `{}` is missing a body expression", name.0)
        }
        infer::lowering::BodyLoweringError::NonLetDef { name, .. } => {
            format!("definition `{}` is not a value binding", name.0)
        }
        infer::lowering::BodyLoweringError::Expr { error, .. } => format_lowering_error(error),
        infer::lowering::BodyLoweringError::RootExpr {
            error: infer::lowering::LoweringError::UnresolvedName { name, .. },
        } => format!("unresolved value name in root expression: {}", name.0),
        infer::lowering::BodyLoweringError::RootExpr { error } => format_lowering_error(error),
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
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::EffectFilterViolation { effect, filter },
        ) => {
            let effect = effect
                .as_ref()
                .map(|path| path.join("::"))
                .unwrap_or_else(|| "<unknown effect>".to_string());
            format!(
                "effect filter mismatch: {effect} is not allowed by {}",
                format_subtractability(filter)
            )
        }
    }
}

fn format_lowering_error(error: &infer::lowering::LoweringError) -> String {
    match error {
        infer::lowering::LoweringError::UnsupportedSyntax { kind } => {
            format!("unsupported expression syntax: {kind:?}")
        }
        infer::lowering::LoweringError::UnsupportedPatternSyntax { kind } => {
            format!("unsupported pattern syntax: {kind:?}")
        }
        infer::lowering::LoweringError::UnsupportedRuleLazyQuantifier { kind, .. } => {
            let quantifier = match kind {
                parser::lex::SyntaxKind::RuleQuantStarLazy => "*?",
                parser::lex::SyntaxKind::RuleQuantPlusLazy => "+?",
                _ => "lazy quantifier",
            };
            format!(
                "rule lazy quantifier `{quantifier}` is not supported; rule uses PEG-style greedy repetition"
            )
        }
        infer::lowering::LoweringError::UnresolvedName { name, .. } => {
            format!("unresolved value name: {}", name.0)
        }
        infer::lowering::LoweringError::InvalidNumber { text } => {
            format!("invalid number literal `{text}`")
        }
        infer::lowering::LoweringError::MissingLambdaBody => {
            "lambda expression is missing a body expression".to_string()
        }
        infer::lowering::LoweringError::MissingIfCondition => {
            "if expression is missing a condition".to_string()
        }
        infer::lowering::LoweringError::MissingIfBody => {
            "if expression is missing a body expression".to_string()
        }
        infer::lowering::LoweringError::MissingCaseScrutinee => {
            "case expression is missing the value to inspect".to_string()
        }
        infer::lowering::LoweringError::MissingCaseArmPattern => {
            "case arm is missing a pattern".to_string()
        }
        infer::lowering::LoweringError::MissingCaseArmBody => {
            "case arm is missing a body expression".to_string()
        }
        infer::lowering::LoweringError::MissingCatchScrutinee { .. } => {
            "catch expression is missing the computation to handle".to_string()
        }
        infer::lowering::LoweringError::MissingCatchArmPattern { .. } => {
            "catch arm is missing a value pattern or effect operation".to_string()
        }
        infer::lowering::LoweringError::MissingCatchArmBody { .. } => {
            "catch arm is missing a body expression".to_string()
        }
        infer::lowering::LoweringError::MissingFieldName => {
            "field access is missing a field name".to_string()
        }
        infer::lowering::LoweringError::MissingOpName => {
            "effect operation is missing an operation name".to_string()
        }
        infer::lowering::LoweringError::MissingOpOperand => {
            "effect operation is missing an operand".to_string()
        }
        infer::lowering::LoweringError::MissingRecordFieldName => {
            "record field is missing a name".to_string()
        }
        infer::lowering::LoweringError::MissingRecordFieldValue => {
            "record field is missing a value expression".to_string()
        }
        infer::lowering::LoweringError::MissingIndexArgument => {
            "index expression is missing an argument".to_string()
        }
        infer::lowering::LoweringError::MissingLocalBindingName => {
            "local binding is missing a name".to_string()
        }
        infer::lowering::LoweringError::MissingLocalBindingBody => {
            "local binding is missing a body expression".to_string()
        }
        infer::lowering::LoweringError::UnsupportedTopLevelVarBinding { name, .. } => format!(
            "top-level mutable binding {} is not supported; move it into a block or function body",
            name.0
        ),
        infer::lowering::LoweringError::MissingLocalVarAct { name } => {
            format!(
                "mutable binding `{}` is missing its variable effect body",
                name.0
            )
        }
        infer::lowering::LoweringError::MissingSubLabelAct { label } => {
            format!("labeled sub `{}` is missing its effect body", label.0)
        }
        infer::lowering::LoweringError::AnnotationBuild { error, .. } => {
            format_annotation_build_error(error)
        }
        infer::lowering::LoweringError::AnnotationConstraint { error } => {
            format_annotation_constraint_error(error)
        }
        infer::lowering::LoweringError::NegSignatureBuild { error } => {
            format_neg_signature_build_error(error)
        }
        infer::lowering::LoweringError::SignatureConstraint { error } => {
            format_signature_constraint_error(error)
        }
        infer::lowering::LoweringError::SignatureShapeMismatch { expected } => {
            format!(
                "signature shape mismatch: expected {}",
                format_signature_shape(*expected)
            )
        }
        infer::lowering::LoweringError::SignatureTypeMismatch { expected } => {
            format!(
                "signature type mismatch: expected {}",
                format_signature_shape(*expected)
            )
        }
        infer::lowering::LoweringError::TypeMismatch {
            actual, expected, ..
        } => {
            format!("type mismatch: {actual} is not {expected}")
        }
    }
}

fn format_annotation_build_error(error: &infer::annotation::AnnBuildError) -> String {
    match error {
        infer::annotation::AnnBuildError::ExpectedTypeExpr { kind } => {
            format!("expected type expression, found {kind:?}")
        }
        infer::annotation::AnnBuildError::EmptyTypeExpr => "expected type expression".to_string(),
        infer::annotation::AnnBuildError::EmptyEffectfulType => {
            "expected effectful type".to_string()
        }
        infer::annotation::AnnBuildError::MissingFunctionReturn => {
            "function type annotation is missing a return type".to_string()
        }
        infer::annotation::AnnBuildError::MissingEffectRow => {
            "effectful type annotation is missing an effect row".to_string()
        }
        infer::annotation::AnnBuildError::InvalidEffectRowTail { .. } => {
            "effect row tail must be a row variable".to_string()
        }
        infer::annotation::AnnBuildError::UnresolvedTypeName { path } => {
            format!("unresolved type name: {}", format_name_path(path))
        }
        infer::annotation::AnnBuildError::UnsupportedSyntax { kind } => {
            format!("unsupported type annotation syntax: {kind:?}")
        }
    }
}

fn format_neg_signature_build_error(error: &infer::lowering::NegSignatureBuildError) -> String {
    match error {
        infer::lowering::NegSignatureBuildError::ExpectedTypeExpr { kind } => {
            format!("expected type expression in signature, found {kind:?}")
        }
        infer::lowering::NegSignatureBuildError::EmptyTypeExpr => {
            "expected type expression in signature".to_string()
        }
        infer::lowering::NegSignatureBuildError::EmptyEffectfulType => {
            "expected effectful type in signature".to_string()
        }
        infer::lowering::NegSignatureBuildError::MissingFunctionReturn => {
            "function signature is missing a return type".to_string()
        }
        infer::lowering::NegSignatureBuildError::MissingEffectRow => {
            "effectful signature is missing an effect row".to_string()
        }
        infer::lowering::NegSignatureBuildError::InvalidEffectRowTail { .. } => {
            "effect row tail in signature must be a row variable".to_string()
        }
        infer::lowering::NegSignatureBuildError::UnresolvedTypeName { path } => {
            format!("unresolved type name: {}", format_name_path(path))
        }
        infer::lowering::NegSignatureBuildError::UnsupportedSyntax { kind } => {
            format!("unsupported signature syntax: {kind:?}")
        }
    }
}

fn format_annotation_constraint_error(error: &infer::annotation::AnnConstraintError) -> String {
    match error {
        infer::annotation::AnnConstraintError::MissingTypeDecl { .. } => {
            "type annotation references a type declaration that is not available".to_string()
        }
        infer::annotation::AnnConstraintError::InvalidConstructorCallee { .. } => {
            "type annotation applies a value that is not a type constructor".to_string()
        }
        infer::annotation::AnnConstraintError::InvalidEffectAtom { .. } => {
            "effect row contains an item that is not an effect".to_string()
        }
        infer::annotation::AnnConstraintError::WildcardEffectRowInTypePosition => {
            "wildcard effect row cannot appear in type position".to_string()
        }
    }
}

fn format_signature_constraint_error(error: &infer::lowering::SignatureConstraintError) -> String {
    match error {
        infer::lowering::SignatureConstraintError::MissingTypeDecl { .. } => {
            "signature references a type declaration that is not available".to_string()
        }
        infer::lowering::SignatureConstraintError::InvalidConstructorCallee { .. } => {
            "signature applies a value that is not a type constructor".to_string()
        }
        infer::lowering::SignatureConstraintError::WildcardEffectRowInTypePosition => {
            "wildcard effect row cannot appear in signature type position".to_string()
        }
    }
}

fn format_signature_shape(shape: infer::lowering::SignatureShape) -> &'static str {
    match shape {
        infer::lowering::SignatureShape::Any => "any signature shape",
        infer::lowering::SignatureShape::Constructor => "a type constructor",
        infer::lowering::SignatureShape::EffectRow => "an effect row",
        infer::lowering::SignatureShape::Function => "a function type",
        infer::lowering::SignatureShape::Tuple => "a tuple type",
    }
}

fn format_subtractability(subtractability: &poly::types::Subtractability) -> String {
    use poly::types::Subtractability;
    match subtractability {
        Subtractability::Empty => "[]".to_string(),
        Subtractability::All => "[_]".to_string(),
        Subtractability::Set(path, _) => format!("[{}]", path.join("::")),
        Subtractability::SetMany(families) => format!(
            "[{}]",
            families
                .iter()
                .map(|(path, _)| path.join("::"))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Subtractability::AllExcept(path, _) => format!("[_; without {}]", path.join("::")),
        Subtractability::AllExceptMany(families) => format!(
            "[_; without {}]",
            families
                .iter()
                .map(|(path, _)| path.join("::"))
                .collect::<Vec<_>>()
                .join(", ")
        ),
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
