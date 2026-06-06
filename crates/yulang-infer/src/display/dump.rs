use std::collections::{HashMap, HashSet};

use yulang_typed_ir as typed_ir;

use crate::diagnostic::{ExpectedEdge, ExpectedEdgeKind};
use crate::display::format as display_format;
use crate::ids::{NegId, PosId, TypeVar};
use crate::lower::LowerState;
use crate::scheme::FrozenScheme;
use crate::simplify::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRow, CompactType,
    CompactTypeScheme, CompactVariant, compact_type_var,
};
use crate::simplify::cooccur::CompactRoleConstraint;
use crate::solve::{EffectSubtractability, Infer, RoleConstraint};
use crate::symbols::{ModuleId, Name, Path, Visibility};
use crate::types::{EffectAtom, Neg, Pos};

// ── エントリポイント ──────────────────────────────────────────────────────────

pub fn render_compact_results(state: &mut LowerState) -> Vec<(String, String)> {
    let paths = collect_user_observable_binding_paths(state);
    finalize_compact_results_for_paths(state, &paths);
    collect_compact_results_for_paths(state, &paths)
}

pub fn render_exported_compact_results(state: &mut LowerState) -> Vec<(String, String)> {
    let paths = collect_non_std_exported_binding_paths(state);
    finalize_compact_results_for_paths(state, &paths);
    collect_compact_results_for_paths(state, &paths)
}

pub fn render_exported_compact_results_in_scope(state: &mut LowerState) -> Vec<(String, String)> {
    let paths = collect_non_std_exported_binding_paths(state);
    finalize_compact_results_for_paths(state, &paths);
    collect_compact_results_for_paths_in_scope(state, &paths, &state.ctx)
}

fn finalize_compact_results_for_paths(state: &mut LowerState, paths: &[(Path, crate::ids::DefId)]) {
    let target_defs = paths.iter().map(|(_, def)| *def).collect::<HashSet<_>>();
    state.finalize_compact_results_for_defs(&target_defs);
    state.infer.prune_resolved_effect_subtract_metadata();
}

pub(crate) fn format_pos_for_diagnostic(infer: &Infer, pos: PosId) -> String {
    let mut namer = VarNamer::default();
    format_pos_id(infer, pos, &mut namer, false)
}

pub(crate) fn format_neg_for_diagnostic(infer: &Infer, neg: NegId) -> String {
    let mut namer = VarNamer::default();
    format_neg_id(infer, neg, &mut namer, false)
}

pub fn collect_compact_results(state: &LowerState) -> Vec<(String, String)> {
    collect_compact_results_for_paths(state, &collect_user_observable_binding_paths(state))
}

pub fn collect_expected_edges(state: &LowerState) -> Vec<String> {
    let mut cache = ExpectedEdgeFormatCache::default();
    state
        .expected_edges
        .iter()
        .map(|edge| format_expected_edge(state, edge, &mut cache))
        .collect()
}

pub fn collect_compact_results_for_paths(
    state: &LowerState,
    paths: &[(Path, crate::ids::DefId)],
) -> Vec<(String, String)> {
    collect_compact_results_for_paths_impl(state, paths, None)
}

pub fn collect_compact_results_for_paths_in_scope(
    state: &LowerState,
    paths: &[(Path, crate::ids::DefId)],
    scope: &crate::lower::ctx::LowerCtx,
) -> Vec<(String, String)> {
    collect_compact_results_for_paths_impl(state, paths, Some(scope))
}

fn collect_compact_results_for_paths_impl(
    state: &LowerState,
    paths: &[(Path, crate::ids::DefId)],
    scope: Option<&crate::lower::ctx::LowerCtx>,
) -> Vec<(String, String)> {
    let mut seen = HashSet::new();
    let hidden_effect_paths = hidden_effect_paths_for_display(state);
    let mut entries = paths
        .into_iter()
        .filter(|(_, def)| seen.insert(*def))
        .filter_map(|(path, def)| {
            let label = render_label_path(path, scope, *def);
            if let Some(scheme) = state.runtime_export_schemes.get(def) {
                return Some((label, format_runtime_export_scheme(scheme)));
            }
            if let Some(&pos_sig) = state.effect_op_pos_sigs.get(def) {
                let scheme = crate::scheme::freeze_pos_scheme(&state.infer, pos_sig);
                let constraints = state.infer.role_constraints_of(*def);
                return Some((
                    label,
                    format_frozen_scheme_with_role_constraints(&state.infer, &scheme, &constraints),
                ));
            }
            if let Some(scheme) = state.compact_scheme_of(*def) {
                let constraints = state.infer.compact_role_constraints_of(*def);
                return Some((
                    label,
                    format_coalesced_scheme_with_role_constraints_optional_scope(
                        &state.infer,
                        &scheme,
                        &constraints,
                        scope,
                        &hidden_effect_paths,
                    ),
                ));
            }

            let frozen = state.infer.frozen_schemes.borrow();
            let scheme = frozen.get(def)?;
            let constraints = state.infer.role_constraints_of(*def);
            Some((
                label,
                format_frozen_scheme_with_role_constraints(&state.infer, scheme, &constraints),
            ))
        })
        .collect::<Vec<_>>();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries
}

fn hidden_effect_paths_for_display(state: &LowerState) -> HashSet<Path> {
    state
        .effect_arities
        .keys()
        .filter(|path| {
            absolute_type_path_visibility(&state.ctx, path)
                .is_some_and(|visibility| matches!(visibility, Visibility::My))
        })
        .cloned()
        .collect()
}

fn absolute_type_path_visibility(
    ctx: &crate::lower::ctx::LowerCtx,
    path: &Path,
) -> Option<Visibility> {
    let (last, module_segments) = path.segments.split_last()?;
    for root in ctx.modules.module_ids() {
        if ctx.modules.node(root).parent.is_some() {
            continue;
        }
        let Some(module) = absolute_module_path_from(ctx, root, module_segments) else {
            continue;
        };
        if ctx.modules.node(module).types.contains_key(last) {
            return Some(ctx.modules.type_visibility(module, last));
        }
    }
    None
}

fn absolute_module_path_from(
    ctx: &crate::lower::ctx::LowerCtx,
    root: ModuleId,
    segments: &[Name],
) -> Option<ModuleId> {
    let mut module = root;
    for segment in segments {
        module = *ctx.modules.node(module).modules.get(segment)?;
    }
    Some(module)
}

fn render_label_path(
    path: &Path,
    scope: Option<&crate::lower::ctx::LowerCtx>,
    def: crate::ids::DefId,
) -> String {
    match scope {
        Some(ctx) => shortest_unique_value_label(ctx, path, def),
        None => path_string(path),
    }
}

fn shortest_unique_value_label(
    ctx: &crate::lower::ctx::LowerCtx,
    full_path: &Path,
    def: crate::ids::DefId,
) -> String {
    if full_path.segments.is_empty() {
        return path_string(full_path);
    }
    let module = ctx.current_module;
    let fixity = ctx.operator_fixity(def);
    let total = full_path.segments.len();
    for k in 1..total {
        let suffix_segments = full_path.segments[total - k..].to_vec();
        let lookup_path = Path {
            segments: lookup_segments_for_operator(suffix_segments.clone(), fixity),
        };
        let candidates = if let Some(fixity) = fixity {
            ctx.resolve_path_operator_value_candidates_via_snapshot(module, &lookup_path, fixity)
        } else {
            ctx.resolve_path_value_candidates_via_snapshot(module, &lookup_path)
        };
        if candidates.as_slice() == [def] {
            return path_string(&lookup_path);
        }
    }
    let display = Path {
        segments: lookup_segments_for_operator(full_path.segments.clone(), fixity),
    };
    path_string(&display)
}

/// `#op:fixity:NAME` 形式の合成 operator binding 名を、生の operator 名へ戻す。
/// fixity が指定されていて、leaf が合成名なら剥がす。
fn lookup_segments_for_operator(
    mut segments: Vec<crate::symbols::Name>,
    fixity: Option<crate::symbols::OperatorFixity>,
) -> Vec<crate::symbols::Name> {
    if fixity.is_none() {
        return segments;
    }
    if let Some(last) = segments.last_mut() {
        if let Some(stripped) = strip_synthetic_operator_name(&last.0) {
            *last = crate::symbols::Name(stripped.to_string());
        }
    }
    segments
}

fn strip_synthetic_operator_name(text: &str) -> Option<&str> {
    let rest = text.strip_prefix("#op:")?;
    let (_fixity, name) = rest.split_once(':')?;
    Some(name)
}

fn collect_user_observable_binding_paths(state: &LowerState) -> Vec<(Path, crate::ids::DefId)> {
    let canonical = crate::export::paths::collect_canonical_binding_paths(state);
    state
        .ctx
        .collect_observable_binding_paths()
        .into_iter()
        .filter(|(_, def)| {
            canonical
                .get(def)
                .and_then(|path| path.segments.first().cloned())
                .or_else(|| {
                    state
                        .ctx
                        .collect_all_binding_paths()
                        .into_iter()
                        .find_map(|(path, current)| (current == *def).then_some(path))
                        .and_then(|path| path.segments.first().cloned())
                })
                .map(|name| name.0.as_str() != "std")
                .unwrap_or(true)
        })
        .collect()
}

fn collect_non_std_exported_binding_paths(state: &LowerState) -> Vec<(Path, crate::ids::DefId)> {
    let canonical = crate::export::paths::collect_canonical_binding_paths(state);
    state
        .ctx
        .collect_exported_binding_paths()
        .into_iter()
        .filter(|(_, def)| {
            canonical
                .get(def)
                .and_then(|path| path.segments.first().cloned())
                .or_else(|| {
                    state
                        .ctx
                        .collect_all_binding_paths()
                        .into_iter()
                        .find_map(|(path, current)| (current == *def).then_some(path))
                        .and_then(|path| path.segments.first().cloned())
                })
                .map(|name| name.0.as_str() != "std")
                .unwrap_or(true)
        })
        .collect()
}

pub(crate) fn format_runtime_export_scheme(scheme: &typed_ir::Scheme) -> String {
    let body = format_core_type(&scheme.body);
    if scheme.requirements.is_empty() {
        return body;
    }
    let requirements = scheme
        .requirements
        .iter()
        .map(format_core_role_requirement)
        .collect::<Vec<_>>()
        .join(", ");
    format!("{requirements} => {body}")
}

fn format_core_role_requirement(requirement: &typed_ir::RoleRequirement) -> String {
    let args = requirement
        .args
        .iter()
        .map(|arg| match arg {
            typed_ir::RoleRequirementArg::Input(bounds) => format_core_bounds(bounds),
            typed_ir::RoleRequirementArg::Associated { name, bounds } => {
                format!("{} = {}", name.0, format_core_bounds(bounds))
            }
        })
        .collect::<Vec<_>>();
    if args.is_empty() {
        return format_core_path(&requirement.role);
    }
    format!(
        "{}<{}>",
        format_core_path(&requirement.role),
        args.join(", ")
    )
}

fn format_core_bounds(bounds: &typed_ir::TypeBounds) -> String {
    match (&bounds.lower, &bounds.upper) {
        (Some(lower), Some(upper)) if lower == upper => format_core_type(lower),
        (Some(lower), Some(upper)) => {
            format!("{} | {}", format_core_type(lower), format_core_type(upper))
        }
        (Some(lower), None) => format_core_type(lower),
        (None, Some(upper)) => format_core_type(upper),
        (None, None) => "⊤".to_string(),
    }
}

fn format_core_type(ty: &typed_ir::Type) -> String {
    match ty {
        typed_ir::Type::Unknown => "?".to_string(),
        typed_ir::Type::Never => "⊥".to_string(),
        typed_ir::Type::Any => "⊤".to_string(),
        typed_ir::Type::Var(tv) => tv.0.clone(),
        typed_ir::Type::Named { path, args } => {
            let name = format_core_path(path);
            if args.is_empty() {
                return name;
            }
            let args = args
                .iter()
                .map(|arg| match arg {
                    typed_ir::TypeArg::Type(ty) => format_core_type(ty),
                    typed_ir::TypeArg::Bounds(bounds) => format_core_bounds(bounds),
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name}<{args}>")
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            let param_text = format_core_type(param);
            let param_effect_text = format_core_type(param_effect);
            let ret_effect_text = format_core_type(ret_effect);
            let ret_text = format_core_type(ret);
            if matches!(&**param_effect, typed_ir::Type::Never | typed_ir::Type::Any)
                && matches!(&**ret_effect, typed_ir::Type::Never | typed_ir::Type::Any)
            {
                format!("{param_text} -> {ret_text}")
            } else {
                format!("{param_text} [{param_effect_text}] -> [{ret_effect_text}] {ret_text}")
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
        typed_ir::Type::Record(record) => {
            let fields = record
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
                .collect::<Vec<_>>()
                .join(", ");
            match &record.spread {
                None => format!("{{{fields}}}"),
                Some(typed_ir::RecordSpread::Head(tail)) => {
                    let mut parts = vec![format!("..{}", format_core_type(tail))];
                    if !fields.is_empty() {
                        parts.push(fields);
                    }
                    format!("{{{}}}", parts.join(", "))
                }
                Some(typed_ir::RecordSpread::Tail(tail)) => {
                    let mut parts = Vec::new();
                    if !fields.is_empty() {
                        parts.push(fields);
                    }
                    parts.push(format!("..{}", format_core_type(tail)));
                    format!("{{{}}}", parts.join(", "))
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            let cases = variant
                .cases
                .iter()
                .map(|case| {
                    if case.payloads.is_empty() {
                        case.name.0.clone()
                    } else if case.payloads.len() == 1 {
                        format!("{} {}", case.name.0, format_core_type(&case.payloads[0]))
                    } else {
                        let payloads = case
                            .payloads
                            .iter()
                            .map(format_core_type)
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("{} ({payloads})", case.name.0)
                    }
                })
                .collect::<Vec<_>>();
            let mut items = cases;
            if let Some(tail) = &variant.tail {
                items.push(format!("..{}", format_core_type(tail)));
            }
            format!(":{{{}}}", items.join(", "))
        }
        typed_ir::Type::Row { items, tail } => {
            let items = items
                .iter()
                .map(format_core_type)
                .collect::<Vec<_>>()
                .join(", ");
            format!("[{}; {}]", items, format_core_type(tail))
        }
        typed_ir::Type::Union(items) => items
            .iter()
            .map(format_core_type)
            .collect::<Vec<_>>()
            .join(" | "),
        typed_ir::Type::Inter(items) => items
            .iter()
            .map(format_core_type)
            .collect::<Vec<_>>()
            .join(" & "),
        typed_ir::Type::Recursive { var, body } => {
            format!("rec {}. {}", var.0, format_core_type(body))
        }
    }
}

fn format_core_path(path: &typed_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.clone())
        .collect::<Vec<_>>()
        .join("::")
}

pub fn format_compact_scheme(scheme: &CompactTypeScheme) -> String {
    let mut namer = VarNamer::default();
    let body = format_compact_bounds(&scheme.cty, &mut namer);
    if scheme.rec_vars.is_empty() {
        return body;
    }

    let mut recs = scheme.rec_vars.iter().collect::<Vec<_>>();
    recs.sort_by_key(|(tv, _)| tv.0);
    let recs = recs
        .into_iter()
        .map(|(tv, bounds)| {
            format!(
                "{} = {}",
                namer.name(tv.0),
                format_compact_bounds(bounds, &mut namer)
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("rec {{{recs}}}. {body}")
}

pub fn format_coalesced_scheme(scheme: &CompactTypeScheme) -> String {
    display_format::format_coalesced_scheme(scheme)
}

#[cfg(test)]
fn format_coalesced_scheme_with_role_constraints(
    infer: &Infer,
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> String {
    format_coalesced_scheme_with_role_constraints_optional_scope(
        infer,
        scheme,
        constraints,
        None,
        &HashSet::new(),
    )
}

fn format_coalesced_scheme_with_role_constraints_optional_scope(
    infer: &Infer,
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    scope: Option<&crate::lower::ctx::LowerCtx>,
    hidden_effect_paths: &HashSet<Path>,
) -> String {
    let mut namer = match scope {
        Some(scope) => display_format::VarNamer::with_scope(scope),
        None => display_format::VarNamer::default(),
    };
    let mut scheme = scheme.clone();
    display_format::materialize_effect_args(infer, &mut scheme);
    let observed_vars = compact_role_constraint_observed_vars(constraints);
    let body_type = display_format::compact_scheme_to_type_with_observed_vars_and_hidden_effects(
        &scheme,
        &observed_vars,
        hidden_effect_paths,
    );
    let mut metadata_vars = observed_vars.clone();
    display_format::collect_type_vars(&body_type, &mut metadata_vars);
    infer.clear_effect_subtract_metadata_for_vars(&metadata_vars);
    let body = display_format::format_type_with_namer(&body_type, &mut namer);
    let rendered_constraints =
        format_effect_metadata_constraints(infer, &metadata_vars, &mut namer)
            .into_iter()
            .chain(constraints.iter().map(|constraint| {
                format_role_constraint_with_display_namer(infer, constraint, &mut namer)
            }))
            .fold(Vec::<String>::new(), |mut out, item| {
                if !out.contains(&item) {
                    out.push(item);
                }
                out
            });
    if rendered_constraints.is_empty() {
        body
    } else {
        format!("{} => {}", rendered_constraints.join(", "), body)
    }
}

fn compact_role_constraint_observed_vars(
    constraints: &[CompactRoleConstraint],
) -> HashSet<TypeVar> {
    let mut out = HashSet::new();
    for constraint in constraints {
        for arg in &constraint.args {
            display_format::collect_compact_bounds_observed_vars(arg, &mut out);
        }
    }
    out
}

fn format_effect_metadata_constraints(
    infer: &Infer,
    observed_vars: &HashSet<TypeVar>,
    namer: &mut display_format::VarNamer<'_>,
) -> Vec<String> {
    let mut vars = observed_vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    let mut out = Vec::new();
    for tv in vars {
        for fact in infer.effect_subtract_facts(tv) {
            out.push(format!(
                "Subtract#{}<{}, {}>",
                fact.id.0,
                namer.type_var_name(tv),
                format_effect_subtractability(&fact.subtractability, namer)
            ));
        }
        for id in infer.effect_non_subtract_ids(tv) {
            out.push(format!("NonSubtract#{}<{}>", id.0, namer.type_var_name(tv)));
        }
    }
    out
}

fn format_effect_subtractability(
    subtractability: &EffectSubtractability,
    namer: &mut display_format::VarNamer<'_>,
) -> String {
    match subtractability {
        EffectSubtractability::Empty => "[]".to_string(),
        EffectSubtractability::All => "*".to_string(),
        EffectSubtractability::Set(atoms) => format_effect_atom_set(atoms, namer),
        EffectSubtractability::AllExcept(atoms) => {
            format!("* \\ {}", format_effect_atom_set(atoms, namer))
        }
    }
}

fn format_effect_atom_set(
    atoms: &[EffectAtom],
    namer: &mut display_format::VarNamer<'_>,
) -> String {
    let atoms = atoms
        .iter()
        .map(|atom| format_effect_atom_with_display_namer(atom, namer))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{atoms}]")
}

fn format_effect_atom_with_display_namer(
    atom: &EffectAtom,
    namer: &mut display_format::VarNamer<'_>,
) -> String {
    if atom.args.is_empty() {
        return namer.render_path(&atom.path);
    }
    let args = atom
        .args
        .iter()
        .map(|(pos, neg)| {
            if pos == neg {
                namer.type_var_name(*pos)
            } else {
                format!(
                    "{} <: {}",
                    namer.type_var_name(*pos),
                    namer.type_var_name(*neg)
                )
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}<{}>", namer.render_path(&atom.path), args)
}

fn format_role_constraint_with_display_namer(
    infer: &Infer,
    constraint: &CompactRoleConstraint,
    namer: &mut display_format::VarNamer<'_>,
) -> String {
    let arg_infos = infer.role_arg_infos_of(&constraint.role);
    let args = constraint
        .args
        .iter()
        .enumerate()
        .map(|(index, arg)| {
            let rendered =
                display_format::format_compact_role_constraint_arg_with_namer(arg, namer);
            let Some(info) = arg_infos.get(index) else {
                return rendered;
            };
            if info.name.is_empty() || info.is_input {
                rendered
            } else {
                format!("{} = {}", info.name, rendered)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}<{}>", role_path_string(&constraint.role), args)
}

fn format_frozen_scheme_with_role_constraints(
    infer: &Infer,
    scheme: &FrozenScheme,
    constraints: &[RoleConstraint],
) -> String {
    let mut namer = VarNamer::default();
    let body = format_pos_id(
        infer,
        crate::scheme::materialize_body(
            infer,
            &crate::scheme::SchemeInstance {
                scheme: scheme.clone(),
                subst: crate::scheme::SmallSubst::new(),
                level: 0,
            },
        ),
        &mut namer,
        false,
    );
    let rendered_constraints = constraints
        .iter()
        .map(|constraint| format_raw_role_constraint(infer, constraint, &mut namer))
        .fold(Vec::<String>::new(), |mut out, item| {
            if !out.contains(&item) {
                out.push(item);
            }
            out
        });
    if rendered_constraints.is_empty() {
        body
    } else {
        format!("{} => {}", rendered_constraints.join(", "), body)
    }
}

#[derive(Default)]
struct ExpectedEdgeFormatCache {
    schemes: HashMap<TypeVar, CompactTypeScheme>,
}

fn format_expected_edge(
    state: &LowerState,
    edge: &ExpectedEdge,
    cache: &mut ExpectedEdgeFormatCache,
) -> String {
    let mut namer = VarNamer::default();
    let actual = format_type_var_bounds(&state.infer, edge.actual_tv, &mut namer, cache);
    let expected = format_type_var_bounds(&state.infer, edge.expected_tv, &mut namer, cache);
    let effects = match (edge.actual_eff, edge.expected_eff) {
        (Some(actual_eff), Some(expected_eff)) => {
            let actual_eff = format_type_var_bounds(&state.infer, actual_eff, &mut namer, cache);
            let expected_eff =
                format_type_var_bounds(&state.infer, expected_eff, &mut namer, cache);
            format!(" effect {actual_eff} => {expected_eff}")
        }
        _ => String::new(),
    };
    let span = edge
        .cause
        .span
        .map(|span| format!(" @{}..{}", u32::from(span.start()), u32::from(span.end())))
        .unwrap_or_default();
    format!(
        "{}: {} => {}{}{}",
        format_expected_edge_kind(edge.kind),
        actual,
        expected,
        effects,
        span,
    )
}

fn format_type_var_bounds(
    infer: &Infer,
    tv: TypeVar,
    namer: &mut VarNamer,
    cache: &mut ExpectedEdgeFormatCache,
) -> String {
    let scheme = cache
        .schemes
        .entry(tv)
        .or_insert_with(|| compact_type_var(infer, tv));
    format_compact_bounds(&scheme.cty, namer)
}

fn format_expected_edge_kind(kind: ExpectedEdgeKind) -> &'static str {
    match kind {
        ExpectedEdgeKind::IfCondition => "if-condition",
        ExpectedEdgeKind::IfBranch => "if-branch",
        ExpectedEdgeKind::MatchGuard => "match-guard",
        ExpectedEdgeKind::MatchBranch => "match-branch",
        ExpectedEdgeKind::CatchGuard => "catch-guard",
        ExpectedEdgeKind::CatchBranch => "catch-branch",
        ExpectedEdgeKind::ApplicationCallee => "application-callee",
        ExpectedEdgeKind::ApplicationArgument => "application-argument",
        ExpectedEdgeKind::Annotation => "annotation",
        ExpectedEdgeKind::RecordField => "record-field",
        ExpectedEdgeKind::VariantPayload => "variant-payload",
        ExpectedEdgeKind::AssignmentValue => "assignment-value",
        ExpectedEdgeKind::RepresentationCoerce => "representation-coerce",
    }
}

// ── フォーマッタ ─────────────────────────────────────────────────────────────

const GREEK: &[&str] = &[
    "α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ", "λ", "μ", "ν", "ξ", "ο", "π", "ρ", "σ", "τ",
    "υ", "φ", "χ", "ψ", "ω",
];

#[derive(Default)]
struct VarNamer {
    names: HashMap<u32, String>,
    next: usize,
}

impl VarNamer {
    fn name(&mut self, raw: u32) -> String {
        if let Some(name) = self.names.get(&raw) {
            return name.clone();
        }

        let name = if self.next < GREEK.len() {
            GREEK[self.next].to_string()
        } else {
            format!("t{}", self.next)
        };
        self.next += 1;
        self.names.insert(raw, name.clone());
        name
    }
}

fn format_compact_bounds(bounds: &CompactBounds, namer: &mut VarNamer) -> String {
    match bounds {
        CompactBounds::Con { path, args } => {
            let name = path_string(path);
            if args.is_empty() {
                return name;
            }
            let args = args
                .iter()
                .map(|arg| format_compact_bounds(arg, namer))
                .collect::<Vec<_>>()
                .join(", ");
            return format!("{name}<{args}>");
        }
        CompactBounds::Tuple { items } => {
            let items = items
                .iter()
                .map(|item| format_compact_bounds(item, namer))
                .collect::<Vec<_>>()
                .join(", ");
            return format!("({items})");
        }
        CompactBounds::Interval { .. } => {}
    }
    if let Some(rendered) = format_compact_bounds_with_center(bounds, namer) {
        return rendered;
    }
    let lower_empty = is_empty_compact(bounds.lower());
    let upper_empty = is_empty_compact(bounds.upper());
    match (lower_empty, upper_empty) {
        (true, true) => bounds
            .self_var()
            .map(|tv| namer.name(tv.0))
            .unwrap_or_else(|| "_".to_string()),
        (false, true) => format_compact_type(bounds.lower(), namer, false),
        (true, false) => format!("_ <: {}", format_compact_type(bounds.upper(), namer, false)),
        (false, false) => {
            if let (Some(lower_vars), Some(upper_vars)) = (
                compact_var_set(bounds.lower()),
                compact_var_set(bounds.upper()),
            ) {
                // A var-only upper union that already contains the lower adds no
                // useful shape information to the rendered constructor argument.
                if lower_vars.is_subset(&upper_vars) {
                    return format_compact_type(bounds.lower(), namer, false);
                }
            }
            let lower = format_compact_type(bounds.lower(), namer, false);
            let upper = format_compact_type(bounds.upper(), namer, false);
            if lower == upper {
                lower
            } else {
                format!("{lower} <: {upper}")
            }
        }
    }
}

fn format_compact_bounds_with_center(
    bounds: &CompactBounds,
    namer: &mut VarNamer,
) -> Option<String> {
    let shared = shared_center_vars(bounds);
    if shared.is_empty() {
        return None;
    }
    let mut lower = bounds.lower().clone();
    let mut upper = bounds.upper().clone();
    for tv in &shared {
        lower.vars.remove(tv);
        upper.vars.remove(tv);
    }

    let lower_empty = is_empty_compact(&lower);
    let upper_empty = is_empty_compact(&upper);
    let center = format_shared_center_vars(&shared, namer);

    if !lower_empty && !upper_empty && lower == upper && has_non_var_shape(&lower) {
        return Some(format_compact_type(&lower, namer, false));
    }

    match (lower_empty, upper_empty) {
        (true, true) => Some(center),
        (false, true) => Some(format!(
            "{} | {center}",
            format_compact_type(&lower, namer, false)
        )),
        (true, false) => Some(format!(
            "{center} & {}",
            format_compact_type_with_join(&upper, namer, false, " & ")
        )),
        (false, false) => Some(format!(
            "{} | {center} & {}",
            format_compact_type(&lower, namer, false),
            format_compact_type_with_join(&upper, namer, false, " & ")
        )),
    }
}

fn shared_center_vars(bounds: &CompactBounds) -> Vec<TypeVar> {
    let mut shared = bounds
        .lower()
        .vars
        .intersection(&bounds.upper().vars)
        .copied()
        .collect::<Vec<_>>();
    shared.sort_by_key(|tv| tv.0);
    shared
}

fn format_shared_center_vars(shared: &[TypeVar], namer: &mut VarNamer) -> String {
    shared
        .iter()
        .map(|tv| namer.name(tv.0))
        .collect::<Vec<_>>()
        .join(" | ")
}

fn compact_var_set(ty: &CompactType) -> Option<HashSet<TypeVar>> {
    (ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty())
    .then(|| ty.vars.clone())
}

fn has_non_var_shape(ty: &CompactType) -> bool {
    !ty.prims.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
}

fn format_raw_role_constraint(
    infer: &Infer,
    constraint: &RoleConstraint,
    namer: &mut VarNamer,
) -> String {
    if constraint.args.is_empty() {
        return role_path_string(&constraint.role);
    }
    let arg_infos = infer.role_arg_infos_of(&constraint.role);
    let args = constraint
        .args
        .iter()
        .enumerate()
        .map(|(index, arg)| {
            let rendered = format_raw_bound_id(infer, arg.pos, arg.neg, namer);
            match arg_infos.get(index) {
                Some(info) if !info.is_input => format!("{} = {}", info.name, rendered),
                _ => rendered,
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}<{}>", role_path_string(&constraint.role), args)
}

fn format_raw_bound_id(infer: &Infer, pos: PosId, neg: NegId, namer: &mut VarNamer) -> String {
    let lower_empty = matches!(infer.arena.get_pos(pos), Pos::Bot);
    let upper_empty = matches!(infer.arena.get_neg(neg), Neg::Top);
    match (lower_empty, upper_empty) {
        (true, true) => "_".to_string(),
        (false, true) => format_pos_id(infer, pos, namer, false),
        (true, false) => format_neg_id(infer, neg, namer, false),
        (false, false) => {
            if let (Pos::Var(lhs), Neg::Var(rhs)) =
                (infer.arena.get_pos(pos), infer.arena.get_neg(neg))
            {
                if lhs == rhs {
                    return namer.name(lhs.0);
                }
            }
            let lower = format_pos_id(infer, pos, namer, false);
            let upper = format_neg_id(infer, neg, namer, false);
            if lower == upper {
                lower
            } else {
                format!("{lower} <: {upper}")
            }
        }
    }
}

fn format_pos_id(infer: &Infer, pos: PosId, namer: &mut VarNamer, needs_paren: bool) -> String {
    match infer.arena.get_pos(pos) {
        Pos::Bot => "⊥".to_string(),
        Pos::Var(tv) | Pos::Raw(tv) => namer.name(tv.0),
        Pos::Atom(atom) => format_effect_atom(&atom, namer),
        Pos::Forall(_, body) => format_pos_id(infer, body, namer, needs_paren),
        Pos::Con(path, args) => {
            let name = path_string(&path);
            if args.is_empty() {
                return name;
            }
            let args = args
                .iter()
                .map(|(lower, upper)| format_raw_bound_id(infer, *lower, *upper, namer))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name}<{args}>")
        }
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            let arg = format_neg_id(infer, arg, namer, true);
            let ret = format_pos_id(infer, ret, namer, false);
            let arg_eff = format_neg_row_inline_id(infer, arg_eff, namer);
            let ret_eff = format_pos_row_inline_id(infer, ret_eff, namer);
            let rendered = match (arg_eff, ret_eff) {
                (None, None) => format!("{arg} -> {ret}"),
                (Some(ae), None) => format!("{arg} [{ae}] -> {ret}"),
                (None, Some(re)) => format!("{arg} -> [{re}] {ret}"),
                (Some(ae), Some(re)) => format!("{arg} [{ae}] -> [{re}] {ret}"),
            };
            if needs_paren {
                format!("({rendered})")
            } else {
                rendered
            }
        }
        Pos::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|field| format!(
                    "{}{}: {}",
                    field.name.0,
                    if field.optional { "?" } else { "" },
                    format_pos_id(infer, field.value, namer, false)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Pos::RecordTailSpread { fields, tail } => format!(
            "{{{}, ..{}}}",
            fields
                .iter()
                .map(|field| format!(
                    "{}{}: {}",
                    field.name.0,
                    if field.optional { "?" } else { "" },
                    format_pos_id(infer, field.value, namer, false)
                ))
                .collect::<Vec<_>>()
                .join(", "),
            format_pos_id(infer, tail, namer, false),
        ),
        Pos::RecordHeadSpread { tail, fields } => format!(
            "{{..{}, {}}}",
            format_pos_id(infer, tail, namer, false),
            fields
                .iter()
                .map(|field| format!(
                    "{}{}: {}",
                    field.name.0,
                    if field.optional { "?" } else { "" },
                    format_pos_id(infer, field.value, namer, false)
                ))
                .collect::<Vec<_>>()
                .join(", "),
        ),
        Pos::PolyVariant(items) => format!(
            ":{{{}}}",
            items
                .iter()
                .map(|(name, payloads)| {
                    if payloads.is_empty() {
                        name.0.clone()
                    } else {
                        format!(
                            "{} {}",
                            name.0,
                            payloads
                                .iter()
                                .map(|payload| format_pos_id(infer, *payload, namer, true))
                                .collect::<Vec<_>>()
                                .join(" ")
                        )
                    }
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Pos::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(|item| format_pos_id(infer, *item, namer, false))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Pos::Row(items, tail) => {
            let items = items
                .iter()
                .map(|item| format_pos_id(infer, *item, namer, false))
                .collect::<Vec<_>>();
            if matches!(infer.arena.get_pos(tail), Pos::Bot) {
                format!("[{};]", items.join(", "))
            } else {
                let tail = format_pos_id(infer, tail, namer, false);
                if items.is_empty() {
                    format!("[; {tail}]")
                } else {
                    format!("[{}; {tail}]", items.join(", "))
                }
            }
        }
        Pos::Union(_, _) => {
            let joined = flatten_pos_union_ids(infer, pos)
                .into_iter()
                .map(|item| format_pos_id(infer, item, namer, true))
                .collect::<Vec<_>>()
                .join(" | ");
            if needs_paren {
                format!("({joined})")
            } else {
                joined
            }
        }
    }
}

fn format_neg_id(infer: &Infer, neg: NegId, namer: &mut VarNamer, needs_paren: bool) -> String {
    match infer.arena.get_neg(neg) {
        Neg::Top => "⊤".to_string(),
        Neg::Var(tv) => namer.name(tv.0),
        Neg::Atom(atom) => format_effect_atom(&atom, namer),
        Neg::Forall(_, body) => format_neg_id(infer, body, namer, needs_paren),
        Neg::Con(path, args) => {
            let name = path_string(&path);
            if args.is_empty() {
                return name;
            }
            let args = args
                .iter()
                .map(|(lower, upper)| format_raw_bound_id(infer, *lower, *upper, namer))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name}<{args}>")
        }
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            let arg = format_pos_id(infer, arg, namer, true);
            let ret = format_neg_id(infer, ret, namer, false);
            let arg_eff = format_pos_row_inline_id(infer, arg_eff, namer);
            let ret_eff = format_neg_row_inline_id(infer, ret_eff, namer);
            let rendered = match (arg_eff, ret_eff) {
                (None, None) => format!("{arg} -> {ret}"),
                (Some(ae), None) => format!("{arg} [{ae}] -> {ret}"),
                (None, Some(re)) => format!("{arg} -> [{re}] {ret}"),
                (Some(ae), Some(re)) => format!("{arg} [{ae}] -> [{re}] {ret}"),
            };
            if needs_paren {
                format!("({rendered})")
            } else {
                rendered
            }
        }
        Neg::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|field| format!(
                    "{}{}: {}",
                    field.name.0,
                    if field.optional { "?" } else { "" },
                    format_neg_id(infer, field.value, namer, false)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Neg::PolyVariant(items) => format!(
            ":{{{}}}",
            items
                .iter()
                .map(|(name, payloads)| {
                    if payloads.is_empty() {
                        name.0.clone()
                    } else {
                        format!(
                            "{} {}",
                            name.0,
                            payloads
                                .iter()
                                .map(|payload| format_neg_id(infer, *payload, namer, true))
                                .collect::<Vec<_>>()
                                .join(" ")
                        )
                    }
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Neg::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(|item| format_neg_id(infer, *item, namer, false))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Neg::Row(items, tail) => {
            let items = items
                .iter()
                .map(|item| format_neg_id(infer, *item, namer, false))
                .collect::<Vec<_>>();
            if matches!(infer.arena.get_neg(tail), Neg::Top) {
                format!("[{};]", items.join(", "))
            } else {
                let tail = format_neg_id(infer, tail, namer, false);
                if items.is_empty() {
                    format!("[; {tail}]")
                } else {
                    format!("[{}; {tail}]", items.join(", "))
                }
            }
        }
        Neg::Intersection(_, _) => {
            let joined = flatten_neg_intersection_ids(infer, neg)
                .into_iter()
                .map(|item| format_neg_id(infer, item, namer, true))
                .collect::<Vec<_>>()
                .join(" & ");
            if needs_paren {
                format!("({joined})")
            } else {
                joined
            }
        }
    }
}

fn format_pos_row_inline_id(infer: &Infer, pos: PosId, namer: &mut VarNamer) -> Option<String> {
    match infer.arena.get_pos(pos) {
        Pos::Bot => None,
        Pos::Row(items, tail) => {
            let mut parts = items
                .iter()
                .map(|item| format_pos_id(infer, *item, namer, false))
                .collect::<Vec<_>>();
            if !matches!(infer.arena.get_pos(tail), Pos::Bot) {
                parts.push(format_pos_id(infer, tail, namer, false));
            }
            (!parts.is_empty()).then(|| parts.join("; "))
        }
        Pos::Union(_, _) => Some(
            flatten_pos_union_ids(infer, pos)
                .into_iter()
                .map(|item| format_pos_id(infer, item, namer, true))
                .collect::<Vec<_>>()
                .join(" | "),
        ),
        _ => Some(format_pos_id(infer, pos, namer, false)),
    }
}

fn format_neg_row_inline_id(infer: &Infer, neg: NegId, namer: &mut VarNamer) -> Option<String> {
    match infer.arena.get_neg(neg) {
        Neg::Top => None,
        Neg::Row(items, tail) => {
            let mut parts = items
                .iter()
                .map(|item| format_neg_id(infer, *item, namer, false))
                .collect::<Vec<_>>();
            if !matches!(infer.arena.get_neg(tail), Neg::Top) {
                parts.push(format_neg_id(infer, tail, namer, false));
            }
            (!parts.is_empty()).then(|| parts.join("; "))
        }
        Neg::Intersection(_, _) => Some(
            flatten_neg_intersection_ids(infer, neg)
                .into_iter()
                .map(|item| format_neg_id(infer, item, namer, true))
                .collect::<Vec<_>>()
                .join(" & "),
        ),
        _ => Some(format_neg_id(infer, neg, namer, false)),
    }
}

fn flatten_pos_union_ids(infer: &Infer, pos: PosId) -> Vec<PosId> {
    match infer.arena.get_pos(pos) {
        Pos::Union(lhs, rhs) => {
            let mut items = flatten_pos_union_ids(infer, lhs);
            items.extend(flatten_pos_union_ids(infer, rhs));
            items
        }
        _ => vec![pos],
    }
}

fn flatten_neg_intersection_ids(infer: &Infer, neg: NegId) -> Vec<NegId> {
    match infer.arena.get_neg(neg) {
        Neg::Intersection(lhs, rhs) => {
            let mut items = flatten_neg_intersection_ids(infer, lhs);
            items.extend(flatten_neg_intersection_ids(infer, rhs));
            items
        }
        _ => vec![neg],
    }
}

fn format_pos_row_inline(_pos: &Pos, _namer: &mut VarNamer) -> Option<String> {
    None
}

fn format_neg_row_inline(_neg: &Neg, _namer: &mut VarNamer) -> Option<String> {
    None
}

fn flatten_pos_union<'a>(pos: &'a Pos) -> Vec<&'a Pos> {
    vec![pos]
}

fn flatten_neg_intersection<'a>(neg: &'a Neg) -> Vec<&'a Neg> {
    vec![neg]
}

#[allow(dead_code)]
fn _legacy_dump_marker() {
    let _ = (
        format_pos_row_inline as fn(&Pos, &mut VarNamer) -> Option<String>,
        format_neg_row_inline as fn(&Neg, &mut VarNamer) -> Option<String>,
        flatten_pos_union as for<'a> fn(&'a Pos) -> Vec<&'a Pos>,
        flatten_neg_intersection as for<'a> fn(&'a Neg) -> Vec<&'a Neg>,
    );
}

fn format_effect_atom(atom: &EffectAtom, namer: &mut VarNamer) -> String {
    if atom.args.is_empty() {
        return path_string(&atom.path);
    }
    let args = atom
        .args
        .iter()
        .map(|(pos, neg)| {
            if pos == neg {
                namer.name(pos.0)
            } else {
                format!("{} <: {}", namer.name(pos.0), namer.name(neg.0))
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}<{}>", path_string(&atom.path), args)
}

fn format_role_constraint_arg(arg: &CompactBounds, namer: &mut VarNamer) -> String {
    if let Some(rendered) = format_compact_bounds_with_center(arg, namer) {
        return rendered;
    }
    match (is_empty_compact(arg.lower()), is_empty_compact(arg.upper())) {
        (true, true) => "_".to_string(),
        (false, true) => format_compact_type(arg.lower(), namer, false),
        (true, false) => format_compact_type_with_join(arg.upper(), namer, false, " & "),
        (false, false) if arg.lower() == arg.upper() => {
            format_compact_type(arg.lower(), namer, false)
        }
        (false, false) => format_compact_interval_arg(arg.lower(), arg.upper(), namer),
    }
}

pub(crate) fn format_compact_role_constraint_arg(arg: &CompactBounds) -> String {
    format_role_constraint_arg(arg, &mut VarNamer::default())
}

fn format_compact_interval_arg(
    lower: &CompactType,
    upper: &CompactType,
    namer: &mut VarNamer,
) -> String {
    let mut lower_parts = format_compact_type_parts(lower, namer);
    let upper_parts = format_compact_type_parts(upper, namer);
    if lower_parts.is_empty() {
        return upper_parts.join(" & ");
    }
    if upper_parts.is_empty() {
        return lower_parts.join(" | ");
    }

    let shared = lower_parts
        .iter()
        .rposition(|part| upper_parts.iter().any(|upper| upper == part));
    if let Some(index) = shared {
        let shared_part = lower_parts.remove(index);
        let mut intersection = vec![shared_part.clone()];
        intersection.extend(upper_parts.into_iter().filter(|part| part != &shared_part));
        lower_parts.push(intersection.join(" & "));
    } else {
        lower_parts.push(upper_parts.join(" & "));
    }
    lower_parts.join(" | ")
}

fn format_compact_type(ty: &CompactType, namer: &mut VarNamer, needs_paren: bool) -> String {
    format_compact_type_with_join(ty, namer, needs_paren, " | ")
}

fn format_compact_type_with_join(
    ty: &CompactType,
    namer: &mut VarNamer,
    needs_paren: bool,
    join: &str,
) -> String {
    let mut parts = format_compact_type_parts(ty, namer);
    if parts.is_empty() {
        return "_".to_string();
    }
    if parts.len() == 1 {
        return parts.remove(0);
    }

    let joined = parts.join(join);
    if needs_paren {
        format!("({joined})")
    } else {
        joined
    }
}

fn format_compact_type_parts(ty: &CompactType, namer: &mut VarNamer) -> Vec<String> {
    let mut parts = Vec::new();

    let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    parts.extend(vars.into_iter().map(|tv| namer.name(tv.0)));

    let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
    prims.sort_by(|a, b| path_string(a).cmp(&path_string(b)));
    parts.extend(prims.into_iter().map(|path| path_string(&path)));

    let mut cons = ty.cons.clone();
    cons.sort_by(|a, b| path_string(&a.path).cmp(&path_string(&b.path)));
    parts.extend(cons.into_iter().map(|con| format_compact_con(&con, namer)));

    parts.extend(ty.funs.iter().map(|fun| format_compact_fun(fun, namer)));
    parts.extend(
        ty.records
            .iter()
            .map(|record| format_compact_record(record, namer)),
    );
    parts.extend(
        ty.variants
            .iter()
            .map(|variant| format_compact_variant(variant, namer)),
    );
    parts.extend(ty.tuples.iter().map(|tuple| {
        let items = tuple
            .iter()
            .map(|item| format_compact_type(item, namer, false))
            .collect::<Vec<_>>();
        format!("({})", items.join(", "))
    }));
    parts.extend(ty.rows.iter().map(|row| format_compact_row(row, namer)));

    parts
}

fn format_compact_con(con: &CompactCon, namer: &mut VarNamer) -> String {
    let name = path_string(&con.path);
    if con.args.is_empty() {
        return name;
    }

    let args = con
        .args
        .iter()
        .map(|arg| format_compact_bounds(arg, namer))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{name}<{args}>")
}

fn format_compact_fun(fun: &CompactFun, namer: &mut VarNamer) -> String {
    let arg = format_compact_type(&fun.arg, namer, true);
    let ret = format_compact_type(&fun.ret, namer, false);
    let arg_eff = format_row_inline(&fun.arg_eff, namer);
    let ret_eff = format_row_inline(&fun.ret_eff, namer);
    match (arg_eff, ret_eff) {
        (None, None) => format!("{arg} -> {ret}"),
        (Some(ae), None) => format!("{arg} [{ae}] -> {ret}"),
        (None, Some(re)) => format!("{arg} -> [{re}] {ret}"),
        (Some(ae), Some(re)) => format!("{arg} [{ae}] -> [{re}] {ret}"),
    }
}

fn format_compact_record(record: &CompactRecord, namer: &mut VarNamer) -> String {
    let fields = record
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}{}: {}",
                field.name.0,
                if field.optional { "?" } else { "" },
                format_compact_type(&field.value, namer, false)
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{{{fields}}}")
}

fn format_compact_variant(variant: &CompactVariant, namer: &mut VarNamer) -> String {
    let items = variant
        .items
        .iter()
        .map(|(name, payloads)| {
            if payloads.is_empty() {
                return name.0.clone();
            }
            let payloads = payloads
                .iter()
                .map(|payload| format_compact_type(payload, namer, true))
                .collect::<Vec<_>>()
                .join(" ");
            format!("{} {payloads}", name.0)
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(":{{{items}}}")
}

fn format_compact_row(row: &CompactRow, namer: &mut VarNamer) -> String {
    let items = row
        .items
        .iter()
        .map(|item| format_compact_type(item, namer, false))
        .collect::<Vec<_>>();
    if is_empty_compact(&row.tail) {
        return format!("[{};]", items.join(", "));
    }
    let tail = format_compact_type(&row.tail, namer, false);
    if items.is_empty() {
        format!("[; {tail}]")
    } else {
        format!("[{}; {tail}]", items.join(", "))
    }
}

fn format_row_inline(ty: &CompactType, namer: &mut VarNamer) -> Option<String> {
    match ty.rows.as_slice() {
        [] if is_empty_compact(ty) => None,
        [row]
            if ty.vars.is_empty()
                && ty.prims.is_empty()
                && ty.cons.is_empty()
                && ty.funs.is_empty()
                && ty.records.is_empty()
                && ty.variants.is_empty()
                && ty.tuples.is_empty() =>
        {
            let items = row
                .items
                .iter()
                .map(|item| format_compact_type(item, namer, false))
                .collect::<Vec<_>>();
            if is_empty_compact(&row.tail) {
                return if items.is_empty() {
                    None
                } else {
                    Some(items.join(", "))
                };
            }
            let tail = format_compact_type(&row.tail, namer, false);
            return if items.is_empty() {
                Some(tail)
            } else {
                Some(format!("{}; {tail}", items.join(", ")))
            };
        }
        _ => Some(format_compact_type(ty, namer, false)),
    }
}

fn is_empty_compact(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn path_string(path: &Path) -> String {
    path_string_names(&path.segments)
}

fn role_path_string(path: &Path) -> String {
    if matches!(path.segments.as_slice(), [Name(std), ..] if std == "std") {
        if let Some(name) = path.segments.last() {
            return display_name_segment(name.0.as_str()).to_string();
        }
    }
    path_string(path)
}

fn path_string_names(names: &[Name]) -> String {
    names
        .iter()
        .map(|name| display_name_segment(name.0.as_str()))
        .collect::<Vec<_>>()
        .join("::")
}

fn display_name_segment(name: &str) -> &str {
    name
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::collections::{HashMap, HashSet};
    use std::panic::{self, AssertUnwindSafe};
    use std::sync::{OnceLock, mpsc};
    use std::thread;

    use crate::diagnostic::TypeOriginKind;
    use crate::fresh_type_var;
    use crate::lower::stmt::{finish_lowering, lower_root, lower_root_in_module};
    use crate::simplify::compact::{
        CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRow, CompactType,
        CompactTypeScheme,
    };
    use crate::simplify::cooccur::CompactRoleConstraint;
    use crate::solve::Infer;
    use crate::types::RecordField;
    use crate::{LowerState, Name, Path};
    use crate::{Name as TirName, Path as TirPath};
    use rowan::SyntaxNode;
    use yulang_parser::sink::YulangLanguage;

    use super::render_compact_results;

    type LargeStackJob = Box<dyn FnOnce() + Send + 'static>;

    thread_local! {
        static STD_SOURCE_CACHE: RefCell<crate::SourceLowerCache> =
            RefCell::new(crate::SourceLowerCache::default());
    }

    fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
    where
        T: Send + 'static,
    {
        let (result_tx, result_rx) = mpsc::sync_channel(1);
        large_stack_worker()
            .send(Box::new(move || {
                let result = panic::catch_unwind(AssertUnwindSafe(f));
                let _ = result_tx.send(result);
            }))
            .expect("large-stack test worker should accept jobs");
        match result_rx
            .recv()
            .expect("large-stack test worker should reply")
        {
            Ok(value) => value,
            Err(payload) => panic::resume_unwind(payload),
        }
    }

    fn large_stack_worker() -> &'static mpsc::Sender<LargeStackJob> {
        static WORKER: OnceLock<mpsc::Sender<LargeStackJob>> = OnceLock::new();
        WORKER.get_or_init(|| {
            let (job_tx, job_rx) = mpsc::channel::<LargeStackJob>();
            thread::Builder::new()
                .name("display-dump-large-stack".to_string())
                .stack_size(32 * 1024 * 1024)
                .spawn(move || {
                    for job in job_rx {
                        job();
                    }
                })
                .expect("spawn large-stack test worker");
            job_tx
        })
    }

    fn lower_virtual_std_source(source: &str) -> crate::LoweredSources {
        let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let source_set = crate::collect_virtual_source_files_with_options(
            source,
            Some(repo_root),
            crate::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .expect("source should collect");
        STD_SOURCE_CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            crate::lower_source_set_with_std_cache(&source_set, &mut cache)
        })
    }

    #[test]
    fn render_compact_results_lists_named_bindings() {
        let green = yulang_parser::parse_module_to_green("my x = 42");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        assert!(rendered.iter().any(|(name, _)| name == "x"));
        assert!(state.ctx.resolve_value(&Name("x".to_string())).is_some());
    }

    #[test]
    fn render_compact_results_keeps_function_shapes() {
        let green =
            yulang_parser::parse_module_to_green("my f x = x\nmy compose f g x = f (g x)\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let f = rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered");
        let compose = rendered
            .iter()
            .find(|(name, _)| name == "compose")
            .expect("compose should be rendered");

        assert!(
            f.1.contains("->"),
            "f should render as a function shape: {}",
            f.1
        );
        assert!(
            compose.1.matches("->").count() >= 3,
            "compose should keep nested function shape: {}",
            compose.1
        );
    }

    #[test]
    fn finalize_compact_results_produces_fun_bounds_for_id_example() {
        let green =
            yulang_parser::parse_module_to_green("my f x = x\nmy compose f g x = f (g x)\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);
        state.finalize_compact_results();

        let f_def = state.ctx.resolve_value(&Name("f".to_string())).unwrap();
        let compose_def = state
            .ctx
            .resolve_value(&Name("compose".to_string()))
            .unwrap();
        let f_scheme = state.compact_scheme_of(f_def).unwrap();
        let compose_scheme = state.compact_scheme_of(compose_def).unwrap();
        assert!(
            !f_scheme.cty.lower().funs.is_empty(),
            "f should have a function lower bound"
        );
        assert!(
            !compose_scheme.cty.lower().funs.is_empty(),
            "compose should have a function lower bound"
        );
    }

    #[test]
    fn render_compact_results_coalesces_identity_shape() {
        let green = yulang_parser::parse_module_to_green("my id x = x\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let id = rendered
            .iter()
            .find(|(name, _)| name == "id")
            .expect("id should be rendered");
        assert_eq!(id.1, "α -> α");
    }

    #[test]
    fn format_coalesced_scheme_hash_cons_recursive_outer_layer() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds::Interval {
                self_var: None,
                lower: CompactType {
                    funs: vec![CompactFun {
                        arg: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType {
                            records: vec![CompactRecord {
                                fields: vec![
                                    RecordField::required(
                                        Name("L".to_string()),
                                        CompactType {
                                            vars: HashSet::from([a]),
                                            ..CompactType::default()
                                        },
                                    ),
                                    RecordField::required(
                                        Name("R".to_string()),
                                        CompactType {
                                            vars: HashSet::from([b]),
                                            ..CompactType::default()
                                        },
                                    ),
                                ],
                            }],
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: HashMap::from([(
                b,
                CompactBounds::Interval {
                    self_var: Some(b),
                    lower: CompactType {
                        records: vec![CompactRecord {
                            fields: vec![
                                RecordField::required(
                                    Name("L".to_string()),
                                    CompactType {
                                        vars: HashSet::from([a]),
                                        ..CompactType::default()
                                    },
                                ),
                                RecordField::required(
                                    Name("R".to_string()),
                                    CompactType {
                                        vars: HashSet::from([b]),
                                        ..CompactType::default()
                                    },
                                ),
                            ],
                        }],
                        ..CompactType::default()
                    },
                    upper: CompactType::default(),
                },
            )]),
        };

        assert_eq!(
            super::format_coalesced_scheme(&scheme),
            "α -> rec {β = {L: α, R: β}}. β"
        );
    }

    #[test]
    fn render_compact_results_accumulates_higher_order_argument_effects() {
        let green = yulang_parser::parse_module_to_green("my compose f g x = f (g x)\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let compose = rendered
            .iter()
            .find(|(name, _)| name == "compose")
            .expect("compose should be rendered");
        assert_eq!(compose.1, "(α -> [γ] β) -> (δ -> [γ] α) -> δ -> [γ] β");
    }

    #[test]
    fn render_compact_results_keeps_minimal_catch_shape() {
        let green = yulang_parser::parse_module_to_green(
            "act undet:\n  our bool: () -> bool\n\nmy shallow_det x = catch x:\n  undet::bool(), k -> k true\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let shallow_det = rendered
            .iter()
            .find(|(name, _)| name == "shallow_det")
            .expect("shallow_det should be rendered");
        assert_eq!(shallow_det.1, "α -> α");
    }

    #[test]
    fn unannotated_callback_catch_does_not_emit_handler_match_artifacts() {
        let green = yulang_parser::parse_module_to_green(
            "act undet:\n  our bool: () -> bool\n\nmy shallow(f) = catch f():\n  undet::bool(), k -> k true\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let program = crate::export_core_program(&mut state);
        assert!(
            program.evidence.handler_matches.is_empty(),
            "unannotated callback catch should not capture or export handler_match evidence"
        );

        let rendered = render_compact_results(&mut state);
        let shallow = rendered
            .iter()
            .find(|(name, _)| name == "shallow")
            .expect("shallow should be rendered");
        assert!(!shallow.1.contains("handler_match"));
        assert!(!shallow.1.contains("Shift"));
        assert!(!shallow.1.contains("Peel"));
    }

    #[test]
    fn render_compact_results_keeps_annotated_argument_effects() {
        let green =
            yulang_parser::parse_module_to_green("my f(x: [_] _) = x\nmy g(x: [io; e] _) = x\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let f = rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered");
        let g = rendered
            .iter()
            .find(|(name, _)| name == "g")
            .expect("g should be rendered");

        assert_eq!(f.1, "α [β] -> [β] α");
        assert_eq!(g.1, "α [β] -> [β] α");
    }

    #[test]
    fn render_compact_results_lifts_pure_function_to_effectful_input() {
        let green = yulang_parser::parse_module_to_green(
            "my app(f: _ [_] -> _) x = f x\nmy id x = x\nmy z = app(id, 1)\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let app = rendered
            .iter()
            .find(|(name, _)| name == "app")
            .expect("app should be rendered");
        let z = rendered
            .iter()
            .find(|(name, _)| name == "z")
            .expect("z should be rendered");

        assert_eq!(app.1, "(α -> [γ] β) -> α -> [γ] β");
        assert_eq!(z.1, "int");
    }

    #[test]
    fn render_compact_results_keeps_effectful_argument_through_pure_id() {
        let green = yulang_parser::parse_module_to_green(
            "act undet:\n  our bool: () -> bool\n\nmy id x = x\nmy f() = id(undet::bool())\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let f = rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered");

        assert_eq!(f.1, "unit -> [undet] bool");
    }

    #[test]
    fn lowering_records_annotation_type_origins() {
        let green = yulang_parser::parse_module_to_green("my g(x: [io; e] _) = x\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        assert!(
            state.infer.origins.borrow().iter().any(|(_, entry)| {
                entry.kind == TypeOriginKind::Annotation
                    && entry
                        .label
                        .as_deref()
                        .is_some_and(|label| label.contains("effect annotation") || label == "e")
            }),
            "annotation-created effect variables should carry annotation origins",
        );
    }

    #[test]
    fn lowering_records_signature_annotation_spans() {
        let source = "act eff:\n  our id: 'a -> 'a\n";
        let green = yulang_parser::parse_module_to_green(source);
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let span = state
            .infer
            .origins
            .borrow()
            .iter()
            .find_map(|(_, entry)| {
                (entry.kind == TypeOriginKind::Annotation && entry.label.as_deref() == Some("'a"))
                    .then_some(entry.span)
                    .flatten()
            })
            .expect("signature type variables should carry source spans");
        let start = u32::from(span.start()) as usize;
        let end = u32::from(span.end()) as usize;
        assert_eq!(&source[start..end], "'a");
    }

    #[test]
    fn render_compact_results_keeps_catch_and_annotation_interaction() {
        let green = yulang_parser::parse_module_to_green(
            "act io:\n  our read: () -> int\n\nmy h(x: [_] _) = catch x:\n  io::read(), k -> k 0\n\nmy k(x: [io; e] _) = catch x:\n  io::read(), k -> k 0\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let h = rendered
            .iter()
            .find(|(name, _)| name == "h")
            .expect("h should be rendered");
        let k = rendered
            .iter()
            .find(|(name, _)| name == "k")
            .expect("k should be rendered");

        // テスト期待値を変えるな
        assert_eq!(h.1, "α [β & [io; β]] -> [β] α");
        assert_eq!(k.1, "α [β & [io; β]] -> [β] α");
    }

    #[test]
    fn render_compact_results_keeps_concrete_effect_annotation_shallow() {
        let green = yulang_parser::parse_module_to_green(
            "act undet:\n  our bool: () -> bool\n\nmy shallow_det(x: [undet] _) = catch x:\n  undet::bool(), k -> k true\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let shallow_det = rendered
            .iter()
            .find(|(name, _)| name == "shallow_det")
            .expect("shallow_det should be rendered");

        // テスト期待値を変えるな
        assert_eq!(shallow_det.1, "α [β & [undet; β]] -> [β] α");
    }

    #[test]
    fn render_compact_results_keeps_shallow_handler_limited_to_annotated_effect() {
        let green = yulang_parser::parse_module_to_green(
            "act read1:\n  our read: () -> int\n\nact read2:\n  our read: () -> int\n\nmy shallow_read1(x: [read1] _) = catch x:\n  read1::read(), k -> k 0\n  read2::read(), k -> k 0\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let shallow_read1 = rendered
            .iter()
            .find(|(name, _)| name == "shallow_read1")
            .expect("shallow_read1 should be rendered");

        assert_eq!(shallow_read1.1, "α [β & [read1; β]] -> [β] α");
    }

    #[test]
    fn render_compact_results_keeps_concrete_effect_annotation_shallow_with_root_use() {
        let green = yulang_parser::parse_module_to_green(
            "act undet:\n  our bool: () -> bool\n\nmy shallow_det(x: [undet] _) = catch x:\n  undet::bool(), k -> k true\n\nshallow_det(undet::bool())\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let shallow_det = rendered
            .iter()
            .find(|(name, _)| name == "shallow_det")
            .expect("shallow_det should be rendered");

        // テスト期待値を変えるな
        assert_eq!(shallow_det.1, "α [β & [undet; β]] -> [β] α");
    }

    #[test]
    fn render_compact_results_keeps_higher_order_effect_annotations_as_function_sigs() {
        let green = yulang_parser::parse_module_to_green(
            "act io:\n  our read: () -> int\n\nmy g1(f: () -> [io] _) = f\nmy g2(f: () -> [io] _) = \\() -> f()\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let g1 = rendered
            .iter()
            .find(|(name, _)| name == "g1")
            .expect("g1 should be rendered");
        let g2 = rendered
            .iter()
            .find(|(name, _)| name == "g2")
            .expect("g2 should be rendered");

        assert_eq!(g1.1, "(unit -> [β] α) -> unit -> [β] α");
        assert_eq!(g2.1, "(unit -> [β] α) -> unit -> [β] α");
    }

    #[test]
    fn render_compact_results_keeps_higher_order_catch_argument_pure() {
        let green = yulang_parser::parse_module_to_green(
            "act undet:\n  our bool: () -> bool\n\nmy shallow(f: () -> [undet] _) = catch f():\n  undet::bool(), k -> k true\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let shallow = rendered
            .iter()
            .find(|(name, _)| name == "shallow")
            .expect("shallow should be rendered");

        assert_eq!(shallow.1, "(unit -> [undet; β] α) -> [β] α");
    }

    #[test]
    fn format_coalesced_scheme_with_role_constraints_shares_var_names_with_body() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let e = fresh_type_var();
        let flip = Path {
            segments: vec![Name("flip".to_string())],
        };
        let list = Path {
            segments: vec![
                Name("std".to_string()),
                Name("list".to_string()),
                Name("list".to_string()),
            ],
        };
        let add = Path {
            segments: vec![Name("Add".to_string())],
        };
        let list_a = CompactType {
            cons: vec![CompactCon {
                path: list,
                args: vec![CompactBounds::Interval {
                    self_var: None,
                    lower: CompactType {
                        vars: HashSet::from([a]),
                        ..CompactType::default()
                    },
                    upper: CompactType {
                        vars: HashSet::from([a]),
                        ..CompactType::default()
                    },
                }],
            }],
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds::Interval {
                self_var: None,
                lower: CompactType {
                    funs: vec![CompactFun {
                        arg: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                        arg_eff: CompactType {
                            rows: vec![CompactRow {
                                items: vec![CompactType {
                                    prims: HashSet::from([flip]),
                                    ..CompactType::default()
                                }],
                                tail: Box::new(CompactType {
                                    vars: HashSet::from([e]),
                                    ..CompactType::default()
                                }),
                            }],
                            ..CompactType::default()
                        },
                        ret_eff: CompactType {
                            vars: HashSet::from([e]),
                            ..CompactType::default()
                        },
                        ret: {
                            let mut ret = list_a.clone();
                            ret.vars.insert(b);
                            ret
                        },
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };
        let constraints = vec![CompactRoleConstraint {
            role: add,
            args: vec![CompactBounds::Interval {
                self_var: None,
                lower: {
                    let mut lower = list_a;
                    lower.vars.insert(b);
                    lower
                },
                upper: CompactType {
                    vars: HashSet::from([b]),
                    ..CompactType::default()
                },
            }],
        }];
        let infer = Infer::new();

        assert_eq!(
            super::format_coalesced_scheme_with_role_constraints(&infer, &scheme, &constraints),
            "Add<std::list::list<α> | β> => α [flip; γ] -> [γ] β | std::list::list<α>"
        );
    }

    #[test]
    fn render_compact_results_lowers_nested_act_declarations_in_act_body() {
        let green = yulang_parser::parse_module_to_green(
            "act outer:\n  our op: () -> never\n  my act local:\n    our break: () -> never\n    our sub(x: [_] _) = catch x:\n      break(), _ -> ()\n      _ -> ()\n  our run(f: () -> [outer] _) = local::sub: catch f():\n    op(), _ -> local::break()\n    _ -> ()\n\npub r = outer::run\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let r = rendered
            .iter()
            .find(|(name, _)| name == "r")
            .expect("r should be rendered");

        assert_eq!(r.1, "(unit -> [outer; α] ⊤) -> [α] unit");
    }

    #[test]
    fn render_compact_results_keeps_function_annotations_effect_open() {
        let green = yulang_parser::parse_module_to_green(
            "my g(x: int) = x\nmy h(f: () -> int) = f\nmy k(f: () -> int) = \\() -> f()\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let g = rendered
            .iter()
            .find(|(name, _)| name == "g")
            .expect("g should be rendered");
        let h = rendered
            .iter()
            .find(|(name, _)| name == "h")
            .expect("h should be rendered");
        let k = rendered
            .iter()
            .find(|(name, _)| name == "k")
            .expect("k should be rendered");

        assert_eq!(g.1, "int -> int");
        assert_eq!(h.1, "(unit -> [α] int) -> unit -> [α] int");
        assert_eq!(k.1, "(unit -> [α] int) -> unit -> [α] int");
    }

    #[test]
    fn render_compact_results_distinguishes_shallow_and_recursive_catch() {
        let green = yulang_parser::parse_module_to_green(
            "act io:\n  our read: () -> int\n\nmy h(x: [_] _) = catch x:\n  io::read(), k -> k 0\n\nmy j(x: [_] _) = catch x:\n  io::read(), k -> j(k 0)\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let h = rendered
            .iter()
            .find(|(name, _)| name == "h")
            .expect("h should be rendered");
        let j = rendered
            .iter()
            .find(|(name, _)| name == "j")
            .expect("j should be rendered");

        assert_eq!(h.1, "α [β & [io; β]] -> [β] α");
        assert_eq!(j.1, "α [io; β] -> [β] α");
    }

    #[test]
    fn render_compact_results_keeps_act_type_args_through_catch() {
        let green = yulang_parser::parse_module_to_green(
            "act var 't:\n  our get: () -> 't\n  our set: 't -> ()\n\nmy run(v, x: [_] _) = catch x:\n  var::get(), k -> run(v, k v)\n  var::set v, k -> run(v, k())\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let run = rendered
            .iter()
            .find(|(name, _)| name == "run")
            .expect("run should be rendered");
        let get = rendered
            .iter()
            .find(|(name, _)| name == "var::get")
            .expect("var::get should be rendered");
        let set = rendered
            .iter()
            .find(|(name, _)| name == "var::set")
            .expect("var::set should be rendered");

        assert_eq!(run.1, "α -> β [var<α>; γ] -> [γ] β");
        assert_eq!(get.1, "unit -> [var<α>] α");
        assert_eq!(set.1, "α -> [var<α>] unit");
    }

    #[test]
    fn render_compact_results_handles_never_returning_recursive_effect_arm() {
        let green = yulang_parser::parse_module_to_green(
            "act parse 'item 'err:\n  our item: () -> 'item\n  our fail: 'err -> never\n\nmy run(x: [parse int str] int) = catch x:\n  parse::item(), k -> run(k 0)\n  parse::fail e, _ -> ()\n  _ -> ()\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let run = rendered
            .iter()
            .find(|(name, _)| name == "run")
            .expect("run should be rendered");

        assert_eq!(run.1, "int [parse<int, std::str::str>; α] -> [α] unit");
    }

    #[test]
    fn render_compact_results_lowers_act_body_helpers() {
        let green = yulang_parser::parse_module_to_green(
            "act var 't:\n  our get: () -> 't\n  our set: 't -> ()\n\n  my run(v, x: [_] _) = catch x:\n    get(), k -> run(v, k v)\n    set v, k -> run(v, k())\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let run = rendered
            .iter()
            .find(|(name, _)| name == "var::run")
            .expect("var::run should be rendered");

        assert_eq!(run.1, "α -> β [var<α>; γ] -> [γ] β");
    }

    #[test]
    fn render_compact_results_lowers_annotated_act_body_helpers() {
        for src in [
            "act var 't:\n  our get: () -> 't\n  our set: 't -> ()\n\n  my run(v: 't, x: [_] 'r): 'r = catch x:\n    get(), k -> run(v, k v)\n    set v, k -> run(v, k())\n",
            "act var 't:\n  our get: () -> 't\n  our set: 't -> ()\n\n  my run(v: 't, x: [_] _) = catch x:\n    get(), k -> run(v, k v)\n    set v, k -> run(v, k())\n",
            "act var 't:\n  our get: () -> 't\n  our set: 't -> ()\n\n  my run(v, x: [_] 'r) = catch x:\n    get(), k -> run(v, k v)\n    set v, k -> run(v, k())\n",
            "act var 't:\n  our get: () -> 't\n  our set: 't -> ()\n\n  my run(v, x: [_] _): 'r = catch x:\n    get(), k -> run(v, k v)\n    set v, k -> run(v, k())\n",
            "act var 't:\n  our get: () -> 't\n  our set: 't -> ()\n\n  my run(v: 't, x: [_] 'r): 'r = catch x:\n    get(), k -> run v: k v\n    set v, k -> run v: k()\n",
        ] {
            let green = yulang_parser::parse_module_to_green(src);
            let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
            let mut state = LowerState::new();
            lower_root(&mut state, &root);

            let rendered = render_compact_results(&mut state);
            let run = rendered
                .iter()
                .find(|(name, _)| name == "var::run")
                .expect("var::run should be rendered");

            assert_eq!(run.1, "α -> β [var<α>; γ] -> [γ] β");
        }
    }

    #[test]
    fn render_compact_results_lowers_copied_act() {
        let green = yulang_parser::parse_module_to_green(
            "act var 't:\n  our get: () -> 't\n  our set: 't -> ()\n\nact local 't = var 't\n\nmy run(v, x: [_] _) = catch x:\n  local::get(), k -> run(v, k v)\n  local::set v, k -> run(v, k())\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let run = rendered
            .iter()
            .find(|(name, _)| name == "run")
            .expect("run should be rendered");
        let get = rendered
            .iter()
            .find(|(name, _)| name == "local::get")
            .expect("local::get should be rendered");
        let set = rendered
            .iter()
            .find(|(name, _)| name == "local::set")
            .expect("local::set should be rendered");

        assert_eq!(run.1, "α -> β [local<α>; γ] -> [γ] β");
        assert_eq!(get.1, "unit -> [local<α>] α");
        assert_eq!(set.1, "α -> [local<α>] unit");
    }

    #[test]
    fn render_compact_results_resolves_struct_constructor_and_method() {
        let green = yulang_parser::parse_module_to_green(
            "struct point { x: int, y: int } with:\n  our p.width = p.x\n\nmy w = (point { x: 1, y: 2 }).width\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let w = rendered
            .iter()
            .find(|(name, _)| name == "w")
            .expect("w should be rendered");
        let width = rendered
            .iter()
            .find(|(name, _)| name == "point::width")
            .expect("point::width should be rendered");

        assert_eq!(w.1, "int");
        assert_eq!(width.1, "point -> int");
    }

    #[test]
    fn render_compact_results_widens_struct_method_through_constructor_fields() {
        let green = yulang_parser::parse_module_to_green(
            "struct point { x: float, y: float } with:\n  our p.width = p.x\n\nmy w = (point { x: 1, y: 2 }).width\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let w = rendered
            .iter()
            .find(|(name, _)| name == "w")
            .expect("w should be rendered");
        let width = rendered
            .iter()
            .find(|(name, _)| name == "point::width")
            .expect("point::width should be rendered");

        assert_eq!(w.1, "float");
        assert_eq!(width.1, "point -> float");
    }

    #[test]
    fn render_compact_results_lowers_struct_declarations_in_act_body() {
        let green = yulang_parser::parse_module_to_green(
            "act outer:\n  pub struct label { go: () -> [outer] never }\n\npub c = outer::label\npub f = outer::label::go\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let c = rendered
            .iter()
            .find(|(name, _)| name == "c")
            .expect("c should be rendered");
        let f = rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered");

        assert_eq!(c.1, "{go: unit -> [outer; ⊤] ⊤} -> outer::label");
        assert_eq!(f.1, "outer::label -> unit -> [outer] ⊥");
    }

    #[test]
    fn render_compact_results_keeps_frozen_struct_constructor_pure_across_owner_use() {
        let green = yulang_parser::parse_module_to_green(
            "act label_loop:\n  our last: () -> never\n  our next: () -> never\n  our redo: () -> never\n  pub struct label {\n    last: () -> [label_loop] never,\n    next: () -> [label_loop] never,\n    redo: () -> [label_loop] never\n  }\n  our mk() =\n    my lbl = label_loop::label {last: label_loop::last, next: label_loop::next, redo: label_loop::redo}\n    lbl\n\npub c = label_loop::label\npub m = label_loop::mk\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let c = rendered
            .iter()
            .find(|(name, _)| name == "c")
            .expect("c should be rendered");
        let m = rendered
            .iter()
            .find(|(name, _)| name == "m")
            .expect("m should be rendered");

        assert_eq!(
            c.1,
            "{last: unit -> [label_loop; ⊤] ⊤, next: unit -> [label_loop; ⊤] ⊤, redo: unit -> [label_loop; ⊤] ⊤} -> label_loop::label"
        );
        assert_eq!(m.1, "unit -> label_loop::label");
    }

    #[test]
    fn render_compact_results_widens_nested_record_fields() {
        let green = yulang_parser::parse_module_to_green(
            "my nested: {a: {x: float}, b: {y: float}} = {a: {x: 1}, b: {y: 2}}\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let nested = rendered
            .iter()
            .find(|(name, _)| name == "nested")
            .expect("nested should be rendered");

        assert_eq!(nested.1, "{a: {x: float}, b: {y: float}}");
    }

    #[test]
    fn render_compact_results_lowers_if_expression() {
        let green = yulang_parser::parse_module_to_green("my check x = if x { 1 } else 0\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let check = rendered
            .iter()
            .find(|(name, _)| name == "check")
            .expect("check should be rendered");

        assert_eq!(check.1, "bool -> int");
    }

    #[test]
    fn render_compact_results_lowers_mixed_numeric_if_expression() {
        let green = yulang_parser::parse_module_to_green("my x = if true { 1 } else { 2.0 }\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let x = rendered
            .iter()
            .find(|(name, _)| name == "x")
            .expect("x should be rendered");

        assert_eq!(x.1, "float");
    }

    #[test]
    fn render_compact_results_uses_nested_block_tail_type() {
        let green = yulang_parser::parse_module_to_green(
            "my id x =\n  my id x = x\n  id x\n\nmy id2 x =\n  my id x = x\n  id id x\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let id = rendered
            .iter()
            .find(|(name, _)| name == "id")
            .expect("id should be rendered");
        let id2 = rendered
            .iter()
            .find(|(name, _)| name == "id2")
            .expect("id2 should be rendered");

        assert_eq!(id.1, "α -> α");
        assert_eq!(id2.1, "α -> α");
    }

    #[test]
    fn render_compact_results_resolves_role_methods() {
        let green = yulang_parser::parse_module_to_green(
            "role Add 'a:\n  our a.add: 'a -> 'a\n\nmy pl a = a.add 1\nmy pl2 = Add::add 2 1\nmy pl3 = Add::add 1: Add::add 2 1\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let add = rendered
            .iter()
            .find(|(name, _)| name == "Add::add")
            .expect("Add::add should be rendered");
        let pl2 = rendered
            .iter()
            .find(|(name, _)| name == "pl2")
            .expect("pl2 should be rendered");
        let pl3 = rendered
            .iter()
            .find(|(name, _)| name == "pl3")
            .expect("pl3 should be rendered");
        let pl = rendered
            .iter()
            .find(|(name, _)| name == "pl")
            .expect("pl should be rendered");

        assert_eq!(add.1, "Add<α> => α -> α -> α");
        assert_eq!(pl.1, "Add<int | α> => α -> α | int");
        assert_eq!(pl2.1, "int");
        // pl3 はトップレベルで計算（`Add::add 1: ...`）が挟まり結果 var を量化できないため
        // 値制限の残差 α が残る（(b) 方針＝正直な主型を出し monomorphize 任せ）。
        assert_eq!(pl3.1, "α | int");
    }

    #[test]
    fn render_compact_results_resolves_role_methods_through_helper_binding() {
        let green = yulang_parser::parse_module_to_green(
            "role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             my plus1 x = Add::add x 1\n\
             my plus1_again x = plus1 x\n\
             my apply_plus1 x = plus1_again x\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let plus1 = rendered
            .iter()
            .find(|(name, _)| name == "plus1")
            .expect("plus1 should be rendered");
        let plus1_again = rendered
            .iter()
            .find(|(name, _)| name == "plus1_again")
            .expect("plus1_again should be rendered");
        let apply_plus1 = rendered
            .iter()
            .find(|(name, _)| name == "apply_plus1")
            .expect("apply_plus1 should be rendered");

        assert_eq!(plus1.1, "Add<int | α> => α -> α | int");
        assert_eq!(plus1_again.1, "Add<int | α> => α -> α | int");
        assert_eq!(apply_plus1.1, "Add<int | α> => α -> α | int");
    }

    #[test]
    fn render_compact_results_defaults_expansive_role_constraints_to_concrete_inputs() {
        let green = yulang_parser::parse_module_to_green(
            "role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             impl Add int;\n\
             my f() = Add::add 1 1\n\
             my plus1 x = Add::add x 1\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let f = rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered");
        let plus1 = rendered
            .iter()
            .find(|(name, _)| name == "plus1")
            .expect("plus1 should be rendered");

        assert_eq!(f.1, "unit -> int");
        assert_eq!(plus1.1, "Add<int | α> => α -> α | int");
    }

    #[test]
    fn render_compact_results_keeps_partial_role_application_open() {
        let green = yulang_parser::parse_module_to_green(
            "role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             impl Add int;\n\
             impl Add float;\n\
             my plus1 = Add::add 1\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let plus1 = rendered
            .iter()
            .find(|(name, _)| name == "plus1")
            .expect("plus1 should be rendered");

        assert_eq!(plus1.1, "Add<int | α> => α -> α | int");
    }

    #[test]
    fn render_compact_results_defaults_mixed_numeric_role_inputs_to_float() {
        let green = yulang_parser::parse_module_to_green(
            "role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             impl Add int;\n\
             impl Add float;\n\
             my f() = Add::add 1.0 2\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let f = rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered");

        assert_eq!(f.1, "unit -> float");
    }

    #[test]
    fn render_compact_results_resolves_concrete_role_constraints_through_impl_candidates() {
        let green = yulang_parser::parse_module_to_green(
            "role Display 'a:\n  our a.display: string\n\n\
             impl Display int;\n\
             my shown = 1.display\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let shown = rendered
            .iter()
            .find(|(name, _)| name == "shown")
            .expect("shown should be rendered");

        assert_eq!(shown.1, "std::str::str");
    }

    #[test]
    fn render_compact_results_hides_failed_concrete_role_constraints() {
        let green = yulang_parser::parse_module_to_green(
            "role Display 'a:\n  our a.display: string\n\n\
             my shown = 1.display\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let shown = rendered
            .iter()
            .find(|(name, _)| name == "shown")
            .expect("shown should be rendered");

        assert_eq!(shown.1, "std::str::str");
        assert!(state.infer.type_errors().iter().any(|error| matches!(
            error.kind,
            crate::diagnostic::TypeErrorKind::MissingImpl { .. }
        )));
    }

    #[test]
    fn render_compact_results_resolves_multi_arg_role_constraints_through_impl_candidates() {
        let green = yulang_parser::parse_module_to_green(
            "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index int bool:\n  type value = string\n\
             my shown: string = 1.index true\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let shown = rendered
            .iter()
            .find(|(name, _)| name == "shown")
            .expect("shown should be rendered");

        assert_eq!(shown.1, "std::str::str");
    }

    #[test]
    fn render_compact_results_resolves_associated_role_outputs_without_annotation() {
        let green = yulang_parser::parse_module_to_green(
            "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index int bool:\n  type value = string\n\
             my shown = 1.index true\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let shown = rendered
            .iter()
            .find(|(name, _)| name == "shown")
            .expect("shown should be rendered");

        assert_eq!(shown.1, "std::str::str");
    }

    #[test]
    fn format_role_constraint_arg_overlays_interval_bounds() {
        use crate::simplify::compact::{CompactBounds, CompactType};

        let a = fresh_type_var();
        let b = fresh_type_var();
        let c = fresh_type_var();
        let d = fresh_type_var();
        let e = fresh_type_var();
        let bounds = CompactBounds::Interval {
            self_var: None,
            lower: CompactType {
                vars: HashSet::from([a, b, c]),
                ..CompactType::default()
            },
            upper: CompactType {
                vars: HashSet::from([c, d, e]),
                ..CompactType::default()
            },
        };
        let mut namer = super::VarNamer::default();

        assert_eq!(
            super::format_role_constraint_arg(&bounds, &mut namer),
            "β | γ | α & δ & ε"
        );
    }

    #[test]
    fn format_compact_bounds_keeps_center_var_between_sides() {
        use crate::simplify::compact::{CompactBounds, CompactType};

        let a = fresh_type_var();
        let b = fresh_type_var();
        let c = fresh_type_var();
        let bounds = CompactBounds::Interval {
            self_var: Some(b),
            lower: CompactType {
                vars: HashSet::from([a, b]),
                ..CompactType::default()
            },
            upper: CompactType {
                vars: HashSet::from([b, c]),
                ..CompactType::default()
            },
        };
        let mut namer = super::VarNamer::default();

        assert_eq!(
            super::format_compact_bounds(&bounds, &mut namer),
            "β | α & γ"
        );
    }

    #[test]
    fn format_role_constraint_arg_keeps_center_var_between_sides() {
        use crate::simplify::compact::{CompactBounds, CompactType};

        let a = fresh_type_var();
        let b = fresh_type_var();
        let c = fresh_type_var();
        let bounds = CompactBounds::Interval {
            self_var: Some(b),
            lower: CompactType {
                vars: HashSet::from([a, b]),
                ..CompactType::default()
            },
            upper: CompactType {
                vars: HashSet::from([b, c]),
                ..CompactType::default()
            },
        };
        let mut namer = super::VarNamer::default();

        assert_eq!(
            super::format_role_constraint_arg(&bounds, &mut namer),
            "β | α & γ"
        );
    }

    #[test]
    fn render_compact_results_handles_annotated_recursive_catch() {
        let green = yulang_parser::parse_module_to_green(
            "act io:\n  our read: () -> int\n\nmy m(x: [io; e] _) = catch x:\n  io::read(), k -> j(k 0)\n\nmy j(x: [_] _) = catch x:\n  io::read(), k -> j(k 0)\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let m = rendered
            .iter()
            .find(|(name, _)| name == "m")
            .expect("m should be rendered");
        let j = rendered
            .iter()
            .find(|(name, _)| name == "j")
            .expect("j should be rendered");

        assert_eq!(j.1, "α [io; β] -> [β] α");
        assert_eq!(m.1, "α [io; β] -> [β] α");
    }

    #[test]
    fn render_compact_results_handles_ref_update_effect() {
        let green = yulang_parser::parse_module_to_green(
            "act ref_update 'a:\n  our update: 'a -> 'a\n\n\
             type ref 'e 'a with:\n  struct self:\n    get: () -> ['e] 'a\n    update_effect: () -> [ref_update 'a; 'e] ()\n  our r.update f =\n    my loop(x: [_] _) = catch x:\n      ref_update::update v, k -> loop(k f(v))\n    loop((r.update_effect)())\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let update = rendered
            .iter()
            .find(|(name, _)| name == "ref::update")
            .expect("ref::update should be rendered");

        // 残留は α・β の2変数のまま（`[α]` には畳まない）。これが principal 形:
        // α=残留, β=f の捕捉エフェクト(γ_f) は正極性でしか共起せず、β は f の型内に
        // 非対称な負極性出現を持つため、健全には統合できない（例: α=io, β=[io, undet]）。
        // 共変の join を自動計算しないので畳めないのが正しい挙動。
        assert_eq!(update.1, "ref<α & β, γ> -> (γ -> [β] γ) -> [α, β] unit");
    }

    // 既知の未解決（cooccur/coalesce 本丸・①の後に直す）。
    // notes/debugs/handler-queue-continuation-shape.md 参照。
    // handler が継続を queue に cons する型は、principal 形に単純化されるべき:
    //   - 継続を1本の `bool -> [β] α` に merge（現状は2本の union に分裂）
    //   - 余剰変数を cooccur で吸収（現状は `β &` / `γ &` が浮く）
    //   - 注釈 eff を入力行に残す（現状は `[δ & [; ε]]` で eff が item から落ちる）
    // 現状 actual: α [δ & [; ε]] -> (β & list<bool -> [δ | eff] α | γ & bool -> [eff] α>)
    //              -> [ε] β | list<bool -> [δ | eff] α | γ & bool -> [eff] α>
    // ①（ref_update over-merge）と同根（principal 形への着地失敗、症状は逆）。
    #[test]
    fn render_compact_results_consolidates_queued_handler_continuation() {
        let green = yulang_parser::parse_module_to_green(
            "type list 'a\npub cons(x: 'a, xs: list 'a): list 'a = xs\n\nmy act eff:\n    our op: () -> bool\n    our handle(x: [eff] 'a, queue: list (bool -> [eff] 'a)) = catch x:\n        op(), k -> cons(k, queue)\n        value -> queue\n\neff::handle\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let handle = rendered
            .iter()
            .find(|(name, _)| name == "eff::handle")
            .expect("eff::handle should be rendered");

        assert_eq!(
            handle.1,
            "α [β & [eff; γ]] -> list<bool -> [β] α> -> [γ] list<bool -> [β] α>"
        );
    }

    #[test]
    fn render_compact_results_preserves_concrete_ref_update_row_items() {
        let green = yulang_parser::parse_module_to_green(
            "act ref_update 'a:\n  our update: 'a -> 'a\n\n\
             type ref 'e 'a with:\n  struct self:\n    get: () -> ['e] 'a\n    update_effect: () -> [ref_update 'a; 'e] ()\n\n\
             struct str { value: int }\n\
             struct char { value: int }\n\
             my index_raw(s: str, i: int): char = char { value: i }\n\
             my to_string(c: char): str = str { value: c.value }\n\
             my splice(old: str, replacement: str): str = replacement\n\n\
             role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index (ref 'e str) int:\n  type value = ref 'e char\n  our r.index i = ref {\n    get: \\() -> index_raw (r.get()) i,\n    update_effect: \\() ->\n      my loop(x: [_] _) = catch x:\n        ref_update::update old, k ->\n          my new_item = ref_update::update (index_raw old i)\n          my replacement = to_string new_item\n          loop(k(splice old replacement))\n      loop((r.update_effect)())\n  }\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let _ = render_compact_results(&mut state);
        assert!(
            state.infer.type_errors().is_empty(),
            "{:#?}",
            state.infer.type_errors()
        );
    }

    #[test]
    fn render_compact_results_lowers_expr_do_notation() {
        let green =
            yulang_parser::parse_module_to_green("my id x = x\n\nmy a =\n  id(id do)\n  1\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let a = rendered
            .iter()
            .find(|(name, _)| name == "a")
            .expect("a should be rendered");

        assert_eq!(a.1, "int");
    }

    #[test]
    fn render_compact_results_lowers_binding_do_notation() {
        let green = yulang_parser::parse_module_to_green(
            "my f k = k 1\nmy g k = k\n\nmy a =\n  my x = f(g do)\n  x\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let a = rendered
            .iter()
            .find(|(name, _)| name == "a")
            .expect("a should be rendered");

        assert_eq!(a.1, "int");
    }

    #[test]
    fn render_compact_results_lowers_empty_do_suffix_to_unit() {
        let green = yulang_parser::parse_module_to_green("my id x = x\n\nmy a =\n  id(do)\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let a = rendered
            .iter()
            .find(|(name, _)| name == "a")
            .expect("a should be rendered");

        assert_eq!(a.1, "unit");
    }

    #[test]
    fn render_compact_results_lowers_brace_do_notation() {
        let green = yulang_parser::parse_module_to_green(
            "my f k = k 1\nmy g k = k\n\nmy a = { my x = f(g do); x }\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let a = rendered
            .iter()
            .find(|(name, _)| name == "a")
            .expect("a should be rendered");

        assert_eq!(a.1, "int");
    }

    #[test]
    fn render_compact_results_lowers_prelude_reexports_across_modules() {
        let mut state = LowerState::new();

        let index = SyntaxNode::<YulangLanguage>::new_root(yulang_parser::parse_module_to_green(
            "pub role Index 'container 'key 'value:\n  our index: 'container -> 'key -> 'value\n",
        ));
        lower_root_in_module(
            &mut state,
            &index,
            TirPath {
                segments: vec![TirName("std".to_string()), TirName("index".to_string())],
            },
        );

        let prelude = SyntaxNode::<YulangLanguage>::new_root(yulang_parser::parse_module_to_green(
            "pub use std::index::Index\npub id x = x\n",
        ));
        lower_root_in_module(
            &mut state,
            &prelude,
            TirPath {
                segments: vec![TirName("std".to_string()), TirName("prelude".to_string())],
            },
        );

        let entry = SyntaxNode::<YulangLanguage>::new_root(yulang_parser::parse_module_to_green(
            "use std::prelude::*\nmy a = id 1\nmy idx = Index::index\n",
        ));
        lower_root_in_module(&mut state, &entry, TirPath { segments: vec![] });
        finish_lowering(&mut state);

        let rendered = render_compact_results(&mut state);
        let a = rendered
            .iter()
            .find(|(name, _)| name == "a")
            .expect("prelude id should be visible");
        let idx = rendered
            .iter()
            .find(|(name, _)| name == "idx")
            .expect("prelude reexported Index module should be visible");

        assert_eq!(a.1, "int");
        assert!(idx.1.contains("Index<"));
    }

    #[test]
    fn render_compact_results_hides_generated_var_sigil_helpers() {
        let green =
            yulang_parser::parse_module_to_green("my read_var =\n  my ($x, y) = (12, 13)\n  $x\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);

        assert!(
            rendered.iter().any(|(name, _)| name == "read_var"),
            "top-level binding should stay observable",
        );
        assert!(
            rendered.iter().all(|(name, _)| !name.starts_with("&x::")),
            "generated var helper bindings should stay hidden: {rendered:?}",
        );
    }

    #[test]
    fn render_compact_results_keeps_local_function_value_capture() {
        let green = yulang_parser::parse_module_to_green("my run y =\n  my g x = y\n  g 1\n");
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let run = rendered
            .iter()
            .find(|(name, _)| name == "run")
            .expect("run should be rendered");

        assert_eq!(run.1, "α -> α");
    }

    #[test]
    fn render_compact_results_keeps_local_function_effect_capture() {
        let green = yulang_parser::parse_module_to_green(
            "act outer:\n  our redo: () -> never\n\n\
             my h(x: [_] _) = catch x:\n  outer::redo(), _ -> ()\n  _ -> ()\n\n\
             my run(f: () -> [outer] _) =\n  my g() = f()\n  h(g())\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let run = rendered
            .iter()
            .find(|(name, _)| name == "run")
            .expect("run should be rendered");

        assert_eq!(run.1, "(unit -> [outer; α] ⊤) -> [α] unit");
    }

    #[test]
    fn render_compact_results_with_our_helper_captures_outer_effect_param() {
        let green = yulang_parser::parse_module_to_green(
            "act outer:\n  our redo: () -> never\n  my act local:\n    our break: () -> never\n    our judge(x: [_] _) = catch x:\n      break(), _ -> true\n      _ -> false\n    our sub(x: [_] _) = catch x:\n      break(), _ -> ()\n      _ -> ()\n  my act repeat = local\n  our run(f: () -> [outer] _) = local::sub: loop true with:\n    our loop b = if b:\n      loop (repeat::judge:catch f():\n        redo(), _ -> repeat::break()\n        _ -> local::break()\n      )\n    else ()\n\npub r = outer::run\n",
        );
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);

        let rendered = render_compact_results(&mut state);
        let r = rendered
            .iter()
            .find(|(name, _)| name == "r")
            .expect("r should be rendered");

        assert_eq!(r.1, "(unit -> [outer; α] ⊤) -> [α] unit");
    }

    #[test]
    fn render_compact_results_lowers_for_in_stmt_to_loop_for_in() {
        run_with_large_stack(|| {
            let mut lowered = lower_virtual_std_source("pub run(xs) =\n  for x in xs:\n    ()\n");

            let rendered = render_compact_results(&mut lowered.state);
            let run = rendered
                .iter()
                .find(|(name, _)| name == "run")
                .expect("run should be rendered");

            assert_eq!(run.1, "Fold<α, item = β> => α -> unit");
        });
    }

    #[test]
    fn render_compact_results_lowers_for_in_ref_push_body() {
        run_with_large_stack(|| {
            let mut lowered = lower_virtual_std_source(
                "my test =\n  my $xs = []\n  for x in [1, 2, 3]:\n    &xs.push(x)\n  $xs\n",
            );

            let rendered = render_compact_results(&mut lowered.state);
            let test = rendered
                .iter()
                .find(|(name, _)| name == "test")
                .expect("test should be rendered");

            assert_eq!(test.1, "std::list::list<int>");
        });
    }

    #[test]
    fn render_compact_results_keeps_state_read_value_type() {
        run_with_large_stack(|| {
            let mut lowered = lower_virtual_std_source("my read_only =\n  my $a = 0\n  $a\n");

            let rendered = render_compact_results(&mut lowered.state);
            let read_only = rendered
                .iter()
                .find(|(name, _)| name == "read_only")
                .expect("read_only should be rendered");

            assert_eq!(read_only.1, "int");
        });
    }

    #[test]
    fn render_compact_results_lowers_direct_list_append() {
        run_with_large_stack(|| {
            let mut lowered =
                lower_virtual_std_source("my test =\n  my xs = []\n  std::list::append xs [1]\n");

            let rendered = render_compact_results(&mut lowered.state);
            let test = rendered
                .iter()
                .find(|(name, _)| name == "test")
                .expect("test should be rendered");

            assert_eq!(test.1, "std::list::list<int | α>");
        });
    }

    #[test]
    fn render_compact_results_lowers_list_expr_and_pattern_spread() {
        run_with_large_stack(|| {
            let mut lowered = lower_virtual_std_source(
                "my spread ys = [1, ..ys, 3]\n\
             my middle xs = case xs:\n  [head, ..middle, tail] -> middle\n  _ -> []\n",
            );

            let rendered = render_compact_results(&mut lowered.state);
            let spread = rendered
                .iter()
                .find(|(name, _)| name == "spread")
                .expect("spread should be rendered");
            let middle = rendered
                .iter()
                .find(|(name, _)| name == "middle")
                .expect("middle should be rendered");

            assert_eq!(
                spread.1,
                "std::list::list<int | α> -> std::list::list<int | α>"
            );
            assert_eq!(middle.1, "std::list::list<α> -> std::list::list<α>");
            let type_error_count = lowered.state.infer.type_errors().len();
            assert_eq!(type_error_count, 0);
        });
    }

    #[test]
    fn render_compact_results_lowers_labeled_for_in_stmt() {
        run_with_large_stack(|| {
            let mut lowered = lower_virtual_std_source(
                "my test =\n  for 'outer x in [1, 2, 3]:\n    'outer.next()\n\
             my nested =\n  for 'outer x in [1, 2, 3]:\n    for 'inner y in [4, 5, 6]:\n      redo 'inner\n    next 'outer\n",
            );

            let rendered = render_compact_results(&mut lowered.state);
            let test = rendered
                .iter()
                .find(|(name, _)| name == "test")
                .expect("test should be rendered");
            let nested = rendered
                .iter()
                .find(|(name, _)| name == "nested")
                .expect("nested should be rendered");

            assert_eq!(test.1, "unit");
            assert_eq!(nested.1, "unit");
            assert!(
                lowered.state.infer.type_errors().is_empty(),
                "{:#?}",
                lowered.state.infer.type_errors()
            );
            assert!(
                lowered.state.effect_args.keys().any(|path| path
                    .segments
                    .first()
                    .is_some_and(|name| name.0.starts_with("#loop_label:outer#"))),
                "outer loop label should get a synthetic act"
            );
            assert!(
                lowered.state.effect_args.keys().any(|path| path
                    .segments
                    .first()
                    .is_some_and(|name| name.0.starts_with("#loop_label:inner#"))),
                "inner loop label should get a separate synthetic act"
            );
        });
    }

    #[test]
    fn render_compact_results_lowers_loop_control_operators() {
        run_with_large_stack(|| {
            let mut lowered = lower_virtual_std_source(
                "my bare =\n  for x in [1, 2, 3]:\n    next\nmy labeled =\n  for 'outer x in [1, 2, 3]:\n    redo 'outer\npub for_in = std::flow::loop::for_in\n",
            );

            let rendered = render_compact_results(&mut lowered.state);
            let bare = rendered
                .iter()
                .find(|(name, _)| name == "bare")
                .expect("bare should be rendered");
            let labeled = rendered
                .iter()
                .find(|(name, _)| name == "labeled")
                .expect("labeled should be rendered");
            let for_in = rendered
                .iter()
                .find(|(name, _)| name == "for_in")
                .expect("for_in should be rendered");

            assert_eq!(bare.1, "unit");
            assert_eq!(labeled.1, "unit");
            assert_eq!(
                for_in.1,
                "Fold<α, item = β> => α -> (β -> [std::flow::loop; γ] ⊤) -> [γ] unit"
            );
        });
    }

    #[test]
    fn render_compact_results_lowers_sub_return_syntax() {
        run_with_large_stack(|| {
            let mut lowered = lower_virtual_std_source(
                "my plain = sub:\n  return 1\n\
             my labeled_field = sub 'outer:\n  'outer.return 1\n\
             my labeled_plain = sub 'outer:\n  return 2\n\
             my nested_field = sub 'outer:\n  sub 'inner:\n    'inner.return true\n  'outer.return 1\n\
             my nested_plain = sub 'outer:\n  sub 'inner:\n    return true\n  return 1\n",
            );

            let rendered = render_compact_results(&mut lowered.state);
            for name in [
                "plain",
                "labeled_field",
                "labeled_plain",
                "nested_field",
                "nested_plain",
            ] {
                let item = rendered
                    .iter()
                    .find(|(rendered_name, _)| rendered_name == name)
                    .expect("sub result should be rendered");
                assert_eq!(item.1, "int", "{name}");
            }
        });
    }
}
