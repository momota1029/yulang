use std::collections::{BTreeSet, HashMap};

use yulang_typed_ir as typed_ir;
use yulang_typed_ir::normalize_union_members;

use crate::FrozenScheme;
use crate::display::format::{Type as DisplayType, compact_scheme_to_type, compact_side_to_type};
use crate::ids::TypeVar;
use crate::simplify::compact::{
    CompactBounds, CompactType, CompactTypeScheme, merge_compact_bounds,
};
use crate::simplify::compact::{compact_type_var, compact_type_vars_in_order};
use crate::simplify::cooccur::{
    CompactRoleConstraint, coalesce_by_co_occurrence,
    coalesce_by_co_occurrence_with_role_constraints_report,
};
use crate::solve::Infer;
use crate::symbols::{Name, Path};
use crate::types::RecordField;

use super::names::{export_name, export_path};

pub fn export_scheme_body(scheme: &CompactTypeScheme) -> typed_ir::Type {
    export_display_type(scheme, &compact_scheme_to_type(scheme))
}

pub fn export_scheme_body_type_vars(scheme: &CompactTypeScheme) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(&export_scheme_body(scheme), &mut vars);
    vars
}

pub fn export_scheme(
    infer: &Infer,
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> typed_ir::Scheme {
    let mut requirements = Vec::new();
    for constraint in constraints {
        let requirement = export_role_requirement(infer, scheme, constraint);
        if !requirements.contains(&requirement) {
            requirements.push(requirement);
        }
    }
    typed_ir::Scheme {
        requirements,
        body: export_scheme_body(scheme),
    }
}

pub fn export_frozen_scheme(_infer: &Infer, scheme: &FrozenScheme) -> typed_ir::Scheme {
    let compact = &scheme.compact;
    typed_ir::Scheme {
        requirements: Vec::new(),
        body: export_scheme_body(compact),
    }
}

pub fn export_frozen_scheme_body_type_vars(
    _infer: &Infer,
    scheme: &FrozenScheme,
) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(&export_scheme_body(&scheme.compact), &mut vars);
    vars
}

pub fn export_type_bounds_for_tv(infer: &Infer, tv: TypeVar) -> typed_ir::TypeBounds {
    let scheme = compact_type_var(infer, tv);
    export_type_bounds(&scheme, &scheme.cty)
}

pub fn export_compact_type_bounds(ty: &CompactType) -> typed_ir::TypeBounds {
    let scheme = CompactTypeScheme {
        cty: CompactBounds {
            self_var: None,
            lower: ty.clone(),
            upper: ty.clone(),
        },
        rec_vars: HashMap::new(),
    };
    export_type_bounds(&scheme, &scheme.cty)
}

pub fn export_type_bounds_for_tvs(
    infer: &Infer,
    tvs: &[TypeVar],
) -> HashMap<TypeVar, typed_ir::TypeBounds> {
    let schemes = compact_type_vars_in_order(infer, tvs);
    tvs.iter()
        .copied()
        .zip(schemes.iter())
        .map(|(tv, scheme)| (tv, export_type_bounds(scheme, &scheme.cty)))
        .collect()
}

pub fn extend_export_type_bounds_cache_for_tvs(
    infer: &Infer,
    tvs: &[TypeVar],
    cache: &mut HashMap<TypeVar, typed_ir::TypeBounds>,
) {
    let missing = tvs
        .iter()
        .copied()
        .filter(|tv| !cache.contains_key(tv))
        .collect::<Vec<_>>();
    if missing.is_empty() {
        return;
    }
    let schemes = compact_type_vars_in_order(infer, &missing);
    for (tv, scheme) in missing.into_iter().zip(schemes.iter()) {
        cache.insert(tv, export_type_bounds(scheme, &scheme.cty));
    }
}

pub fn export_coalesced_type_bounds_for_tvs(
    infer: &Infer,
    tvs: &[TypeVar],
) -> HashMap<TypeVar, typed_ir::TypeBounds> {
    let schemes = compact_type_vars_in_order(infer, tvs);
    tvs.iter()
        .copied()
        .zip(schemes.iter())
        .map(|(tv, scheme)| {
            let scheme = coalesce_by_co_occurrence(scheme);
            (tv, export_type_bounds(&scheme, &scheme.cty))
        })
        .collect()
}

pub fn export_coalesced_type_bounds_for_tv(infer: &Infer, tv: TypeVar) -> typed_ir::TypeBounds {
    let scheme = coalesce_by_co_occurrence(&compact_type_var(infer, tv));
    export_type_bounds(&scheme, &scheme.cty)
}

pub fn export_relevant_type_bounds_for_tv(
    infer: &Infer,
    tv: TypeVar,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::TypeBounds {
    let bounds = export_type_bounds_for_tv(infer, tv);
    project_type_bounds(bounds, relevant_vars)
}

pub fn export_relevant_type_bounds_for_tv_cached(
    infer: &Infer,
    tv: TypeVar,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
    cache: &mut HashMap<TypeVar, typed_ir::TypeBounds>,
) -> typed_ir::TypeBounds {
    let bounds = match cache.get(&tv) {
        Some(bounds) => bounds.clone(),
        None => {
            let bounds = export_type_bounds_for_tv(infer, tv);
            cache.insert(tv, bounds.clone());
            bounds
        }
    };
    project_type_bounds(bounds, relevant_vars)
}

pub fn export_coalesced_apply_evidence_bounds(
    infer: &Infer,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> (
    typed_ir::TypeBounds,
    typed_ir::TypeBounds,
    typed_ir::TypeBounds,
) {
    let schemes = compact_type_vars_in_order(infer, &[callee_tv, arg_tv, result_tv]);
    let mut rec_vars = HashMap::new();
    let mut cty = CompactBounds::default();
    for scheme in &schemes {
        cty = merge_compact_bounds(true, cty, scheme.cty.clone());
        rec_vars.extend(scheme.rec_vars.clone());
    }

    let evidence_constraint = CompactRoleConstraint {
        role: Path {
            segments: vec![Name("__apply_evidence".to_string())],
        },
        args: schemes.iter().map(|scheme| scheme.cty.clone()).collect(),
    };
    let host = CompactTypeScheme { cty, rec_vars };
    let output = coalesce_by_co_occurrence_with_role_constraints_report(
        &host,
        std::slice::from_ref(&evidence_constraint),
    );
    let args = output
        .constraints
        .iter()
        .find(|constraint| {
            constraint.role == evidence_constraint.role
                && constraint.args.len() == evidence_constraint.args.len()
        })
        .map(|constraint| constraint.args.as_slice())
        .unwrap_or(evidence_constraint.args.as_slice());

    (
        project_type_bounds(export_type_bounds(&output.scheme, &args[0]), relevant_vars),
        project_type_bounds(export_type_bounds(&output.scheme, &args[1]), relevant_vars),
        project_type_bounds(export_type_bounds(&output.scheme, &args[2]), relevant_vars),
    )
}

pub fn export_coalesced_apply_evidence_bounds_with_expected_arg(
    infer: &Infer,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    expected_arg_tv: TypeVar,
    result_tv: TypeVar,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> (
    typed_ir::TypeBounds,
    typed_ir::TypeBounds,
    typed_ir::TypeBounds,
    typed_ir::TypeBounds,
) {
    let schemes =
        compact_type_vars_in_order(infer, &[callee_tv, arg_tv, expected_arg_tv, result_tv]);
    let mut rec_vars = HashMap::new();
    let mut cty = CompactBounds::default();
    for scheme in &schemes {
        cty = merge_compact_bounds(true, cty, scheme.cty.clone());
        rec_vars.extend(scheme.rec_vars.clone());
    }

    let evidence_constraint = CompactRoleConstraint {
        role: Path {
            segments: vec![Name("__apply_evidence".to_string())],
        },
        args: schemes.iter().map(|scheme| scheme.cty.clone()).collect(),
    };
    let host = CompactTypeScheme { cty, rec_vars };
    let output = coalesce_by_co_occurrence_with_role_constraints_report(
        &host,
        std::slice::from_ref(&evidence_constraint),
    );
    let args = output
        .constraints
        .iter()
        .find(|constraint| {
            constraint.role == evidence_constraint.role
                && constraint.args.len() == evidence_constraint.args.len()
        })
        .map(|constraint| constraint.args.as_slice())
        .unwrap_or(evidence_constraint.args.as_slice());

    (
        project_type_bounds(export_type_bounds(&output.scheme, &args[0]), relevant_vars),
        project_type_bounds(export_type_bounds(&output.scheme, &args[1]), relevant_vars),
        project_type_bounds(export_type_bounds(&output.scheme, &args[2]), relevant_vars),
        project_type_bounds(export_type_bounds(&output.scheme, &args[3]), relevant_vars),
    )
}

pub fn export_coalesced_coerce_evidence_bounds(
    infer: &Infer,
    actual_tv: TypeVar,
    expected_tv: TypeVar,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> (typed_ir::TypeBounds, typed_ir::TypeBounds) {
    let schemes = compact_type_vars_in_order(infer, &[actual_tv, expected_tv]);
    let mut rec_vars = HashMap::new();
    let mut cty = CompactBounds::default();
    for scheme in &schemes {
        cty = merge_compact_bounds(true, cty, scheme.cty.clone());
        rec_vars.extend(scheme.rec_vars.clone());
    }

    let evidence_constraint = CompactRoleConstraint {
        role: Path {
            segments: vec![Name("__coerce_evidence".to_string())],
        },
        args: schemes.iter().map(|scheme| scheme.cty.clone()).collect(),
    };
    let host = CompactTypeScheme { cty, rec_vars };
    let output = coalesce_by_co_occurrence_with_role_constraints_report(
        &host,
        std::slice::from_ref(&evidence_constraint),
    );
    let args = output
        .constraints
        .iter()
        .find(|constraint| {
            constraint.role == evidence_constraint.role
                && constraint.args.len() == evidence_constraint.args.len()
        })
        .map(|constraint| constraint.args.as_slice())
        .unwrap_or(evidence_constraint.args.as_slice());

    (
        project_type_bounds(export_type_bounds(&output.scheme, &args[0]), relevant_vars),
        project_type_bounds(export_type_bounds(&output.scheme, &args[1]), relevant_vars),
    )
}

pub fn export_role_requirement(
    infer: &Infer,
    scheme: &CompactTypeScheme,
    constraint: &CompactRoleConstraint,
) -> typed_ir::RoleRequirement {
    let arg_infos = infer.role_arg_infos_of(&constraint.role);
    let args = constraint
        .args
        .iter()
        .enumerate()
        .map(|(index, arg)| match arg_infos.get(index) {
            Some(info) if !info.is_input => typed_ir::RoleRequirementArg::Associated {
                name: typed_ir::Name(info.name.clone()),
                bounds: export_type_bounds(scheme, arg),
            },
            _ => typed_ir::RoleRequirementArg::Input(export_type_bounds(scheme, arg)),
        })
        .collect();
    typed_ir::RoleRequirement {
        role: export_path(&constraint.role),
        args,
    }
}

fn export_display_type(scheme: &CompactTypeScheme, ty: &DisplayType) -> typed_ir::Type {
    let raw = match ty {
        DisplayType::Var(tv) => typed_ir::Type::Var(export_type_var(*tv)),
        DisplayType::Prim(path) => typed_ir::Type::Named {
            path: export_path(path),
            args: Vec::new(),
        },
        DisplayType::Con(path, args) => typed_ir::Type::Named {
            path: export_path(path),
            args: args
                .iter()
                .map(|arg| export_type_arg(scheme, arg))
                .collect(),
        },
        DisplayType::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(export_display_type(scheme, arg)),
            param_effect: Box::new(export_display_type(scheme, arg_eff)),
            ret_effect: Box::new(export_display_type(scheme, ret_eff)),
            ret: Box::new(export_display_type(scheme, ret)),
        },
        DisplayType::Record(fields) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: export_record_fields(scheme, fields),
            spread: None,
        }),
        DisplayType::RecordTailSpread { fields, tail } => {
            typed_ir::Type::Record(typed_ir::RecordType {
                fields: export_record_fields(scheme, fields),
                spread: Some(typed_ir::RecordSpread::Tail(Box::new(export_display_type(
                    scheme, tail,
                )))),
            })
        }
        DisplayType::RecordHeadSpread { tail, fields } => {
            typed_ir::Type::Record(typed_ir::RecordType {
                fields: export_record_fields(scheme, fields),
                spread: Some(typed_ir::RecordSpread::Head(Box::new(export_display_type(
                    scheme, tail,
                )))),
            })
        }
        DisplayType::Variant(items) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: items
                .iter()
                .map(|(name, payloads)| typed_ir::VariantCase {
                    name: export_name(name),
                    payloads: payloads
                        .iter()
                        .map(|payload| export_display_type(scheme, payload))
                        .collect(),
                })
                .collect(),
            tail: None,
        }),
        DisplayType::Tuple(items) => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| export_display_type(scheme, item))
                .collect(),
        ),
        DisplayType::Row(items, tail) => typed_ir::Type::Row {
            items: items
                .iter()
                .map(|item| export_display_type(scheme, item))
                .collect(),
            tail: Box::new(export_display_type(scheme, tail)),
        },
        DisplayType::Union(items) => typed_ir::Type::Union(
            items
                .iter()
                .map(|item| export_display_type(scheme, item))
                .collect(),
        ),
        DisplayType::Inter(items) => typed_ir::Type::Inter(
            items
                .iter()
                .map(|item| export_display_type(scheme, item))
                .collect(),
        ),
        DisplayType::Rec(tv, body) => typed_ir::Type::Recursive {
            var: export_type_var(*tv),
            body: Box::new(export_display_type(scheme, body)),
        },
        DisplayType::Bot => typed_ir::Type::Never,
        DisplayType::Top => typed_ir::Type::Any,
    };
    normalize_core_type(raw)
}

fn export_record_fields(
    scheme: &CompactTypeScheme,
    fields: &[RecordField<DisplayType>],
) -> Vec<typed_ir::RecordField<typed_ir::Type>> {
    fields
        .iter()
        .map(|field| typed_ir::RecordField {
            name: export_name(&field.name),
            value: export_display_type(scheme, &field.value),
            optional: field.optional,
        })
        .collect()
}

fn export_type_arg(scheme: &CompactTypeScheme, arg: &CompactBounds) -> typed_ir::TypeArg {
    let bounds = export_type_bounds(scheme, arg);
    match (&bounds.lower, &bounds.upper) {
        (Some(lower), Some(upper)) if lower == upper => typed_ir::TypeArg::Type((**lower).clone()),
        _ => typed_ir::TypeArg::Bounds(bounds),
    }
}

fn export_type_bounds(scheme: &CompactTypeScheme, bounds: &CompactBounds) -> typed_ir::TypeBounds {
    typed_ir::TypeBounds {
        lower: compact_side_option(scheme, &bounds.lower, true).map(Box::new),
        upper: compact_side_option(scheme, &bounds.upper, false).map(Box::new),
    }
}

fn compact_side_option(
    scheme: &CompactTypeScheme,
    ty: &CompactType,
    positive: bool,
) -> Option<typed_ir::Type> {
    (!is_empty_compact_type(ty)).then(|| {
        export_display_type(
            scheme,
            &compact_side_to_type(&scheme.rec_vars, ty, positive),
        )
    })
}

fn export_type_var(tv: crate::ids::TypeVar) -> typed_ir::TypeVar {
    typed_ir::TypeVar(format!("t{}", tv.0))
}

fn project_type_bounds(
    bounds: typed_ir::TypeBounds,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::TypeBounds {
    typed_ir::TypeBounds {
        lower: bounds
            .lower
            .and_then(|ty| project_core_type(*ty, relevant_vars).map(Box::new)),
        upper: bounds
            .upper
            .and_then(|ty| project_core_type(*ty, relevant_vars).map(Box::new)),
    }
}

fn project_core_type(
    ty: typed_ir::Type,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> Option<typed_ir::Type> {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => Some(ty),
        typed_ir::Type::Var(var) => relevant_vars
            .contains(&var)
            .then_some(typed_ir::Type::Var(var)),
        typed_ir::Type::Named { path, args } => Some(typed_ir::Type::Named {
            path,
            args: args
                .into_iter()
                .map(|arg| project_type_arg(arg, relevant_vars))
                .collect(),
        }),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => Some(typed_ir::Type::Fun {
            param: Box::new(project_core_value_type_or_any(*param, relevant_vars)),
            param_effect: Box::new(project_core_effect_type_or_any(
                *param_effect,
                relevant_vars,
            )),
            ret_effect: Box::new(project_core_effect_type_or_any(*ret_effect, relevant_vars)),
            ret: Box::new(project_core_value_type_or_any(*ret, relevant_vars)),
        }),
        typed_ir::Type::Tuple(items) => {
            let items = items
                .into_iter()
                .map(|item| project_core_value_type_or_any(item, relevant_vars))
                .collect::<Vec<_>>();
            (!items.is_empty()).then_some(typed_ir::Type::Tuple(items))
        }
        typed_ir::Type::Record(record) => {
            let fields = record
                .fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name,
                    value: project_core_value_type_or_any(field.value, relevant_vars),
                    optional: field.optional,
                })
                .collect::<Vec<_>>();
            let spread = record.spread.and_then(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => project_core_type(*ty, relevant_vars)
                    .map(|ty| typed_ir::RecordSpread::Head(Box::new(ty))),
                typed_ir::RecordSpread::Tail(ty) => project_core_type(*ty, relevant_vars)
                    .map(|ty| typed_ir::RecordSpread::Tail(Box::new(ty))),
            });
            (!fields.is_empty() || spread.is_some()).then_some(typed_ir::Type::Record(
                typed_ir::RecordType { fields, spread },
            ))
        }
        typed_ir::Type::Variant(variant) => {
            let cases = variant
                .cases
                .into_iter()
                .map(|case| {
                    let payloads = case
                        .payloads
                        .into_iter()
                        .map(|payload| project_core_value_type_or_any(payload, relevant_vars))
                        .collect::<Vec<_>>();
                    typed_ir::VariantCase {
                        name: case.name,
                        payloads,
                    }
                })
                .collect::<Vec<_>>();
            let tail = variant
                .tail
                .and_then(|tail| project_core_type(*tail, relevant_vars).map(Box::new));
            (!cases.is_empty() || tail.is_some()).then_some(typed_ir::Type::Variant(
                typed_ir::VariantType { cases, tail },
            ))
        }
        typed_ir::Type::Row { items, tail } => {
            let items = items
                .into_iter()
                .filter_map(|item| project_core_type(item, relevant_vars))
                .collect::<Vec<_>>();
            let tail = project_core_type(*tail, relevant_vars).unwrap_or(typed_ir::Type::Never);
            (!items.is_empty() || !matches!(tail, typed_ir::Type::Never)).then_some(
                typed_ir::Type::Row {
                    items,
                    tail: Box::new(tail),
                },
            )
        }
        typed_ir::Type::Union(items) => project_type_list(items, relevant_vars, true),
        typed_ir::Type::Inter(items) => project_type_list(items, relevant_vars, false),
        typed_ir::Type::Recursive { var, body } => {
            let body = project_core_type(*body, relevant_vars)?;
            Some(typed_ir::Type::Recursive {
                var,
                body: Box::new(body),
            })
        }
    }
}

pub(super) fn project_core_value_type_or_any(
    ty: typed_ir::Type,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::Type {
    project_core_type(ty, relevant_vars).unwrap_or(typed_ir::Type::Unknown)
}

fn project_core_effect_type_or_any(
    ty: typed_ir::Type,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::Type {
    project_core_type(ty, relevant_vars).unwrap_or(typed_ir::Type::Unknown)
}

fn project_type_arg(
    arg: typed_ir::TypeArg,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(
            project_core_type(ty, relevant_vars).unwrap_or(typed_ir::Type::Unknown),
        ),
        typed_ir::TypeArg::Bounds(bounds) => {
            let bounds = project_type_bounds(bounds, relevant_vars);
            match (&bounds.lower, &bounds.upper) {
                (Some(lower), Some(upper)) if lower == upper => {
                    typed_ir::TypeArg::Type((**lower).clone())
                }
                (None, None) => typed_ir::TypeArg::Type(typed_ir::Type::Unknown),
                _ => typed_ir::TypeArg::Bounds(bounds),
            }
        }
    }
}

fn project_type_list(
    items: Vec<typed_ir::Type>,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
    union: bool,
) -> Option<typed_ir::Type> {
    let mut projected = items
        .into_iter()
        .filter_map(|item| project_core_type(item, relevant_vars))
        .collect::<Vec<_>>();
    match projected.len() {
        0 => None,
        1 => projected.pop(),
        _ if union => Some(typed_ir::Type::Union(projected)),
        _ => Some(typed_ir::Type::Inter(projected)),
    }
}

pub(crate) fn collect_core_type_vars(ty: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        typed_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    typed_ir::TypeArg::Type(ty) => collect_core_type_vars(ty, vars),
                    typed_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = &bounds.lower {
                            collect_core_type_vars(lower, vars);
                        }
                        if let Some(upper) = &bounds.upper {
                            collect_core_type_vars(upper, vars);
                        }
                    }
                }
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_core_type_vars(param, vars);
            collect_core_type_vars(param_effect, vars);
            collect_core_type_vars(ret_effect, vars);
            collect_core_type_vars(ret, vars);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_core_type_vars(item, vars);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_core_type_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_core_type_vars(ty, vars);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_core_type_vars(payload, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_core_type_vars(tail, vars);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_core_type_vars(item, vars);
            }
            collect_core_type_vars(tail, vars);
        }
        typed_ir::Type::Recursive { body, .. } => collect_core_type_vars(body, vars),
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => {}
    }
}

fn is_empty_compact_type(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn normalize_core_type(ty: typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => ty,
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path,
            args: args
                .into_iter()
                .map(|arg| match arg {
                    typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(normalize_core_type(ty)),
                    typed_ir::TypeArg::Bounds(bounds) => {
                        typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                            lower: bounds.lower.map(|ty| Box::new(normalize_core_type(*ty))),
                            upper: bounds.upper.map(|ty| Box::new(normalize_core_type(*ty))),
                        })
                    }
                })
                .collect(),
        },
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(normalize_core_type(*param)),
            param_effect: Box::new(normalize_core_type(*param_effect)),
            ret_effect: Box::new(normalize_core_type(*ret_effect)),
            ret: Box::new(normalize_core_type(*ret)),
        },
        typed_ir::Type::Tuple(items) => {
            typed_ir::Type::Tuple(items.into_iter().map(normalize_core_type).collect())
        }
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name,
                    value: normalize_core_type(field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.map(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => {
                    typed_ir::RecordSpread::Head(Box::new(normalize_core_type(*ty)))
                }
                typed_ir::RecordSpread::Tail(ty) => {
                    typed_ir::RecordSpread::Tail(Box::new(normalize_core_type(*ty)))
                }
            }),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name,
                    payloads: case.payloads.into_iter().map(normalize_core_type).collect(),
                })
                .collect(),
            tail: variant
                .tail
                .map(|tail| Box::new(normalize_core_type(*tail))),
        }),
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items.into_iter().map(normalize_core_type).collect(),
            tail: Box::new(normalize_core_type(*tail)),
        },
        typed_ir::Type::Union(items) => normalize_union(items),
        typed_ir::Type::Inter(items) => {
            typed_ir::Type::Inter(items.into_iter().map(normalize_core_type).collect())
        }
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var,
            body: Box::new(normalize_core_type(*body)),
        },
    }
}

fn normalize_union(items: Vec<typed_ir::Type>) -> typed_ir::Type {
    let mut items = items
        .into_iter()
        .map(normalize_core_type)
        .flat_map(|item| match item {
            typed_ir::Type::Union(items) => items,
            other => vec![other],
        })
        .collect::<Vec<_>>();
    items = normalize_union_members(items);
    items.dedup();
    match items.len() {
        0 => typed_ir::Type::Never,
        1 => items.into_iter().next().unwrap_or(typed_ir::Type::Never),
        _ => typed_ir::Type::Union(items),
    }
}

#[allow(dead_code)]
fn _export_name_for_assoc(name: &Name) -> typed_ir::Name {
    export_name(name)
}
