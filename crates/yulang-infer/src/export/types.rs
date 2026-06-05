use std::collections::{BTreeSet, HashMap, HashSet};

use yulang_typed_ir as typed_ir;

use crate::FrozenScheme;
use crate::display::format::{
    Type as DisplayType, compact_scheme_to_type, materialize_effect_args,
};
use crate::ids::TypeVar;
use crate::simplify::compact::{
    CompactBounds, CompactType, CompactTypeScheme, compact_neg_expr, compact_pos_expr,
    merge_compact_bounds,
};
use crate::simplify::compact::{compact_type_var, compact_type_vars_in_order};
use crate::simplify::cooccur::{
    CompactRoleConstraint, coalesce_by_co_occurrence,
    coalesce_by_co_occurrence_with_role_constraints_report,
};
use crate::solve::Infer;
use crate::symbols::{Name, Path};
use crate::types::{EffectAtom, Neg, Pos, RecordField};

use super::names::{export_name, export_path};

pub fn export_scheme_body(scheme: &CompactTypeScheme) -> typed_ir::Type {
    let mut ctx = ExportTypeCtx::new(scheme);
    let display = compact_scheme_to_type(scheme);
    ctx.export_display_type(&display)
}

pub fn export_scheme_body_with_infer(infer: &Infer, scheme: &CompactTypeScheme) -> typed_ir::Type {
    let mut scheme = scheme.clone();
    materialize_effect_args(infer, &mut scheme);
    let mut ctx = ExportTypeCtx::new(&scheme);
    let display = compact_scheme_to_type(&scheme);
    ctx.export_display_type(&display)
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
        body: export_scheme_body_with_infer(infer, scheme),
    }
}

pub fn export_frozen_scheme(infer: &Infer, scheme: &FrozenScheme) -> typed_ir::Scheme {
    let compact = &scheme.compact;
    typed_ir::Scheme {
        requirements: Vec::new(),
        body: export_scheme_body_with_infer(infer, compact),
    }
}

pub fn export_frozen_scheme_body(scheme: &FrozenScheme) -> typed_ir::Scheme {
    typed_ir::Scheme {
        requirements: Vec::new(),
        body: export_frozen_pos(&scheme.arena, scheme.body),
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

pub fn export_direct_upper_fun_bounds_for_tv(
    infer: &Infer,
    tv: TypeVar,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> Option<typed_ir::TypeBounds> {
    infer.upper_refs_of(tv).into_iter().find_map(|upper| {
        let Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } = infer.arena.get_neg(upper)
        else {
            return None;
        };
        let param = export_required_compact_side_type(&compact_pos_expr(infer, arg), true);
        let param_effect =
            export_required_compact_side_type(&compact_pos_expr(infer, arg_eff), true);
        let ret_effect =
            export_required_compact_side_type(&compact_neg_expr(infer, ret_eff), false);
        let ret = export_required_compact_side_type(&compact_neg_expr(infer, ret), false);
        Some(typed_ir::TypeBounds {
            lower: None,
            upper: Some(Box::new(typed_ir::Type::Fun {
                param: Box::new(project_core_value_type_or_any(param, relevant_vars)),
                param_effect: Box::new(project_core_effect_type_or_any(
                    param_effect,
                    relevant_vars,
                )),
                ret_effect: Box::new(project_core_effect_type_or_any(ret_effect, relevant_vars)),
                ret: Box::new(project_core_value_type_or_any(ret, relevant_vars)),
            })),
        })
    })
}

fn export_required_compact_side_type(ty: &CompactType, positive: bool) -> typed_ir::Type {
    let scheme = CompactTypeScheme {
        cty: CompactBounds::default(),
        rec_vars: HashMap::new(),
    };
    let mut ctx = ExportTypeCtx::new(&scheme);
    ctx.export_required_compact_side(ty, positive)
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

fn export_type_bounds(scheme: &CompactTypeScheme, bounds: &CompactBounds) -> typed_ir::TypeBounds {
    let mut ctx = ExportTypeCtx::new(scheme);
    ctx.export_compact_bounds(bounds)
}

struct ExportTypeCtx {
    active_sides: HashMap<CompactSideKey, typed_ir::TypeVar>,
    recursive_sides: HashSet<CompactSideKey>,
}

impl ExportTypeCtx {
    fn new(_scheme: &CompactTypeScheme) -> Self {
        Self {
            active_sides: HashMap::new(),
            recursive_sides: HashSet::new(),
        }
    }

    fn export_display_type(&mut self, ty: &DisplayType) -> typed_ir::Type {
        self.export_display_type_raw(ty)
    }

    fn export_display_type_raw(&mut self, ty: &DisplayType) -> typed_ir::Type {
        let raw = match ty {
            DisplayType::Var(tv) => typed_ir::Type::Var(export_type_var(*tv)),
            DisplayType::Prim(path) => typed_ir::Type::Named {
                path: export_path(path),
                args: Vec::new(),
            },
            DisplayType::Con(path, args) => typed_ir::Type::Named {
                path: export_path(path),
                args: args.iter().map(|arg| self.export_type_arg(arg)).collect(),
            },
            DisplayType::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => typed_ir::Type::Fun {
                param: Box::new(self.export_display_type_raw(arg)),
                param_effect: Box::new(self.export_display_type_raw(arg_eff)),
                ret_effect: Box::new(self.export_display_type_raw(ret_eff)),
                ret: Box::new(self.export_display_type_raw(ret)),
            },
            DisplayType::Record(fields) => typed_ir::Type::Record(typed_ir::RecordType {
                fields: self.export_record_fields_raw(fields),
                spread: None,
            }),
            DisplayType::RecordTailSpread { fields, tail } => {
                typed_ir::Type::Record(typed_ir::RecordType {
                    fields: self.export_record_fields_raw(fields),
                    spread: Some(typed_ir::RecordSpread::Tail(Box::new(
                        self.export_display_type_raw(tail),
                    ))),
                })
            }
            DisplayType::RecordHeadSpread { tail, fields } => {
                typed_ir::Type::Record(typed_ir::RecordType {
                    fields: self.export_record_fields_raw(fields),
                    spread: Some(typed_ir::RecordSpread::Head(Box::new(
                        self.export_display_type_raw(tail),
                    ))),
                })
            }
            DisplayType::Variant(items) => typed_ir::Type::Variant(typed_ir::VariantType {
                cases: items
                    .iter()
                    .map(|(name, payloads)| typed_ir::VariantCase {
                        name: export_name(name),
                        payloads: payloads
                            .iter()
                            .map(|payload| self.export_display_type_raw(payload))
                            .collect(),
                    })
                    .collect(),
                tail: None,
            }),
            DisplayType::Tuple(items) => typed_ir::Type::Tuple(
                items
                    .iter()
                    .map(|item| self.export_display_type_raw(item))
                    .collect(),
            ),
            DisplayType::Row(items, tail) => typed_ir::Type::Row {
                items: items
                    .iter()
                    .map(|item| self.export_display_type_raw(item))
                    .collect(),
                tail: Box::new(self.export_display_type_raw(tail)),
            },
            DisplayType::Union(items) => typed_ir::Type::Union(
                items
                    .iter()
                    .map(|item| self.export_display_type_raw(item))
                    .collect(),
            ),
            DisplayType::Inter(items) => typed_ir::Type::Inter(
                items
                    .iter()
                    .map(|item| self.export_display_type_raw(item))
                    .collect(),
            ),
            DisplayType::Rec(tv, body) => typed_ir::Type::Recursive {
                var: export_type_var(*tv),
                body: Box::new(self.export_display_type_raw(body)),
            },
            DisplayType::Bot => typed_ir::Type::Never,
            DisplayType::Top => typed_ir::Type::Any,
        };
        raw
    }

    fn export_record_fields_raw(
        &mut self,
        fields: &[RecordField<DisplayType>],
    ) -> Vec<typed_ir::RecordField<typed_ir::Type>> {
        fields
            .iter()
            .map(|field| typed_ir::RecordField {
                name: export_name(&field.name),
                value: self.export_display_type_raw(&field.value),
                optional: field.optional,
            })
            .collect()
    }

    fn export_type_arg(&mut self, arg: &CompactBounds) -> typed_ir::TypeArg {
        let bounds = self.export_compact_bounds(arg);
        match (&bounds.lower, &bounds.upper) {
            (Some(lower), Some(upper)) if lower == upper => {
                typed_ir::TypeArg::Type((**lower).clone())
            }
            _ => typed_ir::TypeArg::Bounds(bounds),
        }
    }

    fn export_compact_bounds(&mut self, bounds: &CompactBounds) -> typed_ir::TypeBounds {
        typed_ir::TypeBounds {
            lower: self.export_compact_side(&bounds.lower, true).map(Box::new),
            upper: self.export_compact_side(&bounds.upper, false).map(Box::new),
        }
    }

    fn export_compact_side(&mut self, ty: &CompactType, positive: bool) -> Option<typed_ir::Type> {
        if compact_type_is_empty(ty) {
            return None;
        }

        let key = compact_side_key(ty, positive);
        if let Some(var) = self.active_sides.get(&key).cloned() {
            self.recursive_sides.insert(key);
            return Some(typed_ir::Type::Var(var));
        }

        let rec_var = typed_ir::TypeVar(format!("r{}", self.active_sides.len()));
        self.active_sides.insert(key.clone(), rec_var.clone());
        let body = self.export_compact_type_body(ty, positive);
        self.active_sides.remove(&key);

        let out = if self.recursive_sides.remove(&key) {
            typed_ir::Type::Recursive {
                var: rec_var,
                body: Box::new(body),
            }
        } else {
            body
        };
        Some(out)
    }

    fn export_required_compact_side(&mut self, ty: &CompactType, positive: bool) -> typed_ir::Type {
        self.export_compact_side(ty, positive)
            .unwrap_or_else(|| empty_compact_side_type(positive))
    }

    fn export_compact_var_side(&mut self, tv: TypeVar, _positive: bool) -> typed_ir::Type {
        typed_ir::Type::Var(export_type_var(tv))
    }

    fn export_compact_type_body(&mut self, ty: &CompactType, positive: bool) -> typed_ir::Type {
        let mut parts = Vec::new();

        let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
        vars.sort_by_key(|tv| tv.0);
        parts.extend(
            vars.into_iter()
                .map(|tv| self.export_compact_var_side(tv, positive)),
        );

        let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
        prims.sort_by_key(export_path_sort_key);
        parts.extend(prims.into_iter().map(|path| typed_ir::Type::Named {
            path: export_path(&path),
            args: Vec::new(),
        }));

        let mut cons = ty.cons.iter().collect::<Vec<_>>();
        cons.sort_by_key(|con| export_path_sort_key(&con.path));
        parts.extend(cons.into_iter().map(|con| {
            typed_ir::Type::Named {
                path: export_path(&con.path),
                args: con
                    .args
                    .iter()
                    .map(|arg| self.export_type_arg(arg))
                    .collect(),
            }
        }));

        parts.extend(ty.funs.iter().map(|fun| typed_ir::Type::Fun {
            param: Box::new(self.export_required_compact_side(&fun.arg, !positive)),
            param_effect: Box::new(self.export_required_compact_side(&fun.arg_eff, !positive)),
            ret_effect: Box::new(self.export_required_compact_side(&fun.ret_eff, positive)),
            ret: Box::new(self.export_required_compact_side(&fun.ret, positive)),
        }));

        parts.extend(ty.records.iter().map(|record| {
            typed_ir::Type::Record(typed_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| typed_ir::RecordField {
                        name: export_name(&field.name),
                        value: self.export_required_compact_side(&field.value, positive),
                        optional: field.optional,
                    })
                    .collect(),
                spread: None,
            })
        }));

        parts.extend(ty.record_spreads.iter().map(|spread| {
            typed_ir::Type::Record(typed_ir::RecordType {
                fields: spread
                    .fields
                    .iter()
                    .map(|field| typed_ir::RecordField {
                        name: export_name(&field.name),
                        value: self.export_required_compact_side(&field.value, positive),
                        optional: field.optional,
                    })
                    .collect(),
                spread: Some(if spread.tail_wins {
                    typed_ir::RecordSpread::Tail(Box::new(
                        self.export_required_compact_side(&spread.tail, positive),
                    ))
                } else {
                    typed_ir::RecordSpread::Head(Box::new(
                        self.export_required_compact_side(&spread.tail, positive),
                    ))
                }),
            })
        }));

        parts.extend(ty.variants.iter().map(|variant| {
            typed_ir::Type::Variant(typed_ir::VariantType {
                cases: variant
                    .items
                    .iter()
                    .map(|(name, payloads)| typed_ir::VariantCase {
                        name: export_name(name),
                        payloads: payloads
                            .iter()
                            .map(|payload| self.export_required_compact_side(payload, positive))
                            .collect(),
                    })
                    .collect(),
                tail: None,
            })
        }));

        parts.extend(ty.tuples.iter().map(|tuple| {
            typed_ir::Type::Tuple(
                tuple
                    .iter()
                    .map(|item| self.export_required_compact_side(item, positive))
                    .collect(),
            )
        }));

        parts.extend(ty.rows.iter().map(|row| {
            typed_ir::Type::Row {
                items: row
                    .items
                    .iter()
                    .map(|item| self.export_required_compact_side(item, positive))
                    .collect(),
                tail: Box::new(self.export_required_compact_side(&row.tail, positive)),
            }
        }));

        combine_export_parts(parts, positive)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CompactSideKey {
    ptr: usize,
    positive: bool,
}

fn compact_side_key(ty: &CompactType, positive: bool) -> CompactSideKey {
    CompactSideKey {
        ptr: ty as *const CompactType as usize,
        positive,
    }
}

fn empty_compact_side_type(positive: bool) -> typed_ir::Type {
    if positive {
        typed_ir::Type::Never
    } else {
        typed_ir::Type::Any
    }
}

fn combine_export_parts(mut parts: Vec<typed_ir::Type>, positive: bool) -> typed_ir::Type {
    parts.retain(|part| {
        !matches!(
            (positive, part),
            (true, typed_ir::Type::Never) | (false, typed_ir::Type::Any)
        )
    });
    parts.dedup();
    match parts.len() {
        0 => empty_compact_side_type(positive),
        1 => parts
            .into_iter()
            .next()
            .unwrap_or_else(|| empty_compact_side_type(positive)),
        _ if positive => typed_ir::Type::Union(parts),
        _ => typed_ir::Type::Inter(parts),
    }
}

fn export_path_sort_key(path: &Path) -> String {
    path.segments
        .iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn export_type_var(tv: crate::ids::TypeVar) -> typed_ir::TypeVar {
    typed_ir::TypeVar(format!("t{}", tv.0))
}

fn export_frozen_pos(
    arena: &crate::types::arena::TypeArena,
    id: crate::ids::PosId,
) -> typed_ir::Type {
    match arena.get_pos(id) {
        Pos::Bot => typed_ir::Type::Never,
        Pos::Var(tv) | Pos::Raw(tv) => typed_ir::Type::Var(export_type_var(tv)),
        Pos::Atom(atom) => export_frozen_effect_atom(atom),
        Pos::Forall(_, body) => export_frozen_pos(arena, body),
        Pos::Con(path, args) => typed_ir::Type::Named {
            path: export_path(&path),
            args: args
                .into_iter()
                .map(|(pos, neg)| export_frozen_type_arg(arena, pos, neg))
                .collect(),
        },
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(export_frozen_neg(arena, arg)),
            param_effect: Box::new(export_frozen_neg(arena, arg_eff)),
            ret_effect: Box::new(export_frozen_pos(arena, ret_eff)),
            ret: Box::new(export_frozen_pos(arena, ret)),
        },
        Pos::Record(fields) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: export_name(&field.name),
                    value: export_frozen_pos(arena, field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: None,
        }),
        Pos::RecordTailSpread { fields, tail } => typed_ir::Type::Record(typed_ir::RecordType {
            fields: fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: export_name(&field.name),
                    value: export_frozen_pos(arena, field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: Some(typed_ir::RecordSpread::Tail(Box::new(export_frozen_pos(
                arena, tail,
            )))),
        }),
        Pos::RecordHeadSpread { tail, fields } => typed_ir::Type::Record(typed_ir::RecordType {
            fields: fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: export_name(&field.name),
                    value: export_frozen_pos(arena, field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: Some(typed_ir::RecordSpread::Head(Box::new(export_frozen_pos(
                arena, tail,
            )))),
        }),
        Pos::PolyVariant(items) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: items
                .into_iter()
                .map(|(name, payloads)| typed_ir::VariantCase {
                    name: export_name(&name),
                    payloads: payloads
                        .into_iter()
                        .map(|payload| export_frozen_pos(arena, payload))
                        .collect(),
                })
                .collect(),
            tail: None,
        }),
        Pos::Tuple(items) => typed_ir::Type::Tuple(
            items
                .into_iter()
                .map(|item| export_frozen_pos(arena, item))
                .collect(),
        ),
        Pos::Row(items, tail) => typed_ir::Type::Row {
            items: items
                .into_iter()
                .map(|item| export_frozen_pos(arena, item))
                .collect(),
            tail: Box::new(export_frozen_pos(arena, tail)),
        },
        Pos::Union(lhs, rhs) => combine_export_parts(
            vec![export_frozen_pos(arena, lhs), export_frozen_pos(arena, rhs)],
            true,
        ),
    }
}

fn export_frozen_neg(
    arena: &crate::types::arena::TypeArena,
    id: crate::ids::NegId,
) -> typed_ir::Type {
    match arena.get_neg(id) {
        Neg::Top => typed_ir::Type::Any,
        Neg::Var(tv) => typed_ir::Type::Var(export_type_var(tv)),
        Neg::Atom(atom) => export_frozen_effect_atom(atom),
        Neg::Forall(_, body) => export_frozen_neg(arena, body),
        Neg::Con(path, args) => typed_ir::Type::Named {
            path: export_path(&path),
            args: args
                .into_iter()
                .map(|(pos, neg)| export_frozen_type_arg(arena, pos, neg))
                .collect(),
        },
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(export_frozen_pos(arena, arg)),
            param_effect: Box::new(export_frozen_pos(arena, arg_eff)),
            ret_effect: Box::new(export_frozen_neg(arena, ret_eff)),
            ret: Box::new(export_frozen_neg(arena, ret)),
        },
        Neg::Record(fields) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: export_name(&field.name),
                    value: export_frozen_neg(arena, field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: None,
        }),
        Neg::PolyVariant(items) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: items
                .into_iter()
                .map(|(name, payloads)| typed_ir::VariantCase {
                    name: export_name(&name),
                    payloads: payloads
                        .into_iter()
                        .map(|payload| export_frozen_neg(arena, payload))
                        .collect(),
                })
                .collect(),
            tail: None,
        }),
        Neg::Tuple(items) => typed_ir::Type::Tuple(
            items
                .into_iter()
                .map(|item| export_frozen_neg(arena, item))
                .collect(),
        ),
        Neg::Row(items, tail) => typed_ir::Type::Row {
            items: items
                .into_iter()
                .map(|item| export_frozen_neg(arena, item))
                .collect(),
            tail: Box::new(export_frozen_neg(arena, tail)),
        },
        Neg::Intersection(lhs, rhs) => combine_export_parts(
            vec![export_frozen_neg(arena, lhs), export_frozen_neg(arena, rhs)],
            false,
        ),
    }
}

fn export_frozen_effect_atom(atom: EffectAtom) -> typed_ir::Type {
    typed_ir::Type::Named {
        path: export_path(&atom.path),
        args: atom
            .args
            .into_iter()
            .map(|(pos, neg)| {
                let lower = typed_ir::Type::Var(export_type_var(pos));
                let upper = typed_ir::Type::Var(export_type_var(neg));
                if lower == upper {
                    typed_ir::TypeArg::Type(lower)
                } else {
                    typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                        lower: Some(Box::new(lower)),
                        upper: Some(Box::new(upper)),
                    })
                }
            })
            .collect(),
    }
}

fn export_frozen_type_arg(
    arena: &crate::types::arena::TypeArena,
    pos: crate::ids::PosId,
    neg: crate::ids::NegId,
) -> typed_ir::TypeArg {
    let lower = export_frozen_pos(arena, pos);
    let upper = export_frozen_neg(arena, neg);
    if lower == upper {
        typed_ir::TypeArg::Type(lower)
    } else {
        typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: Some(Box::new(lower)),
            upper: Some(Box::new(upper)),
        })
    }
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

fn compact_type_is_empty(ty: &CompactType) -> bool {
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

#[allow(dead_code)]
fn _export_name_for_assoc(name: &Name) -> typed_ir::Name {
    export_name(name)
}
