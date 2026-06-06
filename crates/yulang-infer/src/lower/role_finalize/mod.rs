use std::collections::{HashMap, HashSet};

use crate::diagnostic::TypeOrigin;
use crate::ids::TypeVar;
use crate::lower::builtin_types::{
    join_primitive_type_paths, primitive_numeric_type_family, primitive_type_family,
};
use crate::simplify::compact::{
    CompactBounds, CompactType, CompactTypeScheme, compact_root_fun_body_lower,
    merge_compact_bounds, merge_compact_types,
};
use crate::simplify::cooccur::{
    CompactRoleConstraint, coalesce_by_co_occurrence_with_role_constraint_inputs,
    coalesce_by_co_occurrence_with_role_constraints, rewrite_scheme_with_subst,
    role_output_center_replacements,
};
use crate::solve::effect_row::normalize_rewritten_bounds;
use crate::solve::selection::{role_candidate_input_subst, select_most_specific_role_candidates};
use crate::symbols::Path;
use crate::types::Variance;

use super::LowerState;

mod alias;
mod finalize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RoleInputBoundary {
    Lower,
    Upper,
}

#[derive(Debug, Default)]
struct MainTypePolarity {
    positive: HashSet<TypeVar>,
    negative: HashSet<TypeVar>,
}

impl MainTypePolarity {
    fn insert(&mut self, tv: TypeVar, positive: bool) {
        if positive {
            self.positive.insert(tv);
        } else {
            self.negative.insert(tv);
        }
    }

    fn accepts_role_input_boundary(&self, tv: TypeVar, boundary: RoleInputBoundary) -> bool {
        match boundary {
            RoleInputBoundary::Lower => !self.negative.contains(&tv),
            RoleInputBoundary::Upper => !self.positive.contains(&tv),
        }
    }
}

fn role_input_concrete_type_for_target(
    bounds: &CompactBounds,
    target: Option<TypeVar>,
    main_polarity: &MainTypePolarity,
    allow_expansive_defaulting: bool,
) -> Option<CompactType> {
    if target.is_none() && !allow_expansive_defaulting {
        let mut vars = HashSet::new();
        collect_compact_bounds_vars(bounds, &mut vars);
        if vars
            .iter()
            .any(|tv| main_polarity.positive.contains(tv) || main_polarity.negative.contains(tv))
        {
            return None;
        }
    }
    let (boundary, concrete) = concrete_role_input_boundary(bounds)?;
    if let Some(target) = target
        && !main_polarity.accepts_role_input_boundary(target, boundary)
    {
        return None;
    }
    Some(concrete)
}

fn concrete_selected_role_input_types(
    original: &CompactRoleConstraint,
    resolved: &CompactRoleConstraint,
    indices: &[usize],
    main_polarity: &MainTypePolarity,
    allow_expansive_defaulting: bool,
) -> Option<Vec<CompactType>> {
    indices
        .iter()
        .map(|index| {
            let original_arg = original.args.get(*index)?;
            let resolved_arg = resolved.args.get(*index)?;
            let target =
                projection_target_var(original_arg).or_else(|| projection_target_var(resolved_arg));
            role_input_concrete_type_for_target(
                resolved_arg,
                target,
                main_polarity,
                allow_expansive_defaulting,
            )
        })
        .collect()
}

fn concrete_role_input_boundary(
    bounds: &CompactBounds,
) -> Option<(RoleInputBoundary, CompactType)> {
    single_boundary_concrete_type(bounds.lower())
        .map(|concrete| (RoleInputBoundary::Lower, concrete))
        .or_else(|| {
            single_boundary_concrete_type(bounds.upper())
                .map(|concrete| (RoleInputBoundary::Upper, concrete))
        })
}

fn single_boundary_concrete_type(ty: &CompactType) -> Option<CompactType> {
    let mut concrete = strip_compact_type_vars(ty);
    normalize_builtin_numeric_compact_type(&mut concrete);
    (concrete != CompactType::default()
        && is_concrete_compact_type(&concrete)
        && concrete_surface_count(&concrete) == 1)
        .then_some(concrete)
}

fn concrete_surface_count(ty: &CompactType) -> usize {
    let mut named = ty.prims.iter().cloned().collect::<HashSet<_>>();
    let mut count = ty.funs.len()
        + ty.records.len()
        + ty.record_spreads.len()
        + ty.variants.len()
        + ty.tuples.len()
        + ty.rows.len();
    for con in &ty.cons {
        if con.args.is_empty() {
            named.insert(con.path.clone());
        } else {
            count += 1;
        }
    }
    count + named.len()
}

fn main_type_polarity(
    scheme: &CompactTypeScheme,
    variance_of: &dyn Fn(&Path, usize) -> Variance,
) -> MainTypePolarity {
    let mut polarity = MainTypePolarity::default();
    let mut expanded = HashSet::new();
    if let Some(root_fun_body) = compact_root_fun_body_lower(scheme) {
        collect_type_main_type_polarity(
            &root_fun_body,
            true,
            SurfaceVarMode::DropAtConcreteSurface,
            scheme,
            variance_of,
            &mut expanded,
            &mut polarity,
        );
    } else {
        collect_type_main_type_polarity(
            scheme.cty.lower(),
            true,
            SurfaceVarMode::DropAtConcreteSurface,
            scheme,
            variance_of,
            &mut expanded,
            &mut polarity,
        );
    }
    polarity
}

fn collect_bounds_main_type_polarity(
    bounds: &CompactBounds,
    positive: bool,
    surface_vars: SurfaceVarMode,
    scheme: &CompactTypeScheme,
    variance_of: &dyn Fn(&Path, usize) -> Variance,
    expanded: &mut HashSet<(TypeVar, bool)>,
    polarity: &mut MainTypePolarity,
) {
    collect_type_main_type_polarity(
        bounds.lower(),
        positive,
        surface_vars,
        scheme,
        variance_of,
        expanded,
        polarity,
    );
    collect_type_main_type_polarity(
        bounds.upper(),
        !positive,
        surface_vars,
        scheme,
        variance_of,
        expanded,
        polarity,
    );
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SurfaceVarMode {
    DropAtConcreteSurface,
    KeepAtConcreteSurface,
}

fn collect_type_main_type_polarity(
    ty: &CompactType,
    positive: bool,
    surface_vars: SurfaceVarMode,
    scheme: &CompactTypeScheme,
    variance_of: &dyn Fn(&Path, usize) -> Variance,
    expanded: &mut HashSet<(TypeVar, bool)>,
    polarity: &mut MainTypePolarity,
) {
    if surface_vars == SurfaceVarMode::KeepAtConcreteSurface
        || !compact_type_has_non_var_surface(ty)
    {
        collect_main_type_root_vars(ty, positive, scheme, variance_of, expanded, polarity);
    }
    for con in &ty.cons {
        for (index, arg) in con.args.iter().enumerate() {
            let arg_positive = match variance_of(&con.path, index) {
                Variance::Invariant | Variance::Covariant => positive,
                Variance::Contravariant => !positive,
            };
            collect_bounds_main_type_polarity(
                arg,
                arg_positive,
                SurfaceVarMode::KeepAtConcreteSurface,
                scheme,
                variance_of,
                expanded,
                polarity,
            );
        }
    }
    for fun in &ty.funs {
        collect_type_main_type_polarity(
            &fun.arg,
            !positive,
            SurfaceVarMode::DropAtConcreteSurface,
            scheme,
            variance_of,
            expanded,
            polarity,
        );
        collect_type_main_type_polarity(
            &fun.arg_eff,
            !positive,
            SurfaceVarMode::DropAtConcreteSurface,
            scheme,
            variance_of,
            expanded,
            polarity,
        );
        collect_type_main_type_polarity(
            &fun.ret_eff,
            positive,
            SurfaceVarMode::DropAtConcreteSurface,
            scheme,
            variance_of,
            expanded,
            polarity,
        );
        collect_type_main_type_polarity(
            &fun.ret,
            positive,
            SurfaceVarMode::DropAtConcreteSurface,
            scheme,
            variance_of,
            expanded,
            polarity,
        );
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_type_main_type_polarity(
                &field.value,
                positive,
                SurfaceVarMode::DropAtConcreteSurface,
                scheme,
                variance_of,
                expanded,
                polarity,
            );
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_type_main_type_polarity(
                &field.value,
                positive,
                SurfaceVarMode::DropAtConcreteSurface,
                scheme,
                variance_of,
                expanded,
                polarity,
            );
        }
        collect_type_main_type_polarity(
            &spread.tail,
            positive,
            SurfaceVarMode::DropAtConcreteSurface,
            scheme,
            variance_of,
            expanded,
            polarity,
        );
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_type_main_type_polarity(
                    payload,
                    positive,
                    SurfaceVarMode::DropAtConcreteSurface,
                    scheme,
                    variance_of,
                    expanded,
                    polarity,
                );
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_type_main_type_polarity(
                item,
                positive,
                SurfaceVarMode::DropAtConcreteSurface,
                scheme,
                variance_of,
                expanded,
                polarity,
            );
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_type_main_type_polarity(
                item,
                positive,
                SurfaceVarMode::DropAtConcreteSurface,
                scheme,
                variance_of,
                expanded,
                polarity,
            );
        }
        collect_type_main_type_polarity(
            &row.tail,
            positive,
            SurfaceVarMode::DropAtConcreteSurface,
            scheme,
            variance_of,
            expanded,
            polarity,
        );
    }
}

fn collect_main_type_root_vars(
    ty: &CompactType,
    positive: bool,
    scheme: &CompactTypeScheme,
    variance_of: &dyn Fn(&Path, usize) -> Variance,
    expanded: &mut HashSet<(TypeVar, bool)>,
    polarity: &mut MainTypePolarity,
) {
    for &tv in &ty.vars {
        polarity.insert(tv, positive);
        if expanded.insert((tv, positive))
            && let Some(bounds) = scheme.rec_vars.get(&tv)
        {
            let recur = if positive {
                bounds.lower()
            } else {
                bounds.upper()
            };
            collect_type_main_type_polarity(
                recur,
                positive,
                SurfaceVarMode::DropAtConcreteSurface,
                scheme,
                variance_of,
                expanded,
                polarity,
            );
        }
    }
}

fn constructor_arg_variance(infer: &crate::solve::Infer, path: &Path, index: usize) -> Variance {
    infer
        .variances
        .get(path)
        .and_then(|items| items.get(index))
        .copied()
        .unwrap_or(Variance::Invariant)
}

fn compact_type_has_non_var_surface(ty: &CompactType) -> bool {
    !ty.prims.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
}

fn concrete_bounds_repr(bounds: &CompactBounds, allow_boundary: bool) -> Option<CompactType> {
    let lower_empty = bounds.lower() == &CompactType::default();
    let upper_empty = bounds.upper() == &CompactType::default();
    match (lower_empty, upper_empty) {
        (false, true) => concrete_or_boundary_compact_type(bounds.lower(), allow_boundary),
        (true, false) => concrete_or_boundary_compact_type(bounds.upper(), allow_boundary),
        (false, false) if bounds.lower() == bounds.upper() => {
            concrete_or_boundary_compact_type(bounds.lower(), allow_boundary)
        }
        (false, false) if allow_boundary => {
            boundary_join_concrete_bounds(bounds.lower(), bounds.upper())
                .or_else(|| boundary_concrete_compact_type(bounds.lower()))
                .or_else(|| boundary_concrete_compact_type(bounds.upper()))
        }
        _ => None,
    }
}

fn concrete_or_boundary_compact_type(
    ty: &CompactType,
    allow_boundary: bool,
) -> Option<CompactType> {
    if allow_boundary {
        boundary_concrete_compact_type(ty)
    } else if is_concrete_compact_type(ty) {
        Some(ty.clone())
    } else {
        None
    }
}

fn boundary_concrete_compact_type(ty: &CompactType) -> Option<CompactType> {
    if is_concrete_compact_type(ty) {
        let mut normalized = ty.clone();
        normalize_builtin_numeric_compact_type(&mut normalized);
        return Some(normalized);
    }
    let mut stripped = strip_compact_type_vars(ty);
    normalize_builtin_numeric_compact_type(&mut stripped);
    (stripped != CompactType::default() && is_concrete_compact_type(&stripped)).then_some(stripped)
}

fn boundary_join_concrete_bounds(lower: &CompactType, upper: &CompactType) -> Option<CompactType> {
    let lower = boundary_concrete_compact_type(lower)?;
    let upper = boundary_concrete_compact_type(upper)?;
    if lower == upper {
        return Some(lower);
    }
    let lower_path = single_primitive_path(&lower)?;
    let upper_path = single_primitive_path(&upper)?;
    let joined_path = join_primitive_type_paths(lower_path, upper_path)?;
    let mut joined = CompactType::default();
    joined.cons.push(crate::simplify::compact::CompactCon {
        path: joined_path,
        args: Vec::new(),
    });
    Some(joined)
}

fn strip_compact_type_vars(ty: &CompactType) -> CompactType {
    CompactType {
        vars: Default::default(),
        prims: ty.prims.clone(),
        cons: ty
            .cons
            .iter()
            .map(|con| crate::simplify::compact::CompactCon {
                path: con.path.clone(),
                args: con
                    .args
                    .iter()
                    .map(|arg| CompactBounds::Interval {
                        self_var: None,
                        lower: strip_compact_type_vars(arg.lower()),
                        upper: strip_compact_type_vars(arg.upper()),
                    })
                    .collect(),
            })
            .collect(),
        funs: ty
            .funs
            .iter()
            .map(|fun| crate::simplify::compact::CompactFun {
                arg: strip_compact_type_vars(&fun.arg),
                arg_eff: strip_compact_type_vars(&fun.arg_eff),
                ret_eff: strip_compact_type_vars(&fun.ret_eff),
                ret: strip_compact_type_vars(&fun.ret),
            })
            .collect(),
        records: ty
            .records
            .iter()
            .map(|record| crate::simplify::compact::CompactRecord {
                fields: record
                    .fields
                    .iter()
                    .map(|field| crate::types::RecordField {
                        name: field.name.clone(),
                        value: strip_compact_type_vars(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
            })
            .collect(),
        record_spreads: ty
            .record_spreads
            .iter()
            .map(|spread| crate::simplify::compact::CompactRecordSpread {
                fields: spread
                    .fields
                    .iter()
                    .map(|field| crate::types::RecordField {
                        name: field.name.clone(),
                        value: strip_compact_type_vars(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(strip_compact_type_vars(&spread.tail)),
                tail_wins: spread.tail_wins,
            })
            .collect(),
        variants: ty
            .variants
            .iter()
            .map(|variant| crate::simplify::compact::CompactVariant {
                items: variant
                    .items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads.iter().map(strip_compact_type_vars).collect(),
                        )
                    })
                    .collect(),
            })
            .collect(),
        tuples: ty
            .tuples
            .iter()
            .map(|tuple| tuple.iter().map(strip_compact_type_vars).collect())
            .collect(),
        rows: ty
            .rows
            .iter()
            .map(|row| crate::simplify::compact::CompactRow {
                items: row.items.iter().map(strip_compact_type_vars).collect(),
                tail: Box::new(strip_compact_type_vars(&row.tail)),
            })
            .collect(),
    }
}

fn is_concrete_compact_type(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.cons.iter().all(|con| {
            con.args
                .iter()
                .all(|arg| arg.self_var().is_none() && concrete_bounds_repr(arg, false).is_some())
        })
        && ty.funs.iter().all(|fun| {
            is_concrete_compact_type(&fun.arg)
                && is_concrete_compact_type(&fun.arg_eff)
                && is_concrete_compact_type(&fun.ret_eff)
                && is_concrete_compact_type(&fun.ret)
        })
        && ty.records.iter().all(|record| {
            record
                .fields
                .iter()
                .all(|field| is_concrete_compact_type(&field.value))
        })
        && ty.record_spreads.iter().all(|spread| {
            spread
                .fields
                .iter()
                .all(|field| is_concrete_compact_type(&field.value))
                && is_concrete_compact_type(&spread.tail)
        })
        && ty.variants.iter().all(|variant| {
            variant
                .items
                .iter()
                .all(|(_, payloads)| payloads.iter().all(is_concrete_compact_type))
        })
        && ty
            .tuples
            .iter()
            .all(|tuple| tuple.iter().all(is_concrete_compact_type))
        && ty.rows.iter().all(|row| {
            row.items.iter().all(is_concrete_compact_type) && is_concrete_compact_type(&row.tail)
        })
}

fn normalize_builtin_numeric_compact_type(ty: &mut CompactType) {
    normalize_named_compact_type_order(ty);
    for con in &mut ty.cons {
        for arg in &mut con.args {
            normalize_builtin_numeric_compact_type(arg.lower_mut());
            normalize_builtin_numeric_compact_type(arg.upper_mut());
        }
    }
    for fun in &mut ty.funs {
        normalize_builtin_numeric_compact_type(&mut fun.arg);
        normalize_builtin_numeric_compact_type(&mut fun.arg_eff);
        normalize_builtin_numeric_compact_type(&mut fun.ret_eff);
        normalize_builtin_numeric_compact_type(&mut fun.ret);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            normalize_builtin_numeric_compact_type(&mut field.value);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            normalize_builtin_numeric_compact_type(&mut field.value);
        }
        normalize_builtin_numeric_compact_type(&mut spread.tail);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                normalize_builtin_numeric_compact_type(payload);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            normalize_builtin_numeric_compact_type(item);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            normalize_builtin_numeric_compact_type(item);
        }
        normalize_builtin_numeric_compact_type(&mut row.tail);
    }
}

fn normalize_named_compact_type_order(ty: &mut CompactType) {
    let joined = ty
        .prims
        .iter()
        .cloned()
        .chain(
            ty.cons
                .iter()
                .filter(|con| con.args.is_empty())
                .map(|con| con.path.clone()),
        )
        .fold(Vec::<crate::symbols::Path>::new(), |mut out, path| {
            if let Some(index) = out
                .iter()
                .position(|existing| join_local_named_paths(existing, &path).is_some())
            {
                let joined = join_local_named_paths(&out[index], &path).expect("checked above");
                out[index] = joined;
            } else {
                out.push(path);
            }
            out
        });

    ty.prims
        .retain(|path| joined.iter().any(|joined_path| joined_path == path));
    ty.cons.retain(|con| {
        !con.args.is_empty() || joined.iter().any(|joined_path| joined_path == &con.path)
    });
    for joined_path in joined {
        let exists_as_prim = ty.prims.iter().any(|path| path == &joined_path);
        let exists_as_con = ty
            .cons
            .iter()
            .any(|con| con.args.is_empty() && con.path == joined_path);
        if !exists_as_prim && !exists_as_con {
            ty.cons.push(crate::simplify::compact::CompactCon {
                path: joined_path,
                args: Vec::new(),
            });
        }
    }
}

fn join_local_named_paths(left: &Path, right: &Path) -> Option<Path> {
    if left == right {
        return Some(left.clone());
    }
    join_primitive_type_paths(left, right)
}

fn single_primitive_path(ty: &CompactType) -> Option<&Path> {
    if !ty.vars.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
    {
        return None;
    }
    let mut paths = ty.prims.iter().chain(
        ty.cons
            .iter()
            .filter(|con| con.args.is_empty())
            .map(|con| &con.path),
    );
    let path = paths.next()?;
    paths.next().is_none().then_some(path).filter(|path| {
        primitive_numeric_type_family(path).is_some() || primitive_type_family(path).is_some()
    })
}

fn path_string(path: &Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.clone())
        .collect::<Vec<_>>()
        .join("::")
}

fn role_constraint_arg_indices(
    infos: &[crate::solve::RoleArgInfo],
    arg_len: usize,
) -> (Vec<usize>, Vec<usize>) {
    if infos.len() != arg_len {
        return ((0..arg_len).collect(), Vec::new());
    }
    let mut input = Vec::new();
    let mut output = Vec::new();
    for (index, info) in infos.iter().enumerate() {
        if info.is_input {
            input.push(index);
        } else {
            output.push(index);
        }
    }
    if input.is_empty() {
        ((0..arg_len).collect(), Vec::new())
    } else {
        (input, output)
    }
}

fn render_selected_concrete_args(
    constraint: &CompactRoleConstraint,
    indices: &[usize],
    allow_boundary: bool,
) -> Option<Vec<String>> {
    indices
        .iter()
        .map(|index| {
            let arg = constraint.args.get(*index)?;
            let concrete = concrete_bounds_repr(arg, allow_boundary)?;
            Some(render_concrete_compact_type(&concrete))
        })
        .collect()
}

fn render_role_constraint_args_for_diagnostic(
    constraint: &CompactRoleConstraint,
    output_indices: &[usize],
    arg_infos: &[crate::solve::RoleArgInfo],
) -> Vec<String> {
    constraint
        .args
        .iter()
        .enumerate()
        .map(|(index, arg)| {
            let rendered = concrete_bounds_repr(arg, true)
                .map(|concrete| render_concrete_compact_type(&concrete))
                .unwrap_or_else(|| crate::display::dump::format_compact_role_constraint_arg(arg));
            if output_indices.contains(&index) && index < arg_infos.len() {
                format!("{} = {}", arg_infos[index].name, rendered)
            } else {
                rendered
            }
        })
        .collect()
}

fn concrete_selected_input_types(
    constraint: &CompactRoleConstraint,
    indices: &[usize],
    allow_boundary: bool,
) -> Option<Vec<CompactType>> {
    indices
        .iter()
        .map(|index| {
            let arg = constraint.args.get(*index)?;
            concrete_bounds_repr(arg, allow_boundary)
        })
        .collect()
}

fn expand_role_constraint_with_scheme_bounds(
    constraint: &CompactRoleConstraint,
    scheme: &CompactTypeScheme,
) -> CompactRoleConstraint {
    let mut ctx = SchemeBoundsExpansion::new(scheme);
    CompactRoleConstraint {
        role: constraint.role.clone(),
        args: constraint
            .args
            .iter()
            .map(|arg| ctx.expand_bounds(arg))
            .collect(),
    }
}

struct SchemeBoundsExpansion<'a> {
    scheme: &'a CompactTypeScheme,
    in_progress: HashSet<(TypeVar, bool)>,
    cache: HashMap<(TypeVar, bool), CompactType>,
}

impl<'a> SchemeBoundsExpansion<'a> {
    fn new(scheme: &'a CompactTypeScheme) -> Self {
        Self {
            scheme,
            in_progress: HashSet::new(),
            cache: HashMap::new(),
        }
    }

    fn expand_type(&mut self, ty: &CompactType, positive: bool) -> CompactType {
        let mut out = CompactType {
            vars: ty.vars.clone(),
            prims: ty.prims.clone(),
            cons: ty
                .cons
                .iter()
                .map(|con| crate::simplify::compact::CompactCon {
                    path: con.path.clone(),
                    args: con.args.iter().map(|arg| self.expand_bounds(arg)).collect(),
                })
                .collect(),
            funs: ty
                .funs
                .iter()
                .map(|fun| crate::simplify::compact::CompactFun {
                    arg: self.expand_type(&fun.arg, !positive),
                    arg_eff: self.expand_type(&fun.arg_eff, !positive),
                    ret_eff: self.expand_type(&fun.ret_eff, positive),
                    ret: self.expand_type(&fun.ret, positive),
                })
                .collect(),
            records: ty
                .records
                .iter()
                .map(|record| crate::simplify::compact::CompactRecord {
                    fields: record
                        .fields
                        .iter()
                        .map(|field| crate::types::RecordField {
                            name: field.name.clone(),
                            value: self.expand_type(&field.value, positive),
                            optional: field.optional,
                        })
                        .collect(),
                })
                .collect(),
            record_spreads: ty
                .record_spreads
                .iter()
                .map(|spread| crate::simplify::compact::CompactRecordSpread {
                    fields: spread
                        .fields
                        .iter()
                        .map(|field| crate::types::RecordField {
                            name: field.name.clone(),
                            value: self.expand_type(&field.value, positive),
                            optional: field.optional,
                        })
                        .collect(),
                    tail: Box::new(self.expand_type(&spread.tail, positive)),
                    tail_wins: spread.tail_wins,
                })
                .collect(),
            variants: ty
                .variants
                .iter()
                .map(|variant| crate::simplify::compact::CompactVariant {
                    items: variant
                        .items
                        .iter()
                        .map(|(name, payloads)| {
                            (
                                name.clone(),
                                payloads
                                    .iter()
                                    .map(|payload| self.expand_type(payload, positive))
                                    .collect(),
                            )
                        })
                        .collect(),
                })
                .collect(),
            tuples: ty
                .tuples
                .iter()
                .map(|tuple| {
                    tuple
                        .iter()
                        .map(|item| self.expand_type(item, positive))
                        .collect()
                })
                .collect(),
            rows: ty
                .rows
                .iter()
                .map(|row| crate::simplify::compact::CompactRow {
                    items: row
                        .items
                        .iter()
                        .map(|item| self.expand_type(item, positive))
                        .collect(),
                    tail: Box::new(self.expand_type(&row.tail, positive)),
                })
                .collect(),
        };

        for var in &ty.vars {
            if let Some(expanded) = self.expand_rec_var(*var, positive) {
                out = merge_compact_types(positive, out, expanded);
            }
        }
        normalize_builtin_numeric_compact_type(&mut out);
        out
    }

    fn expand_bounds(&mut self, bounds: &CompactBounds) -> CompactBounds {
        normalize_rewritten_bounds(CompactBounds::Interval {
            self_var: bounds.self_var(),
            lower: self.expand_type(bounds.lower(), true),
            upper: self.expand_type(bounds.upper(), false),
        })
    }

    fn expand_rec_var(&mut self, var: TypeVar, positive: bool) -> Option<CompactType> {
        let bounds = self.scheme.rec_vars.get(&var)?;
        let key = (var, positive);
        if let Some(cached) = self.cache.get(&key) {
            return Some(cached.clone());
        }
        if !self.in_progress.insert(key) {
            // Recursive compact schemes keep cycles as rec_vars; expansion should expose
            // the surrounding bounds without unrolling the same polarized edge forever.
            return Some(CompactType {
                vars: [var].into_iter().collect(),
                ..CompactType::default()
            });
        }
        let expanded = if positive {
            self.expand_type(bounds.lower(), positive)
        } else {
            self.expand_type(bounds.upper(), positive)
        };
        self.in_progress.remove(&key);
        self.cache.insert(key, expanded.clone());
        Some(expanded)
    }
}

fn render_concrete_compact_type(ty: &CompactType) -> String {
    crate::display::dump::format_compact_role_constraint_arg(&CompactBounds::Interval {
        self_var: None,
        lower: ty.clone(),
        upper: CompactType::default(),
    })
}

fn role_candidate_previews(candidates: Vec<&crate::solve::RoleImplCandidate>) -> Vec<String> {
    candidates
        .into_iter()
        .map(render_role_candidate_preview)
        .collect()
}

fn render_role_candidate_preview(candidate: &crate::solve::RoleImplCandidate) -> String {
    format!(
        "{}<{}>",
        path_string(&candidate.role),
        candidate.args.join(", ")
    )
}

#[derive(Debug, Clone)]
enum RoleCandidatePrerequisiteStatus {
    Satisfied,
    MissingImpl {
        role: String,
        args: Vec<String>,
        origins: Vec<TypeOrigin>,
    },
    AmbiguousImpl {
        role: String,
        args: Vec<String>,
        candidates: usize,
        previews: Vec<String>,
        origins: Vec<TypeOrigin>,
    },
    Unresolved,
}

fn role_candidate_prerequisite_status(
    infer: &crate::solve::Infer,
    candidate: &crate::solve::RoleImplCandidate,
    subst: &HashMap<TypeVar, CompactType>,
    stack: &mut Vec<(String, Vec<String>)>,
) -> RoleCandidatePrerequisiteStatus {
    if candidate.prerequisites.is_empty() {
        return RoleCandidatePrerequisiteStatus::Satisfied;
    }

    let key = (
        path_string(&candidate.role),
        candidate
            .compact_args
            .iter()
            .map(|arg| render_concrete_compact_type(&apply_candidate_subst_to_type(arg, subst)))
            .collect(),
    );
    if stack.contains(&key) {
        return RoleCandidatePrerequisiteStatus::Unresolved;
    }
    stack.push(key);

    let mut constraints = apply_candidate_subst_to_constraints(&candidate.prerequisites, subst);
    loop {
        let mut progressed = false;
        let mut replacements = Vec::<(TypeVar, CompactType)>::new();
        let remaining = Vec::new();

        for constraint in constraints {
            let arg_infos = infer.role_arg_infos_of(&constraint.role);
            let (input_indices, output_indices) =
                role_constraint_arg_indices(&arg_infos, constraint.args.len());
            let Some(_rendered_inputs) = render_selected_concrete_args(
                &constraint,
                &input_indices,
                !output_indices.is_empty(),
            ) else {
                stack.pop();
                return RoleCandidatePrerequisiteStatus::Unresolved;
            };

            let rendered_args = render_role_constraint_args_for_diagnostic(
                &constraint,
                &output_indices,
                &arg_infos,
            );

            let candidates = infer.role_impl_candidates_of(&constraint.role);
            let head_matches = candidates
                .iter()
                .filter(|candidate| {
                    role_candidate_input_subst(
                        candidate,
                        &input_indices,
                        &concrete_selected_input_types(
                            &constraint,
                            &input_indices,
                            !output_indices.is_empty(),
                        )
                        .unwrap_or_default(),
                    )
                    .is_some()
                })
                .collect::<Vec<_>>();
            let viable_matches = head_matches
                .iter()
                .copied()
                .filter(|candidate| {
                    let Some(local_subst) = role_candidate_input_subst(
                        candidate,
                        &input_indices,
                        &concrete_selected_input_types(
                            &constraint,
                            &input_indices,
                            !output_indices.is_empty(),
                        )
                        .unwrap_or_default(),
                    ) else {
                        return false;
                    };
                    matches!(
                        role_candidate_prerequisite_status(infer, candidate, &local_subst, stack),
                        RoleCandidatePrerequisiteStatus::Satisfied
                    )
                })
                .collect::<Vec<_>>();
            let matches = select_most_specific_role_candidates(viable_matches, &input_indices);

            if matches.len() != 1 {
                stack.pop();
                if matches.is_empty() && !head_matches.is_empty() {
                    let Some(local_subst) = role_candidate_input_subst(
                        head_matches[0],
                        &input_indices,
                        &concrete_selected_input_types(
                            &constraint,
                            &input_indices,
                            !output_indices.is_empty(),
                        )
                        .unwrap_or_default(),
                    ) else {
                        return RoleCandidatePrerequisiteStatus::MissingImpl {
                            role: path_string(&constraint.role),
                            args: rendered_args,
                            origins: candidate.origins.clone(),
                        };
                    };
                    return match role_candidate_prerequisite_status(
                        infer,
                        head_matches[0],
                        &local_subst,
                        stack,
                    ) {
                        RoleCandidatePrerequisiteStatus::MissingImpl {
                            role,
                            args,
                            origins,
                        } => RoleCandidatePrerequisiteStatus::MissingImpl {
                            role,
                            args,
                            origins,
                        },
                        RoleCandidatePrerequisiteStatus::AmbiguousImpl {
                            role,
                            args,
                            candidates,
                            previews,
                            origins,
                        } => RoleCandidatePrerequisiteStatus::AmbiguousImpl {
                            role,
                            args,
                            candidates,
                            previews,
                            origins,
                        },
                        _ => RoleCandidatePrerequisiteStatus::MissingImpl {
                            role: path_string(&constraint.role),
                            args: rendered_args,
                            origins: candidate.origins.clone(),
                        },
                    };
                }
                return if matches.is_empty() {
                    RoleCandidatePrerequisiteStatus::MissingImpl {
                        role: path_string(&constraint.role),
                        args: rendered_args,
                        origins: candidate.origins.clone(),
                    }
                } else {
                    RoleCandidatePrerequisiteStatus::AmbiguousImpl {
                        role: path_string(&constraint.role),
                        args: rendered_args,
                        candidates: matches.len(),
                        previews: role_candidate_previews(matches),
                        origins: candidate.origins.clone(),
                    }
                };
            }

            progressed = true;
            replacements.extend(collect_role_output_replacements(
                &constraint,
                matches[0],
                &role_candidate_input_subst(
                    matches[0],
                    &input_indices,
                    &concrete_selected_input_types(
                        &constraint,
                        &input_indices,
                        !output_indices.is_empty(),
                    )
                    .unwrap_or_default(),
                )
                .unwrap_or_default(),
                &output_indices,
            ));
        }

        if !replacements.is_empty() {
            constraints = apply_role_output_replacements_to_constraints(&remaining, &replacements);
            progressed = true;
        } else {
            constraints = remaining;
        }

        if constraints.is_empty() {
            break;
        }

        if !progressed {
            stack.pop();
            return RoleCandidatePrerequisiteStatus::Unresolved;
        }
    }

    stack.pop();
    RoleCandidatePrerequisiteStatus::Satisfied
}

fn collect_role_output_replacements(
    constraint: &CompactRoleConstraint,
    candidate: &crate::solve::RoleImplCandidate,
    subst: &HashMap<TypeVar, CompactType>,
    output_indices: &[usize],
) -> Vec<(TypeVar, CompactType)> {
    output_indices
        .iter()
        .filter_map(|index| {
            let target = projection_target_var(constraint.args.get(*index)?)?;
            let ty = apply_candidate_subst_to_type(candidate.compact_args.get(*index)?, subst);
            Some((target, ty))
        })
        .collect()
}

fn collect_role_default_replacements_if_disappeared(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    constraint_index: usize,
    constraint: &CompactRoleConstraint,
    candidate: &crate::solve::RoleImplCandidate,
    subst: &HashMap<TypeVar, CompactType>,
    input_indices: &[usize],
    role_arg_inputs: &dyn Fn(&Path) -> Option<Vec<bool>>,
) -> Vec<(TypeVar, CompactType)> {
    let replacements =
        collect_role_default_replacement_candidates(constraint, candidate, subst, input_indices);
    if replacements.is_empty() {
        return Vec::new();
    }
    let remaining_constraints = constraints
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != constraint_index)
        .map(|(_, constraint)| constraint.clone())
        .collect::<Vec<_>>();
    let rewritten_scheme = apply_role_output_replacements_to_scheme(scheme, &replacements);
    let rewritten_constraints =
        apply_role_output_replacements_to_constraints(&remaining_constraints, &replacements);
    let (coalesced_scheme, coalesced_constraints) =
        coalesce_by_co_occurrence_with_role_constraint_inputs(
            &rewritten_scheme,
            &rewritten_constraints,
            role_arg_inputs,
            &HashMap::new(),
            0,
        );
    replacements
        .iter()
        .filter(|(target, _)| {
            !compact_scheme_contains_var(&coalesced_scheme, *target)
                && !compact_constraints_contain_var(&coalesced_constraints, *target)
        })
        .cloned()
        .collect()
}

fn remove_disappearing_noncenter_role_vars(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    role_arg_inputs: &dyn Fn(&Path) -> Option<Vec<bool>>,
) -> (CompactTypeScheme, Vec<CompactRoleConstraint>) {
    if constraints.is_empty() {
        return (scheme.clone(), constraints.to_vec());
    }

    let centered = centered_role_constraint_vars(constraints);
    let (role_free_scheme, _) = coalesce_by_co_occurrence_with_role_constraints(scheme, &[]);
    let original_vars = compact_scheme_and_constraints_vars(scheme, constraints);
    let role_free_vars = compact_scheme_vars(&role_free_scheme);
    let disappeared = original_vars
        .into_iter()
        .filter(|tv| !centered.contains(tv) && !role_free_vars.contains(tv))
        .collect::<Vec<_>>();
    if disappeared.is_empty() {
        return (scheme.clone(), constraints.to_vec());
    }

    let output_center_replacements = role_output_center_replacements(constraints, role_arg_inputs);
    let subst = disappeared
        .into_iter()
        .map(|tv| (tv, output_center_replacements.get(&tv).copied()))
        .collect::<HashMap<_, _>>();
    let rewritten_scheme = rewrite_scheme_with_subst(scheme, &subst);
    let rewritten_constraints =
        rewrite_role_constraints_preserving_explicit_centers(constraints, &subst, role_arg_inputs);
    (rewritten_scheme, rewritten_constraints)
}

fn rewrite_role_constraints_preserving_explicit_centers(
    constraints: &[CompactRoleConstraint],
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    role_arg_inputs: &dyn Fn(&Path) -> Option<Vec<bool>>,
) -> Vec<CompactRoleConstraint> {
    let mut out = Vec::new();
    for constraint in constraints {
        let rewritten = CompactRoleConstraint {
            role: constraint.role.clone(),
            args: constraint
                .args
                .iter()
                .map(|arg| {
                    let mut rewritten = crate::simplify::cooccur::rewrite_bounds(arg, subst);
                    if let Some(center) = arg.self_var()
                        && !subst.contains_key(&center)
                        && !compact_bounds_contains_var(&rewritten, center)
                    {
                        *rewritten.self_var_mut() = Some(center);
                        rewritten.lower_mut().vars.insert(center);
                        rewritten.upper_mut().vars.insert(center);
                    }
                    rewritten
                })
                .collect(),
        };
        if !out.contains(&rewritten) {
            out.push(rewritten);
        }
    }
    coalesce_rewritten_role_constraints(out, role_arg_inputs)
        .into_iter()
        .filter(|constraint| !role_constraint_is_observationally_empty(constraint))
        .collect()
}

fn coalesce_rewritten_role_constraints(
    constraints: Vec<CompactRoleConstraint>,
    role_arg_inputs: &dyn Fn(&Path) -> Option<Vec<bool>>,
) -> Vec<CompactRoleConstraint> {
    let mut out = Vec::new();
    let mut visited = vec![false; constraints.len()];
    for index in 0..constraints.len() {
        if visited[index] {
            continue;
        }
        visited[index] = true;
        let mut component = vec![index];
        let mut cursor = 0;
        while cursor < component.len() {
            let current = component[cursor];
            cursor += 1;
            for other in 0..constraints.len() {
                if visited[other] {
                    continue;
                }
                if role_constraints_share_input_vars(
                    &constraints[current],
                    &constraints[other],
                    role_arg_inputs,
                ) {
                    visited[other] = true;
                    component.push(other);
                }
            }
        }
        out.push(merge_role_constraint_component(
            component
                .into_iter()
                .map(|index| constraints[index].clone()),
        ));
    }
    out
}

fn role_constraints_share_input_vars(
    lhs: &CompactRoleConstraint,
    rhs: &CompactRoleConstraint,
    role_arg_inputs: &dyn Fn(&Path) -> Option<Vec<bool>>,
) -> bool {
    if lhs.role != rhs.role || lhs.args.len() != rhs.args.len() {
        return false;
    }
    if lhs == rhs {
        return true;
    }
    let input_indices = role_constraint_input_indices(lhs, role_arg_inputs);
    !input_indices.is_empty()
        && input_indices.iter().all(|index| {
            let mut lhs_vars = HashSet::new();
            let mut rhs_vars = HashSet::new();
            collect_compact_bounds_vars(&lhs.args[*index], &mut lhs_vars);
            collect_compact_bounds_vars(&rhs.args[*index], &mut rhs_vars);
            !lhs_vars.is_disjoint(&rhs_vars)
        })
}

fn role_constraint_input_indices(
    constraint: &CompactRoleConstraint,
    role_arg_inputs: &dyn Fn(&Path) -> Option<Vec<bool>>,
) -> Vec<usize> {
    let Some(flags) = role_arg_inputs(&constraint.role) else {
        return (0..constraint.args.len()).collect();
    };
    if flags.len() != constraint.args.len() {
        return (0..constraint.args.len()).collect();
    }
    let indices = flags
        .into_iter()
        .enumerate()
        .filter_map(|(index, is_input)| is_input.then_some(index))
        .collect::<Vec<_>>();
    if indices.is_empty() {
        (0..constraint.args.len()).collect()
    } else {
        indices
    }
}

fn merge_role_constraint_component(
    constraints: impl Iterator<Item = CompactRoleConstraint>,
) -> CompactRoleConstraint {
    let mut constraints = constraints.peekable();
    let mut merged = constraints.next().expect("component must not be empty");
    for constraint in constraints {
        merged.args = merged
            .args
            .into_iter()
            .zip(constraint.args.into_iter())
            .map(|(lhs, rhs)| merge_compact_bounds(true, lhs, rhs))
            .collect();
    }
    merged
}

fn role_constraint_is_observationally_empty(constraint: &CompactRoleConstraint) -> bool {
    constraint
        .args
        .iter()
        .all(|arg| arg.self_var().is_none() && is_empty_compact_bounds(arg))
}

fn is_empty_compact_bounds(bounds: &CompactBounds) -> bool {
    is_empty_compact_type(bounds.lower()) && is_empty_compact_type(bounds.upper())
}

fn is_empty_compact_type(ty: &CompactType) -> bool {
    ty == &CompactType::default()
}

fn collect_role_default_replacement_candidates(
    constraint: &CompactRoleConstraint,
    candidate: &crate::solve::RoleImplCandidate,
    subst: &HashMap<TypeVar, CompactType>,
    input_indices: &[usize],
) -> Vec<(TypeVar, CompactType)> {
    input_indices
        .iter()
        .filter_map(|index| {
            let arg = constraint.args.get(*index)?;
            let target = projection_target_var(arg)?;
            let concrete = concrete_bounds_repr(arg, true)?;
            let candidate_ty =
                apply_candidate_subst_to_type(candidate.compact_args.get(*index)?, subst);
            Some((
                target,
                join_default_replacement_type(&concrete, &candidate_ty),
            ))
        })
        .collect()
}

fn join_default_replacement_type(concrete: &CompactType, candidate: &CompactType) -> CompactType {
    let mut joined = merge_compact_types(true, concrete.clone(), candidate.clone());
    normalize_builtin_numeric_compact_type(&mut joined);
    joined
}

fn apply_candidate_subst_to_constraints(
    constraints: &[CompactRoleConstraint],
    subst: &HashMap<TypeVar, CompactType>,
) -> Vec<CompactRoleConstraint> {
    constraints
        .iter()
        .map(|constraint| CompactRoleConstraint {
            role: constraint.role.clone(),
            args: constraint
                .args
                .iter()
                .map(|arg| apply_candidate_subst_to_bounds(arg, subst))
                .collect(),
        })
        .collect()
}

fn apply_candidate_subst_to_bounds(
    bounds: &CompactBounds,
    subst: &HashMap<TypeVar, CompactType>,
) -> CompactBounds {
    normalize_rewritten_bounds(CompactBounds::Interval {
        self_var: bounds.self_var().filter(|tv| !subst.contains_key(tv)),
        lower: apply_candidate_subst_to_type(bounds.lower(), subst),
        upper: apply_candidate_subst_to_type(bounds.upper(), subst),
    })
}

fn apply_candidate_subst_to_type(
    ty: &CompactType,
    subst: &HashMap<TypeVar, CompactType>,
) -> CompactType {
    let mut out = CompactType {
        vars: ty
            .vars
            .iter()
            .copied()
            .filter(|tv| !subst.contains_key(tv))
            .collect(),
        prims: ty.prims.clone(),
        cons: ty
            .cons
            .iter()
            .map(|con| crate::simplify::compact::CompactCon {
                path: con.path.clone(),
                args: con
                    .args
                    .iter()
                    .map(|arg| apply_candidate_subst_to_bounds(arg, subst))
                    .collect(),
            })
            .collect(),
        funs: ty
            .funs
            .iter()
            .map(|fun| crate::simplify::compact::CompactFun {
                arg: apply_candidate_subst_to_type(&fun.arg, subst),
                arg_eff: apply_candidate_subst_to_type(&fun.arg_eff, subst),
                ret_eff: apply_candidate_subst_to_type(&fun.ret_eff, subst),
                ret: apply_candidate_subst_to_type(&fun.ret, subst),
            })
            .collect(),
        records: ty
            .records
            .iter()
            .map(|record| crate::simplify::compact::CompactRecord {
                fields: record
                    .fields
                    .iter()
                    .map(|field| crate::types::RecordField {
                        name: field.name.clone(),
                        value: apply_candidate_subst_to_type(&field.value, subst),
                        optional: field.optional,
                    })
                    .collect(),
            })
            .collect(),
        record_spreads: ty
            .record_spreads
            .iter()
            .map(|spread| crate::simplify::compact::CompactRecordSpread {
                fields: spread
                    .fields
                    .iter()
                    .map(|field| crate::types::RecordField {
                        name: field.name.clone(),
                        value: apply_candidate_subst_to_type(&field.value, subst),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(apply_candidate_subst_to_type(&spread.tail, subst)),
                tail_wins: spread.tail_wins,
            })
            .collect(),
        variants: ty
            .variants
            .iter()
            .map(|variant| crate::simplify::compact::CompactVariant {
                items: variant
                    .items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| apply_candidate_subst_to_type(payload, subst))
                                .collect(),
                        )
                    })
                    .collect(),
            })
            .collect(),
        tuples: ty
            .tuples
            .iter()
            .map(|tuple| {
                tuple
                    .iter()
                    .map(|item| apply_candidate_subst_to_type(item, subst))
                    .collect()
            })
            .collect(),
        rows: ty
            .rows
            .iter()
            .map(|row| crate::simplify::compact::CompactRow {
                items: row
                    .items
                    .iter()
                    .map(|item| apply_candidate_subst_to_type(item, subst))
                    .collect(),
                tail: Box::new(apply_candidate_subst_to_type(&row.tail, subst)),
            })
            .collect(),
    };
    for tv in &ty.vars {
        if let Some(replacement) = subst.get(tv) {
            out = merge_compact_types(true, out, replacement.clone());
        }
    }
    out
}

fn projection_target_var(bounds: &CompactBounds) -> Option<TypeVar> {
    bounds.self_var().or_else(|| {
        let lower = single_compact_var(bounds.lower());
        let upper = single_compact_var(bounds.upper());
        match (lower, upper) {
            (Some(lhs), Some(rhs)) if lhs == rhs => Some(lhs),
            (Some(tv), None) | (None, Some(tv)) => Some(tv),
            _ => None,
        }
    })
}

fn centered_role_constraint_vars(constraints: &[CompactRoleConstraint]) -> HashSet<TypeVar> {
    constraints
        .iter()
        .flat_map(|constraint| constraint.args.iter().filter_map(projection_target_var))
        .collect()
}

fn compact_scheme_and_constraints_vars(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> HashSet<TypeVar> {
    let mut out = compact_scheme_vars(scheme);
    out.extend(compact_constraints_vars(constraints));
    out
}

fn compact_scheme_vars(scheme: &CompactTypeScheme) -> HashSet<TypeVar> {
    let mut out = HashSet::new();
    collect_compact_bounds_vars(&scheme.cty, &mut out);
    for (&tv, bounds) in &scheme.rec_vars {
        out.insert(tv);
        collect_compact_bounds_vars(bounds, &mut out);
    }
    out
}

fn compact_constraints_vars(constraints: &[CompactRoleConstraint]) -> HashSet<TypeVar> {
    let mut out = HashSet::new();
    for constraint in constraints {
        for arg in &constraint.args {
            collect_compact_bounds_vars(arg, &mut out);
        }
    }
    out
}

fn collect_compact_bounds_vars(bounds: &CompactBounds, out: &mut HashSet<TypeVar>) {
    if let Some(tv) = bounds.self_var() {
        out.insert(tv);
    }
    collect_compact_type_vars(bounds.lower(), out);
    collect_compact_type_vars(bounds.upper(), out);
}

fn collect_compact_type_vars(ty: &CompactType, out: &mut HashSet<TypeVar>) {
    out.extend(ty.vars.iter().copied());
    for con in &ty.cons {
        for arg in &con.args {
            collect_compact_bounds_vars(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_compact_type_vars(&fun.arg, out);
        collect_compact_type_vars(&fun.arg_eff, out);
        collect_compact_type_vars(&fun.ret_eff, out);
        collect_compact_type_vars(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_compact_type_vars(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_compact_type_vars(&field.value, out);
        }
        collect_compact_type_vars(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_compact_type_vars(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_compact_type_vars(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_compact_type_vars(item, out);
        }
        collect_compact_type_vars(&row.tail, out);
    }
}

fn single_compact_var(ty: &CompactType) -> Option<TypeVar> {
    (ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
        && ty.vars.len() == 1)
        .then(|| *ty.vars.iter().next().unwrap())
}

fn apply_role_output_replacements_to_scheme(
    scheme: &CompactTypeScheme,
    replacements: &[(TypeVar, CompactType)],
) -> CompactTypeScheme {
    CompactTypeScheme {
        cty: apply_role_output_replacements_to_bounds(&scheme.cty, replacements),
        rec_vars: scheme
            .rec_vars
            .iter()
            .map(|(tv, bounds)| {
                (
                    *tv,
                    apply_role_output_replacements_to_bounds(bounds, replacements),
                )
            })
            .collect(),
    }
}

fn compact_scheme_contains_var(scheme: &CompactTypeScheme, target: TypeVar) -> bool {
    compact_bounds_contains_var(&scheme.cty, target)
        || scheme
            .rec_vars
            .iter()
            .any(|(tv, bounds)| *tv == target || compact_bounds_contains_var(bounds, target))
}

fn compact_constraints_contain_var(constraints: &[CompactRoleConstraint], target: TypeVar) -> bool {
    constraints.iter().any(|constraint| {
        constraint
            .args
            .iter()
            .any(|arg| compact_bounds_contains_var(arg, target))
    })
}

fn compact_bounds_contains_var(bounds: &CompactBounds, target: TypeVar) -> bool {
    bounds.self_var() == Some(target)
        || compact_type_contains_var(bounds.lower(), target)
        || compact_type_contains_var(bounds.upper(), target)
}

fn compact_type_contains_var(ty: &CompactType, target: TypeVar) -> bool {
    ty.vars.contains(&target)
        || ty.cons.iter().any(|con| {
            con.args
                .iter()
                .any(|arg| compact_bounds_contains_var(arg, target))
        })
        || ty.funs.iter().any(|fun| {
            compact_type_contains_var(&fun.arg, target)
                || compact_type_contains_var(&fun.arg_eff, target)
                || compact_type_contains_var(&fun.ret_eff, target)
                || compact_type_contains_var(&fun.ret, target)
        })
        || ty.records.iter().any(|record| {
            record
                .fields
                .iter()
                .any(|field| compact_type_contains_var(&field.value, target))
        })
        || ty.record_spreads.iter().any(|spread| {
            spread
                .fields
                .iter()
                .any(|field| compact_type_contains_var(&field.value, target))
                || compact_type_contains_var(&spread.tail, target)
        })
        || ty.variants.iter().any(|variant| {
            variant.items.iter().any(|(_, payloads)| {
                payloads
                    .iter()
                    .any(|payload| compact_type_contains_var(payload, target))
            })
        })
        || ty.tuples.iter().any(|tuple| {
            tuple
                .iter()
                .any(|item| compact_type_contains_var(item, target))
        })
        || ty.rows.iter().any(|row| {
            row.items
                .iter()
                .any(|item| compact_type_contains_var(item, target))
                || compact_type_contains_var(&row.tail, target)
        })
}

fn apply_role_output_replacements_to_constraints(
    constraints: &[CompactRoleConstraint],
    replacements: &[(TypeVar, CompactType)],
) -> Vec<CompactRoleConstraint> {
    constraints
        .iter()
        .map(|constraint| CompactRoleConstraint {
            role: constraint.role.clone(),
            args: constraint
                .args
                .iter()
                .map(|arg| apply_role_output_replacements_to_bounds(arg, replacements))
                .collect(),
        })
        .collect()
}

fn apply_role_output_replacements_to_bounds(
    bounds: &CompactBounds,
    replacements: &[(TypeVar, CompactType)],
) -> CompactBounds {
    normalize_rewritten_bounds(CompactBounds::Interval {
        self_var: bounds
            .self_var()
            .filter(|tv| !replacements.iter().any(|(target, _)| target == tv)),
        lower: apply_role_output_replacements_to_type(bounds.lower(), replacements, true),
        upper: apply_role_output_replacements_to_type(bounds.upper(), replacements, false),
    })
}

fn apply_role_output_replacements_to_type(
    ty: &CompactType,
    replacements: &[(TypeVar, CompactType)],
    positive: bool,
) -> CompactType {
    let mut out = CompactType {
        vars: ty
            .vars
            .iter()
            .copied()
            .filter(|tv| !replacements.iter().any(|(target, _)| target == tv))
            .collect(),
        prims: ty.prims.clone(),
        cons: ty
            .cons
            .iter()
            .map(|con| crate::simplify::compact::CompactCon {
                path: con.path.clone(),
                args: con
                    .args
                    .iter()
                    .map(|arg| apply_role_output_replacements_to_bounds(arg, replacements))
                    .collect(),
            })
            .collect(),
        funs: ty
            .funs
            .iter()
            .map(|fun| crate::simplify::compact::CompactFun {
                arg: apply_role_output_replacements_to_type(&fun.arg, replacements, !positive),
                arg_eff: apply_role_output_replacements_to_type(
                    &fun.arg_eff,
                    replacements,
                    !positive,
                ),
                ret_eff: apply_role_output_replacements_to_type(
                    &fun.ret_eff,
                    replacements,
                    positive,
                ),
                ret: apply_role_output_replacements_to_type(&fun.ret, replacements, positive),
            })
            .collect(),
        records: ty
            .records
            .iter()
            .map(|record| crate::simplify::compact::CompactRecord {
                fields: record
                    .fields
                    .iter()
                    .map(|field| crate::types::RecordField {
                        name: field.name.clone(),
                        value: apply_role_output_replacements_to_type(
                            &field.value,
                            replacements,
                            positive,
                        ),
                        optional: field.optional,
                    })
                    .collect(),
            })
            .collect(),
        record_spreads: ty
            .record_spreads
            .iter()
            .map(|spread| crate::simplify::compact::CompactRecordSpread {
                fields: spread
                    .fields
                    .iter()
                    .map(|field| crate::types::RecordField {
                        name: field.name.clone(),
                        value: apply_role_output_replacements_to_type(
                            &field.value,
                            replacements,
                            positive,
                        ),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(apply_role_output_replacements_to_type(
                    &spread.tail,
                    replacements,
                    positive,
                )),
                tail_wins: spread.tail_wins,
            })
            .collect(),
        variants: ty
            .variants
            .iter()
            .map(|variant| crate::simplify::compact::CompactVariant {
                items: variant
                    .items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| {
                                    apply_role_output_replacements_to_type(
                                        payload,
                                        replacements,
                                        positive,
                                    )
                                })
                                .collect(),
                        )
                    })
                    .collect(),
            })
            .collect(),
        tuples: ty
            .tuples
            .iter()
            .map(|items| {
                items
                    .iter()
                    .map(|item| {
                        apply_role_output_replacements_to_type(item, replacements, positive)
                    })
                    .collect()
            })
            .collect(),
        rows: ty
            .rows
            .iter()
            .map(|row| crate::simplify::compact::CompactRow {
                items: row
                    .items
                    .iter()
                    .map(|item| {
                        apply_role_output_replacements_to_type(item, replacements, positive)
                    })
                    .collect(),
                tail: Box::new(apply_role_output_replacements_to_type(
                    &row.tail,
                    replacements,
                    positive,
                )),
            })
            .collect(),
    };

    for (target, replacement) in replacements {
        if ty.vars.contains(target) {
            out = merge_compact_types(positive, out, replacement.clone());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::fresh_type_var;
    use crate::symbols::Name;

    use super::*;

    #[test]
    fn role_input_resolution_ignores_root_concrete_residual_vars() {
        let a = fresh_type_var();
        let role_arg = bounds(
            type_with_vars_and_cons([a], ["int"]),
            CompactType::default(),
        );
        let scheme = CompactTypeScheme {
            cty: bounds(
                type_with_vars_and_cons([a], ["int"]),
                CompactType::default(),
            ),
            rec_vars: Default::default(),
        };

        let polarity = main_type_polarity(&scheme, &|_, _| Variance::Invariant);

        assert!(
            role_input_concrete_type_for_target(&role_arg, Some(a), &polarity, false).is_some(),
            "root int | α is rendered as int, so α does not block lower-bound role resolution",
        );
    }

    #[test]
    fn role_input_resolution_counts_vars_inside_invariant_constructor_bounds() {
        let a = fresh_type_var();
        let box_path = path("Box");
        let invariant_arg = bounds(
            type_with_vars_and_cons([a], ["int"]),
            type_with_vars_and_cons([a], ["float"]),
        );
        let scheme = CompactTypeScheme {
            cty: bounds(
                CompactType {
                    cons: vec![crate::simplify::compact::CompactCon {
                        path: box_path,
                        args: vec![invariant_arg.clone()],
                    }],
                    ..CompactType::default()
                },
                CompactType::default(),
            ),
            rec_vars: Default::default(),
        };

        let polarity = main_type_polarity(&scheme, &|_, _| Variance::Invariant);

        assert!(
            role_input_concrete_type_for_target(&invariant_arg, Some(a), &polarity, false)
                .is_none(),
            "invariant args are read as (lower covariant, upper contravariant), so α in the upper side blocks lower-bound role resolution",
        );
    }

    fn bounds(lower: CompactType, upper: CompactType) -> CompactBounds {
        CompactBounds::Interval {
            self_var: None,
            lower,
            upper,
        }
    }

    fn type_with_vars_and_cons(
        vars: impl IntoIterator<Item = TypeVar>,
        cons: impl IntoIterator<Item = &'static str>,
    ) -> CompactType {
        CompactType {
            vars: vars.into_iter().collect::<HashSet<_>>(),
            cons: cons
                .into_iter()
                .map(|name| crate::simplify::compact::CompactCon {
                    path: path(name),
                    args: Vec::new(),
                })
                .collect(),
            ..CompactType::default()
        }
    }

    fn path(name: &str) -> Path {
        Path {
            segments: vec![Name(name.to_string())],
        }
    }
}
