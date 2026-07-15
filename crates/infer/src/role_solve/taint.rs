use super::*;

pub(super) fn role_arg_boundary_has_method_taint<const RECORD_OWNER_DEPENDENCIES: bool>(
    arg: &CompactRoleArg,
    positive: bool,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
) -> bool {
    match &arg.bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
                if positive { lower } else { upper },
                method_taint,
            )
        }
        bounds => {
            compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(bounds, method_taint)
        }
    }
}

pub(super) fn single_concrete_type(ty: &CompactType) -> Option<CompactType> {
    let mut found = Vec::new();
    if ty.never {
        found.push(CompactType::never());
    }
    found.extend(ty.builtins.iter().copied().map(CompactType::from_builtin));
    found.extend(
        compact_con_entries(&ty.cons)
            .into_iter()
            .map(CompactType::from_con),
    );
    found.extend(ty.funs.iter().cloned().map(CompactType::from_fun));
    found.extend(ty.records.iter().cloned().map(CompactType::from_record));
    found.extend(
        ty.record_spreads
            .iter()
            .cloned()
            .map(CompactType::from_record_spread),
    );
    found.extend(
        ty.poly_variants
            .iter()
            .cloned()
            .map(CompactType::from_poly_variant),
    );
    found.extend(ty.tuples.iter().cloned().map(CompactType::from_tuple));
    found.extend(ty.rows.iter().cloned().map(CompactType::from_row));
    (found.len() == 1).then(|| found.remove(0))
}

pub(super) fn compact_type_has_method_taint<const RECORD_OWNER_DEPENDENCIES: bool>(
    ty: &CompactType,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
) -> bool {
    ty.vars.iter().any(|var| {
        if RECORD_OWNER_DEPENDENCIES {
            crate::analysis::record_owner_method_taint_read(var.var);
        }
        method_taint
            .get(&var.var)
            .is_some_and(|selects| !selects.is_empty())
    }) || ty.cons.values().any(|args| {
        args.iter().any(|arg| {
            compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(arg, method_taint)
        })
    }) || ty.funs.iter().any(|fun| {
        compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&fun.arg, method_taint)
            || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
                &fun.arg_eff,
                method_taint,
            )
            || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
                &fun.ret_eff,
                method_taint,
            )
            || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&fun.ret, method_taint)
    }) || ty.records.iter().any(|record| {
        record.fields.iter().any(|field| {
            compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&field.value, method_taint)
        })
    }) || ty.record_spreads.iter().any(|spread| {
        spread.fields.iter().any(|field| {
            compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&field.value, method_taint)
        }) || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&spread.tail, method_taint)
    }) || ty.poly_variants.iter().any(|variant| {
        variant.items.iter().any(|(_, payloads)| {
            payloads.iter().any(|payload| {
                compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(payload, method_taint)
            })
        })
    }) || ty.tuples.iter().any(|tuple| {
        tuple.items.iter().any(|item| {
            compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(item, method_taint)
        })
    }) || ty.rows.iter().any(|row| {
        row.items.values().any(|args| {
            args.iter().any(|arg| {
                compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(arg, method_taint)
            })
        }) || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&row.tail, method_taint)
    })
}

pub(super) fn compact_bounds_has_method_taint<const RECORD_OWNER_DEPENDENCIES: bool>(
    bounds: &CompactBounds,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
) -> bool {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(lower, method_taint)
                || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(upper, method_taint)
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            args.iter().any(|arg| {
                compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(arg, method_taint)
            })
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(arg, method_taint)
                || compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
                    arg_eff,
                    method_taint,
                )
                || compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
                    ret_eff,
                    method_taint,
                )
                || compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(ret, method_taint)
        }
        CompactBounds::Record { fields } => fields.iter().any(|field| {
            compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&field.value, method_taint)
        }),
        CompactBounds::PolyVariant { items } => items.iter().any(|(_, payloads)| {
            payloads.iter().any(|payload| {
                compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(payload, method_taint)
            })
        }),
    }
}

pub(super) fn role_arg_allowed_by_main_polarity(
    arg: &CompactRoleArg,
    selected_positive_boundary: bool,
    main_polarity: &MainPolarity,
) -> bool {
    role_arg_vars(arg).into_iter().all(|var| {
        match (
            main_polarity.positive.contains(&var),
            main_polarity.negative.contains(&var),
        ) {
            (false, false) => true,
            (true, false) => selected_positive_boundary,
            (false, true) => !selected_positive_boundary,
            (true, true) => false,
        }
    })
}

/// 下界での解決可否。main-negative な変数も、その負出現がすべて `target` と
/// 同じ交差に同伴しているなら許す。呼び出し側から入る値は交差の concrete 成分で
/// `target` 以下に絞られるので、subject が `target` 以外へ instantiate されることはない。
/// （例: `impl Debug int: our x.dsize = x.size` — x は `'x & int` で釘付け）
/// 同伴なしの負出現が一つでもあれば従来どおり拒否する（`'a + 1` の `'a` を守る）。
///
/// 見るのは subject の**トップレベル変数だけ**。con 引数の中の不変 interval 変数は
/// 構造ごと candidate との `match_bounds_pattern` が照合する領分で、ここで両極性
/// （同じ変数が lower/upper の両側に出る）を理由に拒否すると `list int` のような
/// 入れ子 concrete subject が永遠に解決できない。
pub(super) fn role_arg_lower_allowed(
    arg: &CompactRoleArg,
    target: &CompactType,
    main_polarity: &MainPolarity,
) -> bool {
    let top_level_vars = role_arg_top_level_vars(arg);
    top_level_vars.into_iter().all(|var| {
        match (
            main_polarity.positive.contains(&var),
            main_polarity.negative.contains(&var),
        ) {
            (false, false) => true,
            (true, false) => true,
            (false, true) => main_polarity.negative_occurrences_pinned_to(var, target),
            (true, true) => false,
        }
    })
}
