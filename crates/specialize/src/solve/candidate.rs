use super::*;

pub(super) fn simplify_resolved_union(
    graph: &ConstraintGraph<'_>,
    left: Type,
    right: Type,
) -> Type {
    if type_candidates_equivalent(&left, &right) || type_candidate_subtype(graph, &right, &left) {
        return left;
    }
    if type_candidate_subtype(graph, &left, &right) {
        return right;
    }
    types::simplify_type(Type::Union(Box::new(left), Box::new(right)))
}

pub(super) fn simplify_resolved_intersection(
    graph: &ConstraintGraph<'_>,
    left: Type,
    right: Type,
) -> Type {
    if type_candidates_equivalent(&left, &right) || type_candidate_subtype(graph, &left, &right) {
        return left;
    }
    if type_candidate_subtype(graph, &right, &left) {
        return right;
    }
    types::simplify_type(Type::Intersection(Box::new(left), Box::new(right)))
}

pub(super) fn effect_slot_candidate(slot_kind: TypeSlotKind, ty: Type) -> Type {
    if slot_kind != TypeSlotKind::Effect || matches!(ty, Type::EffectRow(_)) {
        return ty;
    }
    Type::EffectRow(vec![ty])
}

pub(super) fn join_effect_type_candidates(left: Type, right: Type) -> Type {
    if left.is_pure_effect() {
        return right;
    }
    if right.is_pure_effect() {
        return left;
    }
    match (left, right) {
        (Type::EffectRow(mut left), Type::EffectRow(right)) => {
            for item in right {
                if !left.contains(&item) {
                    left.push(item);
                }
            }
            types::simplify_type(Type::EffectRow(left))
        }
        (left, right) => types::simplify_type(Type::Union(Box::new(left), Box::new(right))),
    }
}

pub(super) fn meet_effect_type_candidates(left: Type, right: Type) -> Type {
    if left.is_pure_effect() || right.is_pure_effect() {
        return Type::pure_effect();
    }
    match (left, right) {
        (Type::EffectRow(left), Type::EffectRow(right)) => types::simplify_type(Type::EffectRow(
            left.into_iter()
                .filter(|item| right.contains(item))
                .collect(),
        )),
        (left, right) => types::simplify_type(Type::Intersection(Box::new(left), Box::new(right))),
    }
}

pub(super) fn join_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    if let Some(merged) = merge_open_candidate_shape(&left, &right) {
        return Ok(merged);
    }
    match (&left, &right) {
        (Type::Record(_), Type::Record(_)) => {
            return join_record_type_candidates(graph, slot, left, right);
        }
        (Type::PolyVariant(_), Type::PolyVariant(_)) => {
            return join_poly_variant_type_candidates(graph, slot, left, right);
        }
        _ => {}
    }
    if type_candidates_equivalent(&left, &right) || type_candidate_subtype(graph, &right, &left) {
        return Ok(left);
    }
    if type_candidate_subtype(graph, &left, &right) {
        return Ok(right);
    }
    match (left, right) {
        (Type::Never, right) => Ok(right),
        (left, Type::Never) => Ok(left),
        (Type::Any, _) | (_, Type::Any) => Ok(Type::Any),
        (left, right) => Err(SpecializeError::ConflictingTypeCandidates {
            slot,
            existing: left,
            incoming: right,
        }),
    }
}

pub(super) fn meet_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    if let Some(merged) = merge_open_candidate_shape(&left, &right) {
        return Ok(merged);
    }
    match (&left, &right) {
        (Type::Record(_), Type::Record(_)) => {
            return meet_record_type_candidates(graph, slot, left, right);
        }
        (Type::PolyVariant(_), Type::PolyVariant(_)) => {
            return meet_poly_variant_type_candidates(graph, slot, left, right);
        }
        _ => {}
    }
    if type_candidates_equivalent(&left, &right) || type_candidate_subtype(graph, &left, &right) {
        return Ok(left);
    }
    if type_candidate_subtype(graph, &right, &left) {
        return Ok(right);
    }
    match (left, right) {
        (Type::Any, right) => Ok(right),
        (left, Type::Any) => Ok(left),
        (Type::Never, _) | (_, Type::Never) => Ok(Type::Never),
        (left, right) => Err(SpecializeError::ConflictingTypeCandidates {
            slot,
            existing: left,
            incoming: right,
        }),
    }
}

pub(super) fn join_record_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::Record(left_fields), Type::Record(right_fields)) = (left, right) else {
        unreachable!("record candidates checked by caller");
    };
    merge_record_type_candidates(graph, slot, left_fields, right_fields, RecordMerge::Join)
        .map(Type::Record)
}

pub(super) fn meet_record_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::Record(left_fields), Type::Record(right_fields)) = (left, right) else {
        unreachable!("record candidates checked by caller");
    };
    merge_record_type_candidates(graph, slot, left_fields, right_fields, RecordMerge::Meet)
        .map(Type::Record)
}

pub(super) fn merge_record_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left_fields: Vec<TypeField>,
    right_fields: Vec<TypeField>,
    merge: RecordMerge,
) -> Result<Vec<TypeField>, SpecializeError> {
    let mut out = Vec::new();
    for left in &left_fields {
        match record_field_type(&right_fields, &left.name) {
            Some(right) => {
                let value = match merge {
                    RecordMerge::Join => {
                        join_type_candidates(graph, slot, left.value.clone(), right.value.clone())?
                    }
                    RecordMerge::Meet => {
                        meet_type_candidates(graph, slot, left.value.clone(), right.value.clone())?
                    }
                };
                out.push(TypeField {
                    name: left.name.clone(),
                    value,
                    optional: match merge {
                        RecordMerge::Join => left.optional || right.optional,
                        RecordMerge::Meet => left.optional && right.optional,
                    },
                });
            }
            None => out.push(TypeField {
                name: left.name.clone(),
                value: left.value.clone(),
                optional: match merge {
                    RecordMerge::Join => true,
                    RecordMerge::Meet => left.optional,
                },
            }),
        }
    }
    for right in right_fields {
        if left_fields.iter().any(|left| left.name == right.name) {
            continue;
        }
        out.push(TypeField {
            name: right.name,
            value: right.value,
            optional: match merge {
                RecordMerge::Join => true,
                RecordMerge::Meet => right.optional,
            },
        });
    }
    Ok(out)
}

pub(super) fn join_poly_variant_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::PolyVariant(left_variants), Type::PolyVariant(right_variants)) = (left, right)
    else {
        unreachable!("poly variant candidates checked by caller");
    };
    let variants = merge_poly_variant_type_candidates(
        graph,
        slot,
        left_variants,
        right_variants,
        VariantMerge::Join,
    )?;
    Ok(Type::PolyVariant(variants))
}

pub(super) fn meet_poly_variant_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::PolyVariant(left_variants), Type::PolyVariant(right_variants)) = (left, right)
    else {
        unreachable!("poly variant candidates checked by caller");
    };
    let variants = merge_poly_variant_type_candidates(
        graph,
        slot,
        left_variants,
        right_variants,
        VariantMerge::Meet,
    )?;
    if variants.is_empty() {
        return Ok(Type::Never);
    }
    Ok(Type::PolyVariant(variants))
}

pub(super) fn merge_poly_variant_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left_variants: Vec<TypeVariant>,
    right_variants: Vec<TypeVariant>,
    merge: VariantMerge,
) -> Result<Vec<TypeVariant>, SpecializeError> {
    let mut out = Vec::new();
    for left in &left_variants {
        match matching_variant(&right_variants, left) {
            Some(right) => {
                let payloads = left
                    .payloads
                    .iter()
                    .cloned()
                    .zip(right.payloads.iter().cloned())
                    .map(|(left, right)| match merge {
                        VariantMerge::Join => join_type_candidates(graph, slot, left, right),
                        VariantMerge::Meet => meet_type_candidates(graph, slot, left, right),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                out.push(TypeVariant {
                    name: left.name.clone(),
                    payloads,
                });
            }
            None if merge == VariantMerge::Join => out.push(left.clone()),
            None => {}
        }
    }
    if merge == VariantMerge::Join {
        for right in right_variants {
            if left_variants
                .iter()
                .any(|left| variants_match(left, &right))
            {
                continue;
            }
            out.push(right);
        }
    }
    Ok(out)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RecordMerge {
    Join,
    Meet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum VariantMerge {
    Join,
    Meet,
}

pub(super) fn type_candidates_equivalent(left: &Type, right: &Type) -> bool {
    if left == right || left.is_pure_effect() && right.is_pure_effect() {
        return true;
    }
    let (Type::EffectRow(left_items), Type::EffectRow(right_items)) = (left, right) else {
        return false;
    };
    effect_row_candidates_equivalent(left_items, right_items)
}

pub(super) fn type_contains_open_var(ty: &Type) -> bool {
    match ty {
        Type::OpenVar(_) => true,
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_contains_open_var(arg)
                || type_contains_open_var(arg_effect)
                || type_contains_open_var(ret_effect)
                || type_contains_open_var(ret)
        }
        Type::Thunk { effect, value } => {
            type_contains_open_var(effect) || type_contains_open_var(value)
        }
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(type_contains_open_var)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_contains_open_var(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_contains_open_var)),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_contains_open_var(left) || type_contains_open_var(right)
        }
        Type::Stack { inner, .. } => type_contains_open_var(inner),
        Type::Any | Type::Never => false,
    }
}

pub(super) fn type_mentions_ref_update_unit(ty: &Type) -> bool {
    match ty {
        Type::Con { path, args } => {
            path.as_slice()
                == ["std", "control", "var", "ref_update", "update"]
                    .map(str::to_string)
                    .as_slice()
                || (path.as_slice()
                    == ["std", "control", "var", "ref_update"]
                        .map(str::to_string)
                        .as_slice()
                    && args.as_slice() == [Type::unit()])
                || args.iter().any(type_mentions_ref_update_unit)
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_mentions_ref_update_unit(arg)
                || type_mentions_ref_update_unit(arg_effect)
                || type_mentions_ref_update_unit(ret_effect)
                || type_mentions_ref_update_unit(ret)
        }
        Type::Thunk { effect, value } => {
            type_mentions_ref_update_unit(effect) || type_mentions_ref_update_unit(value)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_mentions_ref_update_unit(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_mentions_ref_update_unit)),
        Type::Tuple(items) | Type::EffectRow(items) => {
            items.iter().any(type_mentions_ref_update_unit)
        }
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_mentions_ref_update_unit(left) || type_mentions_ref_update_unit(right)
        }
        Type::Stack { inner, .. } => type_mentions_ref_update_unit(inner),
        Type::OpenVar(_) | Type::Any | Type::Never => false,
    }
}

pub(super) fn expr_kind_label(expr: &poly_expr::Expr) -> &'static str {
    match expr {
        poly_expr::Expr::Lit(_) => "lit",
        poly_expr::Expr::PrimitiveOp(_) => "primitive",
        poly_expr::Expr::Var(_) => "var",
        poly_expr::Expr::App(_, _) => "app",
        poly_expr::Expr::RefSet(_, _) => "ref-set",
        poly_expr::Expr::Lambda(_, _) => "lambda",
        poly_expr::Expr::Tuple(_) => "tuple",
        poly_expr::Expr::Record { .. } => "record",
        poly_expr::Expr::PolyVariant(_, _) => "poly-variant",
        poly_expr::Expr::Select(_, _) => "select",
        poly_expr::Expr::Case(_, _) => "case",
        poly_expr::Expr::Catch(_, _) => "catch",
        poly_expr::Expr::Block(_, _) => "block",
    }
}

pub(super) fn debug_expr_tree(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
    depth: usize,
) -> String {
    if depth == 0 {
        return format!("{expr:?}:...");
    }
    match arena.expr(expr) {
        poly_expr::Expr::Lit(_) => format!("{expr:?}:lit"),
        poly_expr::Expr::PrimitiveOp(op) => format!("{expr:?}:primitive({op:?})"),
        poly_expr::Expr::Var(ref_id) => {
            let target = arena.ref_target(*ref_id);
            let operation = target.and_then(|def| arena.effect_operations.get(&def));
            format!(
                "{expr:?}:var(ref={ref_id:?}, target={target:?}, op={:?})",
                operation.map(|operation| &operation.path)
            )
        }
        poly_expr::Expr::App(callee, arg) => format!(
            "{expr:?}:app({}, {})",
            debug_expr_tree(arena, *callee, depth - 1),
            debug_expr_tree(arena, *arg, depth - 1)
        ),
        poly_expr::Expr::RefSet(reference, value) => format!(
            "{expr:?}:ref-set({}, {})",
            debug_expr_tree(arena, *reference, depth - 1),
            debug_expr_tree(arena, *value, depth - 1)
        ),
        poly_expr::Expr::Lambda(param, body) => {
            format!(
                "{expr:?}:lambda({param:?} -> {})",
                debug_expr_tree(arena, *body, depth - 1)
            )
        }
        poly_expr::Expr::Tuple(items) => format!(
            "{expr:?}:tuple({})",
            items
                .iter()
                .map(|item| debug_expr_tree(arena, *item, depth - 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        poly_expr::Expr::Record { fields, spread } => format!(
            "{expr:?}:record({}; spread={})",
            fields
                .iter()
                .map(|(name, value)| format!(
                    "{name}:{}",
                    debug_expr_tree(arena, *value, depth - 1)
                ))
                .collect::<Vec<_>>()
                .join(", "),
            debug_record_spread(arena, spread, depth - 1)
        ),
        poly_expr::Expr::PolyVariant(tag, payloads) => format!(
            "{expr:?}:variant({tag}, {})",
            payloads
                .iter()
                .map(|payload| debug_expr_tree(arena, *payload, depth - 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        poly_expr::Expr::Select(base, select) => {
            let select = arena.select(*select);
            format!(
                "{expr:?}:select({}, name={}, resolution={:?})",
                debug_expr_tree(arena, *base, depth - 1),
                select.name,
                select.resolution
            )
        }
        poly_expr::Expr::Case(scrutinee, arms) => format!(
            "{expr:?}:case({}, arms={})",
            debug_expr_tree(arena, *scrutinee, depth - 1),
            arms.len()
        ),
        poly_expr::Expr::Catch(body, arms) => format!(
            "{expr:?}:catch({}, arms={})",
            debug_expr_tree(arena, *body, depth - 1),
            arms.len()
        ),
        poly_expr::Expr::Block(stmts, tail) => format!(
            "{expr:?}:block(stmts={}, tail={})",
            stmts.len(),
            tail.map(|tail| debug_expr_tree(arena, tail, depth - 1))
                .unwrap_or_else(|| "none".to_string())
        ),
    }
}

pub(super) fn debug_record_spread(
    arena: &poly_expr::Arena,
    spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
    depth: usize,
) -> String {
    match spread {
        poly_expr::RecordSpread::None => "none".to_string(),
        poly_expr::RecordSpread::Head(expr) => {
            format!("head({})", debug_expr_tree(arena, *expr, depth))
        }
        poly_expr::RecordSpread::Tail(expr) => {
            format!("tail({})", debug_expr_tree(arena, *expr, depth))
        }
    }
}

pub(super) fn type_candidate_subtype(
    graph: &ConstraintGraph<'_>,
    lower: &Type,
    upper: &Type,
) -> bool {
    if type_candidates_equivalent(lower, upper)
        || matches!(lower, Type::Never)
        || matches!(upper, Type::Any)
        || graph.direct_closed_cast_subtype(lower, upper)
    {
        return true;
    }
    match (lower, upper) {
        (Type::Union(left, right), _) => {
            type_candidate_subtype(graph, left, upper)
                && type_candidate_subtype(graph, right, upper)
        }
        (_, Type::Union(left, right)) => {
            type_candidate_subtype(graph, lower, left)
                || type_candidate_subtype(graph, lower, right)
        }
        (Type::Intersection(left, right), _) => {
            type_candidate_subtype(graph, left, upper)
                || type_candidate_subtype(graph, right, upper)
        }
        (_, Type::Intersection(left, right)) => {
            type_candidate_subtype(graph, lower, left)
                && type_candidate_subtype(graph, lower, right)
        }
        (lower, Type::Thunk { effect, value }) if effect.is_pure_effect() => {
            type_candidate_subtype(graph, lower, value)
        }
        (Type::Thunk { effect, value }, upper) if effect.is_pure_effect() => {
            type_candidate_subtype(graph, value, upper)
        }
        (
            Type::Con {
                path: lower_path,
                args: lower_args,
            },
            Type::Con {
                path: upper_path,
                args: upper_args,
            },
        ) => {
            lower_path == upper_path
                && lower_args.len() == upper_args.len()
                && lower_args
                    .iter()
                    .zip(upper_args)
                    .all(|(lower, upper)| type_candidates_equivalent(lower, upper))
        }
        (
            Type::Fun {
                arg: lower_arg,
                arg_effect: lower_arg_effect,
                ret_effect: lower_ret_effect,
                ret: lower_ret,
            },
            Type::Fun {
                arg: upper_arg,
                arg_effect: upper_arg_effect,
                ret_effect: upper_ret_effect,
                ret: upper_ret,
            },
        ) => {
            type_candidate_subtype(graph, upper_arg, lower_arg)
                && type_candidate_subtype(graph, upper_arg_effect, lower_arg_effect)
                && type_candidate_subtype(graph, lower_ret_effect, upper_ret_effect)
                && type_candidate_subtype(graph, lower_ret, upper_ret)
        }
        (
            Type::Thunk {
                effect: lower_effect,
                value: lower_value,
            },
            Type::Thunk {
                effect: upper_effect,
                value: upper_value,
            },
        ) => {
            type_candidate_subtype(graph, lower_effect, upper_effect)
                && type_candidate_subtype(graph, lower_value, upper_value)
        }
        (Type::Tuple(lower_items), Type::Tuple(upper_items)) => {
            lower_items.len() == upper_items.len()
                && lower_items
                    .iter()
                    .zip(upper_items)
                    .all(|(lower, upper)| type_candidate_subtype(graph, lower, upper))
        }
        (Type::Record(lower_fields), Type::Record(upper_fields)) => {
            upper_fields.iter().all(|upper_field| {
                upper_field.optional
                    || record_field_type(lower_fields, &upper_field.name).is_some_and(
                        |lower_field| {
                            type_candidate_subtype(graph, &lower_field.value, &upper_field.value)
                        },
                    )
            })
        }
        (Type::PolyVariant(lower_variants), Type::PolyVariant(upper_variants)) => {
            lower_variants.iter().all(|lower_variant| {
                upper_variants
                    .iter()
                    .find(|upper_variant| {
                        upper_variant.name == lower_variant.name
                            && upper_variant.payloads.len() == lower_variant.payloads.len()
                    })
                    .is_some_and(|upper_variant| {
                        lower_variant
                            .payloads
                            .iter()
                            .zip(&upper_variant.payloads)
                            .all(|(lower, upper)| type_candidate_subtype(graph, lower, upper))
                    })
            })
        }
        (Type::EffectRow(lower_items), Type::EffectRow(upper_items)) => {
            effect_row_candidate_subtype(graph, lower_items, upper_items)
        }
        (Type::Stack { inner: lower, .. }, Type::Stack { inner: upper, .. }) => {
            type_candidate_subtype(graph, lower, upper)
        }
        (Type::Stack { inner, weight }, upper) => graph
            .stack_constraint_projection(inner.as_ref().clone(), weight.clone())
            .is_some_and(|lower| type_candidate_subtype(graph, &lower, upper)),
        (lower, Type::Stack { inner, weight }) => graph
            .stack_constraint_projection(inner.as_ref().clone(), weight.clone())
            .is_some_and(|upper| type_candidate_subtype(graph, lower, &upper)),
        _ => false,
    }
}

pub(super) fn effect_row_candidates_equivalent(left_items: &[Type], right_items: &[Type]) -> bool {
    if left_items.len() != right_items.len() {
        return false;
    }
    let mut matched_right = vec![false; right_items.len()];
    for left in left_items {
        let Some(right_index) = right_items.iter().enumerate().find_map(|(index, right)| {
            (!matched_right[index]
                && same_effect_row_family(left, right)
                && type_candidates_equivalent(left, right))
            .then_some(index)
        }) else {
            return false;
        };
        matched_right[right_index] = true;
    }
    true
}

pub(super) fn effect_row_candidate_subtype(
    graph: &ConstraintGraph<'_>,
    lower_items: &[Type],
    upper_items: &[Type],
) -> bool {
    if lower_items.is_empty() {
        return true;
    }
    if lower_items.len() != upper_items.len() {
        return false;
    }
    let mut matched_upper = vec![false; upper_items.len()];
    for lower in lower_items {
        let Some(upper_index) = upper_items.iter().enumerate().find_map(|(index, upper)| {
            (!matched_upper[index]
                && same_effect_row_family(lower, upper)
                && type_candidate_subtype(graph, lower, upper))
            .then_some(index)
        }) else {
            return false;
        };
        matched_upper[upper_index] = true;
    }
    true
}

pub(super) fn resolve_role_arg_exact_type(
    graph: &ConstraintGraph<'_>,
    resolver: &mut TypeResolver<'_, '_, '_>,
    arg: &types::InstantiatedRoleArg,
) -> Result<Option<Type>, SpecializeError> {
    let lower = resolve_role_arg_bound(resolver, &arg.lower, RoleArgBound::Lower)?;
    let upper = resolve_role_arg_bound(resolver, &arg.upper, RoleArgBound::Upper)?;
    Ok(choose_resolved_role_arg_exact_type(graph, lower, upper))
}

pub(super) fn resolve_role_arg_bound(
    resolver: &mut TypeResolver<'_, '_, '_>,
    bound: &Type,
    side: RoleArgBound,
) -> Result<Option<Type>, SpecializeError> {
    match resolver.resolve(bound) {
        Ok(ty) => Ok(side.non_trivial(ty)),
        Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(None),
        Err(error) => Err(error),
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) enum RoleArgBound {
    Lower,
    Upper,
}

impl RoleArgBound {
    fn non_trivial(self, ty: Type) -> Option<Type> {
        match (self, &ty) {
            (Self::Lower, Type::Never) | (Self::Upper, Type::Any) => None,
            _ => Some(ty),
        }
    }
}

pub(super) fn choose_resolved_role_arg_exact_type(
    graph: &ConstraintGraph<'_>,
    lower: Option<Type>,
    upper: Option<Type>,
) -> Option<Type> {
    match (lower, upper) {
        (Some(lower), Some(upper)) if type_candidates_equivalent(&lower, &upper) => Some(lower),
        (Some(lower), Some(upper)) if type_candidate_subtype(graph, &lower, &upper) => Some(lower),
        (Some(lower), Some(upper)) if type_candidate_subtype(graph, &upper, &lower) => Some(upper),
        (Some(lower), None) => Some(lower),
        (None, Some(upper)) => Some(upper),
        _ => None,
    }
}

pub(super) fn con_path_without_args(ty: &Type) -> Option<&[String]> {
    let Type::Con { path, args } = ty else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    Some(path)
}

pub(super) fn record_field_type<'a>(fields: &'a [TypeField], name: &str) -> Option<&'a TypeField> {
    fields.iter().find(|field| field.name == name)
}

pub(super) fn matching_variant<'a>(
    variants: &'a [TypeVariant],
    target: &TypeVariant,
) -> Option<&'a TypeVariant> {
    variants
        .iter()
        .find(|variant| variants_match(variant, target))
}

pub(super) fn variants_match(left: &TypeVariant, right: &TypeVariant) -> bool {
    left.name == right.name && left.payloads.len() == right.payloads.len()
}

pub(super) fn join_record_fields(mut head: Vec<TypeField>, tail: Vec<TypeField>) -> Vec<TypeField> {
    head.extend(tail);
    head
}

pub(super) fn record_spread_def(
    spread: &poly_expr::RecordSpread<poly_expr::DefId>,
) -> Option<poly_expr::DefId> {
    match spread {
        poly_expr::RecordSpread::Head(def) | poly_expr::RecordSpread::Tail(def) => Some(*def),
        poly_expr::RecordSpread::None => None,
    }
}

pub(super) fn list_item_type(ty: &Type) -> Option<Type> {
    let Type::Con { args, .. } = ty else {
        return None;
    };
    let [item] = args.as_slice() else {
        return None;
    };
    Some(item.clone())
}

pub(super) fn primitive_spine_arg_type(
    op: poly_expr::PrimitiveOp,
    applied: usize,
    ret: &Type,
) -> Option<Type> {
    use poly_expr::PrimitiveOp;

    let final_ret = runtime_value_shape(final_return_type(ret));
    let list = list_item_type(final_ret).map(|_| final_ret.clone());
    let item = list.as_ref().and_then(list_item_type);
    match (op, applied) {
        (PrimitiveOp::ListEmpty, 0) => Some(Type::unit()),
        (PrimitiveOp::ListSingleton, 0) => item,
        (PrimitiveOp::ListMerge, 0 | 1)
        | (PrimitiveOp::ListIndexRange, 0)
        | (PrimitiveOp::ListSplice, 0 | 2)
        | (PrimitiveOp::ListIndexRangeRaw, 0)
        | (PrimitiveOp::ListSpliceRaw, 0 | 3) => list,
        (PrimitiveOp::ListIndexRange, 1) | (PrimitiveOp::ListSplice, 1) => Some(range_type()),
        (PrimitiveOp::ListIndexRangeRaw, 1 | 2) | (PrimitiveOp::ListSpliceRaw, 1 | 2) => {
            Some(int_type())
        }
        _ => None,
    }
}
