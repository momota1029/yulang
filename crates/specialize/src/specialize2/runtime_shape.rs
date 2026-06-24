use super::*;

pub(super) fn resolve_role_input_types(
    resolver: &mut TypeResolver<'_, '_>,
    demand: &types::InstantiatedRolePredicate,
) -> Result<Option<Vec<Type>>, SpecializeError> {
    let mut inputs = Vec::with_capacity(demand.inputs.len());
    for input in &demand.inputs {
        let lower = match resolver.resolve(&input.lower) {
            Ok(lower) => lower,
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => return Ok(None),
            Err(error) => return Err(error),
        };
        let upper = match resolver.resolve(&input.upper) {
            Ok(upper) => upper,
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => return Ok(None),
            Err(error) => return Err(error),
        };
        let Some(ty) = choose_role_arg_exact_type(lower, upper) else {
            return Ok(None);
        };
        inputs.push(role_input_value_type(ty));
    }
    Ok(Some(inputs))
}

pub(super) fn exact_role_input_types(
    predicate: &types::InstantiatedRolePredicate,
) -> Option<Vec<Type>> {
    predicate
        .inputs
        .iter()
        .map(|input| {
            choose_role_arg_exact_type(input.lower.clone(), input.upper.clone())
                .map(role_input_value_type)
        })
        .collect()
}

pub(super) fn role_input_value_type(ty: Type) -> Type {
    split_runtime_computation_shape(ty).0
}

pub(super) fn choose_role_arg_exact_type(lower: Type, upper: Type) -> Option<Type> {
    if lower == upper {
        return Some(lower);
    }
    if matches!(lower, Type::Never) && !matches!(upper, Type::Any) {
        return Some(upper);
    }
    if matches!(upper, Type::Any) && !matches!(lower, Type::Never) {
        return Some(lower);
    }
    None
}

pub(super) fn split_runtime_computation_shape(ty: Type) -> (Type, Type) {
    match ty {
        Type::Thunk { effect, value } => (*value, *effect),
        ty => (ty, Type::pure_effect()),
    }
}

pub(super) fn runtime_function_return_type(ty: &Type) -> Option<Type> {
    let Type::Fun {
        ret_effect, ret, ..
    } = ty
    else {
        return None;
    };
    Some(types::runtime_shape(
        ret_effect.as_ref().clone(),
        ret.as_ref().clone(),
    ))
}

pub(super) fn discarded_value_type(ty: &Type) -> Type {
    match ty {
        Type::Thunk { effect, value } => {
            types::runtime_shape(effect.as_ref().clone(), discarded_value_type(value))
        }
        Type::OpenVar(_) => Type::unit(),
        Type::Con { path, args } => Type::Con {
            path: path.clone(),
            args: args.iter().map(discarded_value_type).collect(),
        },
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(discarded_value_type(arg)),
            arg_effect: Box::new(discarded_effect_type(arg_effect)),
            ret_effect: Box::new(discarded_effect_type(ret_effect)),
            ret: Box::new(discarded_value_type(ret)),
        },
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|field| TypeField {
                    name: field.name.clone(),
                    value: discarded_value_type(&field.value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::PolyVariant(variants) => Type::PolyVariant(
            variants
                .iter()
                .map(|variant| TypeVariant {
                    name: variant.name.clone(),
                    payloads: variant.payloads.iter().map(discarded_value_type).collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(items.iter().map(discarded_value_type).collect()),
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(discarded_value_type(left)),
            Box::new(discarded_value_type(right)),
        )),
        Type::Intersection(left, right) => types::simplify_type(Type::Intersection(
            Box::new(discarded_value_type(left)),
            Box::new(discarded_value_type(right)),
        )),
        Type::Stack { inner, weight } => {
            types::simplify_stack_type(discarded_value_type(inner), weight.clone())
        }
        Type::EffectRow(_) => Type::unit(),
        Type::Any | Type::Never => ty.clone(),
    }
}

pub(super) fn discarded_effect_type(ty: &Type) -> Type {
    match ty {
        Type::OpenVar(_) => Type::pure_effect(),
        Type::EffectRow(items) => types::simplify_type(Type::EffectRow(
            items.iter().map(discarded_effect_type).collect(),
        )),
        Type::Stack { inner, weight } => {
            types::simplify_stack_type(discarded_effect_type(inner), weight.clone())
        }
        ty => discarded_value_type(ty),
    }
}

pub(super) fn discarded_catch_has_open_result(expr: &poly_expr::Expr, ty: &Type) -> bool {
    matches!(expr, poly_expr::Expr::Catch(_, _))
        && matches!(ty, Type::Thunk { value, .. } if matches!(value.as_ref(), Type::OpenVar(_)))
}

pub(super) struct FunctionComputationParts {
    pub(super) arg: Type,
    pub(super) arg_effect: Type,
    pub(super) ret_effect: Type,
    pub(super) ret: Type,
}

pub(super) fn function_computation_parts(ty: &Type) -> Option<FunctionComputationParts> {
    let Type::Fun {
        arg,
        arg_effect,
        ret_effect,
        ret,
    } = ty
    else {
        return None;
    };
    let (arg, arg_effect) =
        split_declared_runtime_shape(arg.as_ref().clone(), arg_effect.as_ref().clone());
    let (ret, ret_effect) =
        split_declared_runtime_shape(ret.as_ref().clone(), ret_effect.as_ref().clone());
    Some(FunctionComputationParts {
        arg,
        arg_effect,
        ret_effect,
        ret,
    })
}

pub(super) fn split_declared_runtime_shape(shape: Type, legacy_effect: Type) -> (Type, Type) {
    match shape {
        Type::Thunk { effect, value } => (*value, *effect),
        value => (value, legacy_effect),
    }
}

pub(super) fn split_function_spine(mut ty: Type, arity: usize) -> Option<(Vec<Type>, Type)> {
    let mut args = Vec::with_capacity(arity);
    for _ in 0..arity {
        let Type::Fun { arg, ret, .. } = ty else {
            return None;
        };
        args.push(*arg);
        ty = *ret;
    }
    Some((args, ty))
}

pub(super) fn unary_type(arg: Type, ret: Type) -> Type {
    types::pure_function_type(arg, ret)
}

pub(super) fn binary_type(param: Type, ret: Type) -> Type {
    function_type(vec![param.clone(), param], ret)
}

pub(super) fn function_type(args: Vec<Type>, ret: Type) -> Type {
    args.into_iter()
        .rev()
        .fold(ret, |ret, arg| types::pure_function_type(arg, ret))
}

pub(super) fn int_type() -> Type {
    con(&["int"], Vec::new())
}

pub(super) fn float_type() -> Type {
    con(&["float"], Vec::new())
}

pub(super) fn bool_type() -> Type {
    con(&["bool"], Vec::new())
}

pub(super) fn str_type() -> Type {
    std_types::str_type()
}

pub(super) fn char_type() -> Type {
    std_types::char_type()
}

pub(super) fn bytes_type() -> Type {
    std_types::bytes_type()
}

pub(super) fn path_type() -> Type {
    std_types::path_type()
}

pub(super) fn range_type() -> Type {
    std_types::range_type()
}

pub(super) fn list_type(item: Type) -> Type {
    std_types::list_type(item)
}

pub(super) fn list_view_type(item: Type) -> Type {
    std_types::list_view_type(item)
}

pub(super) fn con(path: &[&str], args: Vec<Type>) -> Type {
    Type::Con {
        path: path.iter().map(|segment| (*segment).to_string()).collect(),
        args,
    }
}

pub(super) fn record_field_type<'a>(fields: &'a [TypeField], name: &str) -> Option<&'a TypeField> {
    fields.iter().find(|field| field.name == name)
}

pub(super) fn effect_family_paths(arena: &poly_expr::Arena) -> HashSet<Vec<String>> {
    arena
        .effect_operations
        .values()
        .filter_map(|operation| effect_operation_family_path(&operation.path))
        .collect()
}

pub(super) fn effect_operation_family_path(path: &[String]) -> Option<Vec<String>> {
    (path.len() >= 2).then(|| path[..path.len() - 1].to_vec())
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

pub(super) fn record_spread_def(
    spread: &poly_expr::RecordSpread<poly_expr::DefId>,
) -> Option<poly_expr::DefId> {
    match spread {
        poly_expr::RecordSpread::Head(def) | poly_expr::RecordSpread::Tail(def) => Some(*def),
        poly_expr::RecordSpread::None => None,
    }
}

pub(super) fn same_effect_row_family(left: &Type, right: &Type) -> bool {
    let (
        Type::Con {
            path: left_path, ..
        },
        Type::Con {
            path: right_path, ..
        },
    ) = (left, right)
    else {
        return left == right;
    };
    effect_paths_same_family(left_path, right_path)
}

pub(super) fn effect_paths_same_family(left: &[String], right: &[String]) -> bool {
    effect_path_contains_family(left, right) || effect_path_contains_family(right, left)
}

pub(super) fn effect_path_contains_family(family: &[String], item: &[String]) -> bool {
    !family.is_empty() && item.starts_with(family)
}

pub(super) fn effect_row_items(effect: &Type) -> &[Type] {
    match effect {
        Type::EffectRow(items) => items,
        _ => std::slice::from_ref(effect),
    }
}

pub(super) fn effect_family_from_item(item: &Type) -> Option<EffectFamily> {
    let Type::Con { path, args } = item else {
        return None;
    };
    Some(EffectFamily {
        path: path.clone(),
        args: args.clone(),
    })
}

pub(super) fn matching_effect_row_item(item: &Type, candidates: &[Type]) -> Option<Type> {
    candidates
        .iter()
        .find(|candidate| same_effect_row_family(item, candidate))
        .cloned()
}

pub(super) fn refine_operation_type_from_handled_effect(
    ty: Type,
    operation_effect: &Type,
    handled_effect: &Type,
) -> Type {
    let mut replacements = Vec::new();
    for operation_item in effect_row_items(operation_effect) {
        for handled_item in effect_row_items(handled_effect) {
            collect_effect_arg_replacements(operation_item, handled_item, &mut replacements);
        }
    }
    replace_effect_arg_occurrences(ty, &replacements)
}

pub(super) fn collect_effect_arg_replacements(
    operation_item: &Type,
    handled_item: &Type,
    replacements: &mut Vec<(Type, Type)>,
) {
    let (
        Type::Con {
            path: operation_path,
            args: operation_args,
        },
        Type::Con {
            path: handled_path,
            args: handled_args,
        },
    ) = (operation_item, handled_item)
    else {
        return;
    };
    if operation_path != handled_path || operation_args.len() != handled_args.len() {
        return;
    }
    replacements.extend(
        operation_args
            .iter()
            .cloned()
            .zip(handled_args.iter().cloned()),
    );
}

pub(super) fn replace_effect_arg_occurrences(ty: Type, replacements: &[(Type, Type)]) -> Type {
    if let Some((_, replacement)) = replacements
        .iter()
        .find(|(needle, _)| type_replacement_key_matches(&ty, needle))
    {
        return replacement.clone();
    }
    match ty {
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(replace_effect_arg_occurrences(*arg, replacements)),
            arg_effect: Box::new(replace_effect_arg_occurrences(*arg_effect, replacements)),
            ret_effect: Box::new(replace_effect_arg_occurrences(*ret_effect, replacements)),
            ret: Box::new(replace_effect_arg_occurrences(*ret, replacements)),
        },
        Type::Thunk { effect, value } => Type::Thunk {
            effect: Box::new(replace_effect_arg_occurrences(*effect, replacements)),
            value: Box::new(replace_effect_arg_occurrences(*value, replacements)),
        },
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    optional: field.optional,
                    value: replace_effect_arg_occurrences(field.value, replacements),
                })
                .collect(),
        ),
        Type::PolyVariant(variants) => Type::PolyVariant(
            variants
                .into_iter()
                .map(|variant| TypeVariant {
                    name: variant.name,
                    payloads: variant
                        .payloads
                        .into_iter()
                        .map(|payload| replace_effect_arg_occurrences(payload, replacements))
                        .collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(|item| replace_effect_arg_occurrences(item, replacements))
                .collect(),
        ),
        Type::EffectRow(items) => Type::EffectRow(
            items
                .into_iter()
                .map(|item| replace_effect_arg_occurrences(item, replacements))
                .collect(),
        ),
        Type::Con { path, args } => Type::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| replace_effect_arg_occurrences(arg, replacements))
                .collect(),
        },
        Type::Union(left, right) => Type::Union(
            Box::new(replace_effect_arg_occurrences(*left, replacements)),
            Box::new(replace_effect_arg_occurrences(*right, replacements)),
        ),
        Type::Intersection(left, right) => Type::Intersection(
            Box::new(replace_effect_arg_occurrences(*left, replacements)),
            Box::new(replace_effect_arg_occurrences(*right, replacements)),
        ),
        Type::Stack { inner, weight } => Type::Stack {
            inner: Box::new(replace_effect_arg_occurrences(*inner, replacements)),
            weight,
        },
        Type::OpenVar(_) | Type::Any | Type::Never => ty,
    }
}

pub(super) fn type_replacement_key_matches(ty: &Type, needle: &Type) -> bool {
    matches!(needle, Type::OpenVar(_)) && ty == needle
}

pub(super) fn let_body(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
) -> Result<poly_expr::ExprId, SpecializeError> {
    match arena.defs.get(def) {
        Some(poly_expr::Def::Let {
            body: Some(body), ..
        }) => Ok(*body),
        Some(poly_expr::Def::Let { body: None, .. }) => Err(SpecializeError::MissingBody {
            def: convert_def(def),
        }),
        Some(other) => Err(SpecializeError::UnsupportedDefKind {
            def: convert_def(def),
            kind: def_kind(other),
        }),
        None => Err(SpecializeError::MissingDef {
            def: convert_def(def),
        }),
    }
}

pub(super) fn collect_pattern_defs(
    arena: &poly_expr::Arena,
    pat: poly_expr::PatId,
    out: &mut Vec<poly_expr::DefId>,
) {
    match arena.pat(pat) {
        poly_expr::Pat::Wild | poly_expr::Pat::Lit(_) | poly_expr::Pat::Ref(_) => {}
        poly_expr::Pat::Var(def) => out.push(*def),
        poly_expr::Pat::As(inner, def) => {
            collect_pattern_defs(arena, *inner, out);
            out.push(*def);
        }
        poly_expr::Pat::Tuple(items) | poly_expr::Pat::PolyVariant(_, items) => {
            for item in items {
                collect_pattern_defs(arena, *item, out);
            }
        }
        poly_expr::Pat::Con(_, payloads) => {
            for payload in payloads {
                collect_pattern_defs(arena, *payload, out);
            }
        }
        poly_expr::Pat::Or(left, right) => {
            collect_pattern_defs(arena, *left, out);
            collect_pattern_defs(arena, *right, out);
        }
        poly_expr::Pat::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix.iter().chain(suffix) {
                collect_pattern_defs(arena, *item, out);
            }
            if let Some(spread) = spread {
                collect_pattern_defs(arena, *spread, out);
            }
        }
        poly_expr::Pat::Record { fields, spread } => {
            for field in fields {
                collect_pattern_defs(arena, field.pat, out);
            }
            if let Some(def) = record_spread_def(spread) {
                out.push(def);
            }
        }
    }
}

pub(super) fn forced_computation_value_type(ty: Type) -> Type {
    match ty {
        Type::Thunk { value, .. } => *value,
        ty => ty,
    }
}

pub(super) fn raw_expr_value_type(
    arena: &poly_expr::Arena,
    solved: &SolvedTask,
    expr: poly_expr::ExprId,
) -> Option<Type> {
    let actual = solved.actual_type_of(expr)?;
    match arena.expr(expr) {
        poly_expr::Expr::App(callee, _) if callee_is_effect_operation_spine(arena, *callee) => {
            Some(actual.clone())
        }
        poly_expr::Expr::App(callee, _) if callee_is_constructor_spine(arena, *callee) => {
            Some(ComputationShape::from_runtime_type(actual).value)
        }
        poly_expr::Expr::App(callee, _) => {
            Some(raw_apply_value_type(solved, *callee).unwrap_or_else(|| actual.clone()))
        }
        poly_expr::Expr::Select(_, select) => Some(
            raw_select_value_type(arena, solved, expr, *select).unwrap_or_else(|| actual.clone()),
        ),
        poly_expr::Expr::RefSet(_, _)
        | poly_expr::Expr::Tuple(_)
        | poly_expr::Expr::Record { .. }
        | poly_expr::Expr::PolyVariant(_, _)
        | poly_expr::Expr::Case(_, _)
        | poly_expr::Expr::Catch(_, _)
        | poly_expr::Expr::Block(_, _) => Some(ComputationShape::from_runtime_type(actual).value),
        poly_expr::Expr::Lit(_)
        | poly_expr::Expr::PrimitiveOp(_)
        | poly_expr::Expr::Var(_)
        | poly_expr::Expr::Lambda(_, _) => Some(actual.clone()),
    }
}

pub(super) fn callee_is_effect_operation_spine(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
) -> bool {
    match arena.expr(expr) {
        poly_expr::Expr::Var(ref_id) => arena
            .ref_target(*ref_id)
            .is_some_and(|def| arena.effect_operations.contains_key(&def)),
        poly_expr::Expr::App(callee, _) => callee_is_effect_operation_spine(arena, *callee),
        _ => false,
    }
}

pub(super) fn callee_is_constructor_spine(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
) -> bool {
    match arena.expr(expr) {
        poly_expr::Expr::Var(ref_id) => arena
            .ref_target(*ref_id)
            .is_some_and(|def| arena.constructors.contains_key(&def)),
        poly_expr::Expr::App(callee, _) => callee_is_constructor_spine(arena, *callee),
        _ => false,
    }
}

pub(super) fn raw_apply_value_type(solved: &SolvedTask, callee: poly_expr::ExprId) -> Option<Type> {
    let callee_ty = solved
        .emitted_type_of(callee)
        .or_else(|| solved.actual_type_of(callee))?;
    let parts = function_computation_parts(callee_ty)?;
    Some(types::runtime_shape(parts.ret_effect, parts.ret))
}

pub(super) fn raw_select_value_type(
    arena: &poly_expr::Arena,
    solved: &SolvedTask,
    expr: poly_expr::ExprId,
    select: poly_expr::SelectId,
) -> Option<Type> {
    match arena.select(select).resolution {
        Some(poly_expr::SelectResolution::RecordField) => solved
            .actual_type_of(expr)
            .map(|actual| ComputationShape::from_runtime_type(actual).value),
        Some(poly_expr::SelectResolution::Method { .. }) => solved
            .select_signature(expr)
            .and_then(function_computation_parts)
            .map(|parts| types::runtime_shape(parts.ret_effect, parts.ret)),
        Some(poly_expr::SelectResolution::TypeclassMethod { .. }) => solved
            .typeclass_resolution(expr)
            .map(|resolution| &resolution.signature)
            .and_then(function_computation_parts)
            .map(|parts| types::runtime_shape(parts.ret_effect, parts.ret)),
        None => solved.actual_type_of(expr).cloned(),
    }
}

pub(super) fn raw_expr_is_computation(
    arena: &poly_expr::Arena,
    solved: &SolvedTask,
    expr: poly_expr::ExprId,
) -> bool {
    solved.is_raw_thunk_computation(expr)
        || matches!(arena.expr(expr), poly_expr::Expr::Catch(_, _))
}

pub(super) fn force_emitted_expr_if_thunk(actual: Option<&Type>, emitted: EmittedExpr) -> Expr {
    let Some(actual @ Type::Thunk { .. }) = actual else {
        return emitted.expr;
    };
    let target = ComputationShape::from_runtime_type(actual);
    let Some(current) = emitted.computation.clone() else {
        return force_expr_if_thunk(actual, emitted.expr);
    };
    if equivalent_boundary_types(&current.value, &target.value) {
        return emitted.expr;
    }
    force_emitted_value_thunk(emitted, target).expr
}

pub(super) fn force_expr_if_thunk(actual: &Type, expr: Expr) -> Expr {
    let Type::Thunk { value, .. } = actual else {
        return expr;
    };
    boundary_expr(actual, value, expr)
}

pub(super) fn same_record_boundary_shape(actual: &Type, expected: &Type) -> bool {
    let (Type::Record(actual_fields), Type::Record(expected_fields)) = (actual, expected) else {
        return false;
    };
    actual_fields.len() == expected_fields.len()
        && expected_fields
            .iter()
            .all(|expected| record_field_type(actual_fields, &expected.name).is_some())
}

pub(super) fn forced_value_shape(
    actual: &Type,
    current: &ComputationShape,
    expected: &Type,
) -> ComputationShape {
    let actual_shape = ComputationShape::from_runtime_type(actual);
    if equivalent_boundary_types(&actual_shape.value, expected) {
        return ComputationShape {
            value: expected.clone(),
            ..actual_shape
        };
    }
    let Type::Thunk { effect, .. } = &current.value else {
        return ComputationShape {
            effect: current.effect.clone(),
            value: expected.clone(),
        };
    };
    ComputationShape {
        effect: join_emitted_effects(current.effect.clone(), effect.as_ref().clone()),
        value: expected.clone(),
    }
}

pub(super) fn force_emitted_value_thunk(
    emitted: EmittedExpr,
    target: ComputationShape,
) -> EmittedExpr {
    let Some(current) = emitted.computation.clone() else {
        return emitted;
    };
    let Type::Thunk { effect, value } = current.value else {
        return EmittedExpr {
            computation: Some(target),
            ..emitted
        };
    };
    let source = runtime_effective_thunk_type(*effect, *value);
    let target = runtime_computation_type(target);
    let expr = Expr::new(ExprKind::ForceThunk {
        source,
        target: target.clone(),
        thunk: Box::new(emitted.expr),
    });
    EmittedExpr {
        expr,
        computation: Some(ComputationShape {
            effect: target.effect,
            value: target.value,
        }),
    }
}

pub(super) fn make_thunk_from_computation(
    emitted: EmittedExpr,
    target_effect: Type,
    target_value: Type,
) -> EmittedExpr {
    let Some(source) = emitted.computation.clone() else {
        return emitted;
    };
    let source = runtime_computation_type(source);
    let target = runtime_effective_thunk_type(target_effect, target_value);
    let target_ty = Type::Thunk {
        effect: Box::new(target.effect.clone()),
        value: Box::new(target.value.clone()),
    };
    let expr = Expr::new(ExprKind::MakeThunk {
        source,
        target,
        body: Box::new(emitted.expr),
    });
    EmittedExpr::pure(expr, Some(target_ty))
}

pub(super) fn runtime_computation_type(shape: ComputationShape) -> ComputationType {
    ComputationType {
        effect: close_resolved_runtime_surface(shape.effect, TypeSlotKind::Effect),
        value: close_resolved_runtime_surface(shape.value, TypeSlotKind::Value),
    }
}

pub(super) fn runtime_effective_thunk_type(effect: Type, value: Type) -> EffectiveThunkType {
    EffectiveThunkType {
        effect: close_resolved_runtime_surface(effect, TypeSlotKind::Effect),
        value: close_resolved_runtime_surface(value, TypeSlotKind::Value),
    }
}

pub(super) fn join_emitted_effects(left: Type, right: Type) -> Type {
    if left.is_pure_effect() {
        return right;
    }
    if right.is_pure_effect() {
        return left;
    }
    let mut items = effect_row_items(&left).to_vec();
    items.extend(effect_row_items(&right).iter().cloned());
    types::simplify_type(Type::EffectRow(items))
}

pub(super) fn boundary_expr(actual: &Type, expected: &Type, expr: Expr) -> Expr {
    boundary_expr_with_argument_contract(actual, expected, expr, None)
}

pub(super) fn boundary_expr_with_argument_contract(
    actual: &Type,
    expected: &Type,
    expr: Expr,
    argument_effect_contract: Option<&poly_expr::ArgEffectContract>,
) -> Expr {
    let actual = close_runtime_type_surface(
        erase_negative_only_open_vars(actual.clone()),
        TypeSlotKind::Value,
    );
    let expected = close_runtime_type_surface(
        erase_negative_only_open_vars(expected.clone()),
        TypeSlotKind::Value,
    );
    let actual = &actual;
    let expected = &expected;
    if equivalent_boundary_types(actual, expected) {
        return expr;
    }
    if let (
        Type::Thunk {
            effect: source_effect,
            value: source_value,
        },
        Type::Thunk {
            effect: target_effect,
            value: target_value,
        },
    ) = (actual, expected)
    {
        let forced = Expr::new(ExprKind::ForceThunk {
            source: EffectiveThunkType {
                effect: source_effect.as_ref().clone(),
                value: source_value.as_ref().clone(),
            },
            target: ComputationType {
                effect: source_effect.as_ref().clone(),
                value: source_value.as_ref().clone(),
            },
            thunk: Box::new(expr),
        });
        let body = if equivalent_boundary_types(source_value.as_ref(), target_value.as_ref()) {
            forced
        } else {
            boundary_expr_with_argument_contract(
                source_value.as_ref(),
                target_value.as_ref(),
                forced,
                argument_effect_contract,
            )
        };
        return Expr::new(ExprKind::MakeThunk {
            source: ComputationType {
                effect: target_effect.as_ref().clone(),
                value: target_value.as_ref().clone(),
            },
            target: EffectiveThunkType {
                effect: target_effect.as_ref().clone(),
                value: target_value.as_ref().clone(),
            },
            body: Box::new(body),
        });
    }
    if let Type::Thunk { effect, value } = expected
        && equivalent_boundary_types(actual, value.as_ref())
    {
        return Expr::new(ExprKind::MakeThunk {
            source: ComputationType {
                effect: effect.as_ref().clone(),
                value: actual.clone(),
            },
            target: EffectiveThunkType {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            body: Box::new(expr),
        });
    }
    if let Type::Thunk { effect, value } = actual
        && equivalent_boundary_types(value.as_ref(), expected)
    {
        return Expr::new(ExprKind::ForceThunk {
            source: EffectiveThunkType {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            target: ComputationType {
                effect: effect.as_ref().clone(),
                value: expected.clone(),
            },
            thunk: Box::new(expr),
        });
    }
    if function_boundary_types(actual, expected) {
        return Expr::new(ExprKind::FunctionAdapter {
            source: actual.clone(),
            target: expected.clone(),
            function: Box::new(expr),
            hygiene: hygiene::function_adapter_hygiene_with_argument_contract(
                actual,
                expected,
                argument_effect_contract,
            ),
        });
    }
    Expr::new(ExprKind::Coerce {
        source: actual.clone(),
        target: expected.clone(),
        expr: Box::new(expr),
    })
}
