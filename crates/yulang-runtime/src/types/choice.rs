use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoundsChoice {
    RuntimeValue,
    VisiblePrincipal,
    TirEvidence,
    MonomorphicExpected,
    ValidationEvidence,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TypeChoice {
    RuntimeValue,
    VisiblePrincipal,
    Substitution,
}

pub(crate) fn choose_bounds_type(
    bounds: &core_ir::TypeBounds,
    choice: BoundsChoice,
) -> Option<core_ir::Type> {
    choose_bounds_pair(
        bounds.lower.as_deref().cloned(),
        bounds.upper.as_deref().cloned(),
        choice,
    )
}

pub(crate) fn choose_bounds_pair(
    lower: Option<core_ir::Type>,
    upper: Option<core_ir::Type>,
    choice: BoundsChoice,
) -> Option<core_ir::Type> {
    match (lower, upper) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower),
        (Some(lower), Some(upper)) => choose_distinct_bounds(lower, upper, choice),
        (Some(lower), None) => choose_single_lower_bound(lower, choice),
        (None, Some(upper)) => Some(upper),
        (None, None) => None,
    }
}

pub(crate) fn choose_core_type(
    left: core_ir::Type,
    right: core_ir::Type,
    choice: TypeChoice,
) -> core_ir::Type {
    match choice {
        TypeChoice::RuntimeValue => choose_runtime_type(left, right),
        TypeChoice::VisiblePrincipal => choose_visible_type(left, right),
        TypeChoice::Substitution => choose_substitution_type(left, right),
    }
}

pub(crate) fn choose_optional_core_type(
    left: Option<core_ir::Type>,
    right: Option<core_ir::Type>,
    choice: TypeChoice,
) -> Option<core_ir::Type> {
    match (left, right) {
        (Some(left), Some(right)) => Some(choose_core_type(left, right, choice)),
        (Some(ty), None) | (None, Some(ty)) => Some(ty),
        (None, None) => None,
    }
}

pub(crate) fn choose_core_type_candidate(
    current: Option<core_ir::Type>,
    candidate: core_ir::Type,
    choice: TypeChoice,
) -> Option<core_ir::Type> {
    match current {
        Some(current) => Some(choose_core_type(current, candidate, choice)),
        None => Some(candidate),
    }
}

pub(crate) fn core_type_is_hole(ty: &core_ir::Type) -> bool {
    core_type_is_inference_hole(ty)
}

pub(crate) fn hir_type_is_hole(ty: &RuntimeType) -> bool {
    runtime_type_is_inference_hole(ty)
}

#[cfg(test)]
fn type_hole_count(ty: &core_ir::Type) -> usize {
    match ty {
        core_ir::Type::Var(_) => 1,
        core_ir::Type::Any => 0,
        core_ir::Type::Named { args, .. } => args.iter().map(type_arg_hole_count).sum(),
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_hole_count(param)
                + type_hole_count(param_effect)
                + type_hole_count(ret_effect)
                + type_hole_count(ret)
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().map(type_hole_count).sum()
        }
        core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .map(|field| type_hole_count(&field.value))
                .sum::<usize>()
                + record
                    .spread
                    .as_ref()
                    .map(record_spread_hole_count)
                    .unwrap_or(0)
        }
        core_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .flat_map(|case| &case.payloads)
                .map(type_hole_count)
                .sum::<usize>()
                + variant.tail.as_deref().map(type_hole_count).unwrap_or(0)
        }
        core_ir::Type::Row { items, tail } => {
            items.iter().map(type_hole_count).sum::<usize>() + type_hole_count(tail)
        }
        core_ir::Type::Recursive { body, .. } => type_hole_count(body),
        core_ir::Type::Never => 0,
    }
}

pub(crate) fn type_imprecision_count(ty: &core_ir::Type) -> usize {
    match ty {
        core_ir::Type::Any | core_ir::Type::Var(_) => 1,
        core_ir::Type::Named { args, .. } => args.iter().map(type_arg_imprecision_count).sum(),
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_imprecision_count(param)
                + type_imprecision_count(param_effect)
                + type_imprecision_count(ret_effect)
                + type_imprecision_count(ret)
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().map(type_imprecision_count).sum()
        }
        core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .map(|field| type_imprecision_count(&field.value))
                .sum::<usize>()
                + record
                    .spread
                    .as_ref()
                    .map(record_spread_imprecision_count)
                    .unwrap_or(0)
        }
        core_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .flat_map(|case| &case.payloads)
                .map(type_imprecision_count)
                .sum::<usize>()
                + variant
                    .tail
                    .as_deref()
                    .map(type_imprecision_count)
                    .unwrap_or(0)
        }
        core_ir::Type::Row { items, tail } => {
            items.iter().map(type_imprecision_count).sum::<usize>() + type_imprecision_count(tail)
        }
        core_ir::Type::Recursive { body, .. } => type_imprecision_count(body),
        core_ir::Type::Never => 0,
    }
}

pub(crate) fn hir_type_imprecision_count(ty: &RuntimeType) -> usize {
    match ty {
        RuntimeType::Unknown => 1,
        RuntimeType::Core(ty) => type_imprecision_count(ty),
        RuntimeType::Fun { param, ret } => {
            hir_type_imprecision_count(param) + hir_type_imprecision_count(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            type_imprecision_count(effect) + hir_type_imprecision_count(value)
        }
    }
}

pub(crate) fn type_choice_rank(ty: &core_ir::Type, choice: TypeChoice) -> u8 {
    match ty {
        core_ir::Type::Fun { .. } => 8,
        core_ir::Type::Tuple(_) | core_ir::Type::Record(_) | core_ir::Type::Variant(_) => 7,
        core_ir::Type::Named { .. } => 6,
        core_ir::Type::Never => 2,
        core_ir::Type::Var(_) if matches!(choice, TypeChoice::Substitution) => 1,
        core_ir::Type::Recursive { body, .. } => type_choice_rank(body, choice),
        core_ir::Type::Any
        | core_ir::Type::Var(_)
        | core_ir::Type::Union(_)
        | core_ir::Type::Inter(_)
        | core_ir::Type::Row { .. } => 0,
    }
}

fn choose_distinct_bounds(
    lower: core_ir::Type,
    upper: core_ir::Type,
    choice: BoundsChoice,
) -> Option<core_ir::Type> {
    match choice {
        BoundsChoice::RuntimeValue => {
            if is_runtime_floor(&lower) {
                return Some(upper);
            }
            if type_compatible(&upper, &lower) || type_compatible(&lower, &upper) {
                return Some(lower);
            }
            choose_core_type_candidate(Some(upper), lower, TypeChoice::RuntimeValue)
        }
        BoundsChoice::VisiblePrincipal | BoundsChoice::MonomorphicExpected => Some(lower),
        BoundsChoice::TirEvidence => Some(upper),
        BoundsChoice::ValidationEvidence => {
            if type_compatible(&lower, &upper) {
                Some(lower)
            } else {
                Some(upper)
            }
        }
    }
}

fn choose_single_lower_bound(lower: core_ir::Type, choice: BoundsChoice) -> Option<core_ir::Type> {
    match choice {
        BoundsChoice::RuntimeValue if is_runtime_floor(&lower) => None,
        _ => Some(lower),
    }
}

fn choose_runtime_type(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    if matches!(left, core_ir::Type::Never) && matches!(right, core_ir::Type::Var(_)) {
        return right;
    }
    if matches!(left, core_ir::Type::Var(_)) && matches!(right, core_ir::Type::Never) {
        return left;
    }
    if type_compatible(&left, &right) {
        return choose_by_rank(left, right, TypeChoice::RuntimeValue);
    }
    if type_choice_rank(&right, TypeChoice::RuntimeValue)
        > type_choice_rank(&left, TypeChoice::RuntimeValue)
    {
        right
    } else {
        left
    }
}

fn choose_visible_type(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    match (core_type_is_hole(&left), core_type_is_hole(&right)) {
        (true, false) => return right,
        (false, true) => return left,
        _ => {}
    }
    let left_rank = type_choice_rank(&left, TypeChoice::VisiblePrincipal);
    let right_rank = type_choice_rank(&right, TypeChoice::VisiblePrincipal);
    match left_rank.cmp(&right_rank) {
        std::cmp::Ordering::Less => return right,
        std::cmp::Ordering::Greater => return left,
        std::cmp::Ordering::Equal => {}
    }
    if type_imprecision_count(&right) < type_imprecision_count(&left) {
        right
    } else {
        left
    }
}

fn choose_substitution_type(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    if left == right {
        return left;
    }
    if matches!(left, core_ir::Type::Never) && !matches!(right, core_ir::Type::Never) {
        return right;
    }
    if matches!(right, core_ir::Type::Never) {
        return left;
    }
    if type_compatible(&left, &right) || type_compatible(&right, &left) {
        choose_by_rank(left, right, TypeChoice::Substitution)
    } else {
        left
    }
}

fn choose_by_rank(left: core_ir::Type, right: core_ir::Type, choice: TypeChoice) -> core_ir::Type {
    if type_choice_rank(&right, choice) > type_choice_rank(&left, choice) {
        right
    } else {
        left
    }
}

#[cfg(test)]
fn type_arg_hole_count(arg: &core_ir::TypeArg) -> usize {
    match arg {
        core_ir::TypeArg::Type(ty) => type_hole_count(ty),
        core_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().map(type_hole_count).unwrap_or(0)
                + bounds.upper.as_deref().map(type_hole_count).unwrap_or(0)
        }
    }
}

#[cfg(test)]
fn record_spread_hole_count(spread: &core_ir::RecordSpread) -> usize {
    match spread {
        core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => type_hole_count(ty),
    }
}

fn type_arg_imprecision_count(arg: &core_ir::TypeArg) -> usize {
    match arg {
        core_ir::TypeArg::Type(ty) => type_imprecision_count(ty),
        core_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_deref()
                .map(type_imprecision_count)
                .unwrap_or(0)
                + bounds
                    .upper
                    .as_deref()
                    .map(type_imprecision_count)
                    .unwrap_or(0)
        }
    }
}

fn record_spread_imprecision_count(spread: &core_ir::RecordSpread) -> usize {
    match spread {
        core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
            type_imprecision_count(ty)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounds_choice_names_upper_and_lower_priorities() {
        let lower = named("int");
        let upper = core_ir::Type::Any;
        let bounds = core_ir::TypeBounds {
            lower: Some(Box::new(lower.clone())),
            upper: Some(Box::new(upper.clone())),
        };

        assert_eq!(
            choose_bounds_type(&bounds, BoundsChoice::VisiblePrincipal),
            Some(lower.clone())
        );
        assert_eq!(
            choose_bounds_type(&bounds, BoundsChoice::MonomorphicExpected),
            Some(lower)
        );
        assert_eq!(
            choose_bounds_type(&bounds, BoundsChoice::TirEvidence),
            Some(upper)
        );
    }

    #[test]
    fn runtime_bounds_skip_unusable_lower_floor() {
        let bounds = core_ir::TypeBounds {
            lower: Some(Box::new(core_ir::Type::Never)),
            upper: Some(Box::new(named("int"))),
        };

        assert_eq!(
            choose_bounds_type(&bounds, BoundsChoice::RuntimeValue),
            Some(named("int"))
        );
    }

    #[test]
    fn visible_type_choice_prefers_concrete_shapes_over_holes() {
        assert_eq!(
            choose_core_type(
                core_ir::Type::Any,
                named("int"),
                TypeChoice::VisiblePrincipal
            ),
            named("int")
        );
    }

    #[test]
    fn hole_count_does_not_count_any_but_imprecision_does() {
        assert_eq!(type_hole_count(&core_ir::Type::Any), 0);
        assert_eq!(type_imprecision_count(&core_ir::Type::Any), 1);
        assert_eq!(
            type_hole_count(&core_ir::Type::Var(core_ir::TypeVar("a".to_string()))),
            1
        );
    }

    #[test]
    fn substitution_type_choice_keeps_non_never_candidate() {
        assert_eq!(
            choose_core_type(core_ir::Type::Never, named("int"), TypeChoice::Substitution),
            named("int")
        );
        assert_eq!(
            choose_core_type(named("int"), core_ir::Type::Never, TypeChoice::Substitution),
            named("int")
        );
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
