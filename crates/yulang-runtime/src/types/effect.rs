use super::*;

pub(crate) fn should_thunk_effect(effect: &core_ir::Type) -> bool {
    !effect_is_empty(effect) && !matches!(effect, core_ir::Type::Any)
}

pub(crate) fn effect_is_empty(effect: &core_ir::Type) -> bool {
    match effect {
        core_ir::Type::Never => true,
        core_ir::Type::Named { path, args } => {
            args.is_empty()
                && matches!(
                    path.segments.as_slice(),
                    [core_ir::Name(name)] if name == "never"
                )
        }
        core_ir::Type::Row { items, tail } => items.is_empty() && effect_is_empty(tail),
        core_ir::Type::Recursive { body, .. } => effect_is_empty(body),
        _ => false,
    }
}

pub(crate) fn effect_compatible(expected: &core_ir::Type, actual: &core_ir::Type) -> bool {
    if type_compatible(expected, actual) || effect_is_empty(actual) {
        return true;
    }
    if effect_is_empty(expected) {
        return effect_is_empty(actual);
    }
    let expected_paths = effect_paths(expected);
    let actual_paths = effect_paths(actual);
    if expected_paths.is_empty() || actual_paths.is_empty() {
        return false;
    }
    if effect_has_open_var(expected) {
        return true;
    }
    if expected_paths.iter().any(is_internal_loop_parent_effect) {
        return true;
    }
    if effect_has_open_var(actual) {
        return actual_paths.iter().all(|actual| {
            is_internal_loop_parent_effect(actual)
                || expected_paths
                    .iter()
                    .any(|expected| effect_paths_match(expected, actual))
        });
    }
    actual_paths.iter().all(|actual| {
        expected_paths
            .iter()
            .any(|expected| effect_paths_match(expected, actual))
    })
}

pub(crate) fn effect_paths(effect: &core_ir::Type) -> Vec<core_ir::Path> {
    let mut paths = Vec::new();
    collect_effect_paths(effect, &mut paths);
    paths
}

pub(crate) fn collect_effect_paths(effect: &core_ir::Type, paths: &mut Vec<core_ir::Path>) {
    match effect {
        core_ir::Type::Row { items, tail } => {
            for item in items {
                collect_effect_paths(item, paths);
            }
            collect_effect_paths(tail, paths);
        }
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_effect_paths(item, paths);
            }
        }
        core_ir::Type::Recursive { body, .. } => collect_effect_paths(body, paths),
        effect => {
            if let Some(path) = effect_path(effect) {
                if !paths
                    .iter()
                    .any(|existing| effect_paths_match(existing, &path))
                {
                    paths.push(path);
                }
            }
        }
    }
}

pub(crate) fn effect_path(ty: &core_ir::Type) -> Option<core_ir::Path> {
    match ty {
        core_ir::Type::Named { path, .. } => Some(path.clone()),
        _ => None,
    }
}

pub(crate) fn effect_paths_match(left: &core_ir::Path, right: &core_ir::Path) -> bool {
    left == right
        || left.segments.ends_with(right.segments.as_slice())
        || right.segments.ends_with(left.segments.as_slice())
        || qualified_prefix_effect_paths_match(left, right)
        || qualified_prefix_effect_paths_match(right, left)
}

fn qualified_prefix_effect_paths_match(parent: &core_ir::Path, child: &core_ir::Path) -> bool {
    parent.segments.len() > 1
        && child.segments.len() > parent.segments.len()
        && child.segments.starts_with(parent.segments.as_slice())
}

fn is_internal_loop_parent_effect(path: &core_ir::Path) -> bool {
    matches!(
        path.segments.as_slice(),
        [core_ir::Name(std), core_ir::Name(flow), core_ir::Name(loop_)]
            if std == "std" && flow == "flow" && loop_ == "loop"
    )
}

fn effect_has_open_var(effect: &core_ir::Type) -> bool {
    match effect {
        core_ir::Type::Any | core_ir::Type::Var(_) => true,
        core_ir::Type::Row { items, tail } => {
            items.iter().any(effect_has_open_var) || effect_has_open_var(tail)
        }
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().any(effect_has_open_var)
        }
        core_ir::Type::Recursive { body, .. } => effect_has_open_var(body),
        _ => false,
    }
}

pub(crate) fn effect_row(items: Vec<core_ir::Type>, tail: core_ir::Type) -> core_ir::Type {
    if items.is_empty() {
        return tail;
    }
    core_ir::Type::Row {
        items,
        tail: Box::new(tail),
    }
}

pub(crate) fn effect_row_from_items(items: Vec<core_ir::Type>) -> core_ir::Type {
    effect_row(items, core_ir::Type::Never)
}
