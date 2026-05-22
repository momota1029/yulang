use super::*;

pub(crate) fn should_thunk_effect(effect: &typed_ir::Type) -> bool {
    !effect_is_empty(effect) && !core_type_is_unknown(effect) && !core_type_is_top(effect)
}

pub(crate) fn effect_is_empty(effect: &typed_ir::Type) -> bool {
    match effect {
        effect if core_type_is_never(effect) => true,
        typed_ir::Type::Row { items, tail } => items.is_empty() && effect_is_empty(tail),
        typed_ir::Type::Recursive { body, .. } => effect_is_empty(body),
        _ => false,
    }
}

pub(crate) fn type_is_effect_like(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Row { .. } => true,
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            !items.is_empty() && items.iter().all(type_is_effect_like)
        }
        typed_ir::Type::Recursive { body, .. } => type_is_effect_like(body),
        _ => false,
    }
}

pub(crate) fn effect_compatible(expected: &typed_ir::Type, actual: &typed_ir::Type) -> bool {
    if core_type_contains_unknown(expected) || core_type_contains_unknown(actual) {
        return true;
    }
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
    if effect_has_open_var(actual) {
        return actual_paths.iter().all(|actual| {
            expected_paths
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

pub(crate) fn effect_paths(effect: &typed_ir::Type) -> Vec<typed_ir::Path> {
    let mut paths = Vec::new();
    collect_effect_paths(effect, &mut paths);
    paths
}

pub(crate) fn collect_effect_paths(effect: &typed_ir::Type, paths: &mut Vec<typed_ir::Path>) {
    match effect {
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_effect_paths(item, paths);
            }
            collect_effect_paths(tail, paths);
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_effect_paths(item, paths);
            }
        }
        typed_ir::Type::Recursive { body, .. } => collect_effect_paths(body, paths),
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

pub(crate) fn effect_path(ty: &typed_ir::Type) -> Option<typed_ir::Path> {
    match ty {
        typed_ir::Type::Named { path, .. } => Some(path.clone()),
        _ => None,
    }
}

pub(crate) fn effect_paths_match(left: &typed_ir::Path, right: &typed_ir::Path) -> bool {
    left == right
        || qualified_prefix_effect_paths_match(left, right)
        || qualified_prefix_effect_paths_match(right, left)
}

fn qualified_prefix_effect_paths_match(parent: &typed_ir::Path, child: &typed_ir::Path) -> bool {
    effect_path_can_match_child_prefix(parent)
        && child.segments.len() > parent.segments.len()
        && child.segments.starts_with(parent.segments.as_slice())
}

fn effect_path_can_match_child_prefix(path: &typed_ir::Path) -> bool {
    path.segments.len() > 1
        || path.segments.first().is_some_and(|name| {
            name.0.starts_with('#') || name.0.starts_with('&') && name.0.contains('#')
        })
}

fn effect_has_open_var(effect: &typed_ir::Type) -> bool {
    match effect {
        effect if core_type_is_top(effect) || core_type_is_inference_var(effect) => true,
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(effect_has_open_var) || effect_has_open_var(tail)
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            items.iter().any(effect_has_open_var)
        }
        typed_ir::Type::Recursive { body, .. } => effect_has_open_var(body),
        _ => false,
    }
}

pub(crate) fn effect_row(items: Vec<typed_ir::Type>, tail: typed_ir::Type) -> typed_ir::Type {
    if items.is_empty() {
        return tail;
    }
    typed_ir::Type::Row {
        items,
        tail: Box::new(tail),
    }
}

pub(crate) fn effect_row_from_items(items: Vec<typed_ir::Type>) -> typed_ir::Type {
    effect_row(items, typed_ir::Type::Never)
}
