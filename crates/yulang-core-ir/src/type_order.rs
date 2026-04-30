use crate::{Name, Path, Type};

pub fn can_widen_named_leaves(actual: &str, expected: &str) -> bool {
    actual == expected || is_reachable_named_leaf(actual, expected)
}

pub fn join_named_leaves(left: &str, right: &str) -> Option<String> {
    if left == right {
        return Some(left.to_string());
    }
    if can_widen_named_leaves(left, right) {
        return Some(right.to_string());
    }
    if can_widen_named_leaves(right, left) {
        return Some(left.to_string());
    }

    let left_supertypes = named_supertype_chain(left);
    let right_supertypes = named_supertype_chain(right);
    let common = left_supertypes
        .iter()
        .find(|left_name| right_supertypes.contains(left_name))?;
    Some((*common).to_string())
}

pub fn can_widen_named_paths(actual: &Path, expected: &Path) -> bool {
    let Some(actual_leaf) = named_leaf(actual) else {
        return false;
    };
    let Some(expected_leaf) = named_leaf(expected) else {
        return false;
    };
    can_widen_named_leaves(actual_leaf, expected_leaf)
}

pub fn join_named_paths(left: &Path, right: &Path) -> Option<Path> {
    let left_leaf = named_leaf(left)?;
    let right_leaf = named_leaf(right)?;
    let joined = join_named_leaves(left_leaf, right_leaf)?;
    if joined == left_leaf {
        if can_widen_named_paths(right, left) {
            return Some(left.clone());
        }
        return Some(Path::from_name(Name(joined)));
    }
    if joined == right_leaf && can_widen_named_paths(left, right) {
        return Some(right.clone());
    }
    Some(Path::from_name(Name(joined)))
}

pub fn join_types(left: &Type, right: &Type) -> Option<Type> {
    match (left, right) {
        (
            Type::Named {
                path: left_path,
                args: left_args,
            },
            Type::Named {
                path: right_path,
                args: right_args,
            },
        ) if left_args.is_empty() && right_args.is_empty() => Some(Type::Named {
            path: join_named_paths(left_path, right_path)?,
            args: Vec::new(),
        }),
        _ => None,
    }
}

pub fn normalize_union_members(items: Vec<Type>) -> Vec<Type> {
    let mut out = items;
    loop {
        let mut changed = false;
        'scan: for left in 0..out.len() {
            for right in (left + 1)..out.len() {
                if let Some(joined) = join_types(&out[left], &out[right]) {
                    out[left] = joined;
                    out.remove(right);
                    changed = true;
                    break 'scan;
                }
            }
        }
        if !changed {
            break;
        }
    }
    out
}

fn named_leaf(path: &Path) -> Option<&str> {
    path.segments.last().map(|name| name.0.as_str())
}

fn is_reachable_named_leaf(actual: &str, expected: &str) -> bool {
    named_supertype_chain(actual)
        .into_iter()
        .any(|name| name == expected)
}

fn named_supertype_chain(name: &str) -> Vec<&'static str> {
    let mut out = vec![intern_named_leaf(name)];
    let mut cursor = name;
    while let Some(next) = direct_named_supertypes(cursor).first().copied() {
        if out.contains(&next) {
            break;
        }
        out.push(next);
        cursor = next;
    }
    out
}

fn direct_named_supertypes(name: &str) -> &'static [&'static str] {
    match name {
        "int" => &["float"],
        _ => &[],
    }
}

fn intern_named_leaf(name: &str) -> &'static str {
    match name {
        "int" => "int",
        "float" => "float",
        "bool" => "bool",
        "unit" => "unit",
        "str" => "str",
        other => Box::leak(other.to_string().into_boxed_str()),
    }
}

#[cfg(test)]
mod tests {
    use super::{can_widen_named_paths, join_named_paths, join_types, normalize_union_members};
    use crate::{Name, Path, Type};

    fn named(name: &str) -> Type {
        Type::Named {
            path: Path::from_name(Name(name.to_string())),
            args: Vec::new(),
        }
    }

    #[test]
    fn joins_int_and_float_to_float() {
        let joined = join_named_paths(
            &Path::from_name(Name("int".to_string())),
            &Path::from_name(Name("float".to_string())),
        )
        .expect("join");
        assert_eq!(joined, Path::from_name(Name("float".to_string())));
    }

    #[test]
    fn widens_int_to_float() {
        assert!(can_widen_named_paths(
            &Path::from_name(Name("int".to_string())),
            &Path::from_name(Name("float".to_string())),
        ));
    }

    #[test]
    fn joins_named_types_to_float() {
        assert_eq!(
            join_types(&named("int"), &named("float")),
            Some(named("float"))
        );
    }

    #[test]
    fn normalizes_union_members_by_join() {
        assert_eq!(
            normalize_union_members(vec![named("int"), named("float")]),
            vec![named("float")]
        );
    }
}
