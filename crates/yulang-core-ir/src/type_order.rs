use crate::{Name, Path, Type};

pub fn can_widen_named_paths(actual: &Path, expected: &Path) -> bool {
    actual == expected || is_standard_int_path(actual) && is_standard_float_path(expected)
}

pub fn join_named_paths(left: &Path, right: &Path) -> Option<Path> {
    if left == right {
        return Some(left.clone());
    }
    if is_standard_int_path(left) && is_standard_float_path(right)
        || is_standard_float_path(left) && is_standard_int_path(right)
    {
        return Some(standard_float_path());
    }
    None
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

fn is_standard_int_path(path: &Path) -> bool {
    path == &standard_int_path()
}

fn is_standard_float_path(path: &Path) -> bool {
    path == &standard_float_path()
}

fn standard_int_path() -> Path {
    Path::from_name(Name("int".to_string()))
}

fn standard_float_path() -> Path {
    Path::from_name(Name("float".to_string()))
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
    fn does_not_widen_by_leaf_name() {
        assert!(!can_widen_named_paths(
            &Path::new(vec![Name("user".to_string()), Name("int".to_string())]),
            &Path::from_name(Name("float".to_string())),
        ));
        assert_eq!(
            join_named_paths(
                &Path::new(vec![Name("user".to_string()), Name("int".to_string())]),
                &Path::from_name(Name("float".to_string())),
            ),
            None
        );
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
