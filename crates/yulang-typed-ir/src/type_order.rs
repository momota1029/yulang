use crate::{Name, Path, Type};

pub fn can_widen_named_paths(actual: &Path, expected: &Path) -> bool {
    actual == expected
        || numeric_type_family(actual).is_some_and(|actual| {
            numeric_type_family(expected).is_some_and(|expected| actual.rank() <= expected.rank())
        })
}

pub fn join_named_paths(left: &Path, right: &Path) -> Option<Path> {
    if left == right {
        return Some(left.clone());
    }
    if let (Some(left), Some(right)) = (numeric_type_family(left), numeric_type_family(right)) {
        return NumericTypeFamily::from_rank(left.rank().max(right.rank())).map(numeric_type_path);
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NumericTypeFamily {
    Int,
    Frac,
    Float,
}

impl NumericTypeFamily {
    fn rank(self) -> u8 {
        match self {
            Self::Int => 0,
            Self::Frac => 1,
            Self::Float => 2,
        }
    }

    fn from_rank(rank: u8) -> Option<Self> {
        match rank {
            0 => Some(Self::Int),
            1 => Some(Self::Frac),
            2 => Some(Self::Float),
            _ => None,
        }
    }
}

fn numeric_type_family(path: &Path) -> Option<NumericTypeFamily> {
    match path.segments.as_slice() {
        [Name(name)] if name == "int" => Some(NumericTypeFamily::Int),
        [Name(std), Name(module), Name(name)]
            if std == "std" && module == "int" && name == "int" =>
        {
            Some(NumericTypeFamily::Int)
        }
        [Name(name)] if name == "float" => Some(NumericTypeFamily::Float),
        [Name(std), Name(module), Name(name)]
            if std == "std" && module == "float" && name == "float" =>
        {
            Some(NumericTypeFamily::Float)
        }
        [Name(std), Name(module), Name(name)]
            if std == "std" && module == "frac" && name == "frac" =>
        {
            Some(NumericTypeFamily::Frac)
        }
        _ => None,
    }
}

fn numeric_type_path(family: NumericTypeFamily) -> Path {
    match family {
        NumericTypeFamily::Int => Path::from_name(Name("int".to_string())),
        NumericTypeFamily::Float => Path::from_name(Name("float".to_string())),
        NumericTypeFamily::Frac => Path::new(vec![
            Name("std".to_string()),
            Name("frac".to_string()),
            Name("frac".to_string()),
        ]),
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
    fn widens_qualified_numeric_paths() {
        let std_int = Path::new(vec![
            Name("std".to_string()),
            Name("int".to_string()),
            Name("int".to_string()),
        ]);
        let std_float = Path::new(vec![
            Name("std".to_string()),
            Name("float".to_string()),
            Name("float".to_string()),
        ]);

        assert!(can_widen_named_paths(&std_int, &std_float));
        assert!(can_widen_named_paths(
            &std_int,
            &Path::from_name(Name("float".to_string())),
        ));
        assert!(can_widen_named_paths(
            &Path::from_name(Name("int".to_string())),
            &std_float,
        ));
        assert_eq!(
            join_named_paths(&std_int, &std_float),
            Some(Path::from_name(Name("float".to_string())))
        );
    }

    #[test]
    fn widens_int_to_frac_and_frac_to_float() {
        let frac = Path::new(vec![
            Name("std".to_string()),
            Name("frac".to_string()),
            Name("frac".to_string()),
        ]);
        assert!(can_widen_named_paths(
            &Path::from_name(Name("int".to_string())),
            &frac,
        ));
        assert!(can_widen_named_paths(
            &frac,
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
