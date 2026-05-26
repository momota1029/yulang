use std::collections::HashMap;

use crate::{Name, Path, PrimitiveTypeFamily, PrimitiveTypeGraphNode, Type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrimitiveTypeOrder {
    family_by_path: HashMap<Path, PrimitiveTypeFamily>,
    path_by_family: HashMap<PrimitiveTypeFamily, Path>,
}

impl PrimitiveTypeOrder {
    pub fn standard() -> Self {
        let mut order = Self {
            family_by_path: HashMap::new(),
            path_by_family: HashMap::new(),
        };
        for node in standard_primitive_type_nodes() {
            order.insert(node.family, node.path);
        }
        order
    }

    pub fn from_primitive_types(nodes: &[PrimitiveTypeGraphNode]) -> Self {
        let mut order = Self::standard();
        for node in nodes {
            order.insert(node.family, node.path.clone());
        }
        order
    }

    pub fn can_widen_named_paths(&self, actual: &Path, expected: &Path) -> bool {
        actual == expected
            || self
                .family_pair(actual, expected)
                .is_some_and(|(actual, expected)| actual.can_widen_to(expected))
    }

    pub fn join_named_paths(&self, left: &Path, right: &Path) -> Option<Path> {
        if left == right {
            return Some(left.clone());
        }
        let (left_family, right_family) = self.family_pair(left, right)?;
        let joined = left_family.join(right_family)?;
        self.path_by_family.get(&joined).cloned()
    }

    pub fn join_types(&self, left: &Type, right: &Type) -> Option<Type> {
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
                path: self.join_named_paths(left_path, right_path)?,
                args: Vec::new(),
            }),
            _ => None,
        }
    }

    pub fn normalize_union_members(&self, items: Vec<Type>) -> Vec<Type> {
        let mut out = items;
        loop {
            let mut changed = false;
            'scan: for left in 0..out.len() {
                for right in (left + 1)..out.len() {
                    if let Some(joined) = self.join_types(&out[left], &out[right]) {
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

    fn insert(&mut self, family: PrimitiveTypeFamily, path: Path) {
        if let Some(previous) = self.path_by_family.insert(family, path.clone()) {
            self.family_by_path.remove(&previous);
        }
        self.family_by_path.insert(path.clone(), family);
    }

    fn family_pair(
        &self,
        left: &Path,
        right: &Path,
    ) -> Option<(PrimitiveTypeFamily, PrimitiveTypeFamily)> {
        Some((
            *self.family_by_path.get(left)?,
            *self.family_by_path.get(right)?,
        ))
    }
}

impl Default for PrimitiveTypeOrder {
    fn default() -> Self {
        Self::standard()
    }
}

impl PrimitiveTypeFamily {
    fn join(self, other: Self) -> Option<Self> {
        if self.can_widen_to(other) {
            return Some(other);
        }
        if other.can_widen_to(self) {
            return Some(self);
        }
        let (left, right) = self.numeric_rank().zip(other.numeric_rank())?;
        Self::from_numeric_rank(left.max(right))
    }

    fn can_widen_to(self, expected: Self) -> bool {
        self == expected
            || self
                .numeric_rank()
                .zip(expected.numeric_rank())
                .is_some_and(|(actual, expected)| actual <= expected)
            || matches!((self, expected), (Self::Str, Self::Path))
    }

    fn numeric_rank(self) -> Option<u8> {
        match self {
            Self::Int => Some(0),
            Self::Frac => Some(1),
            Self::Float => Some(2),
            _ => None,
        }
    }

    fn from_numeric_rank(rank: u8) -> Option<Self> {
        match rank {
            0 => Some(Self::Int),
            1 => Some(Self::Frac),
            2 => Some(Self::Float),
            _ => None,
        }
    }
}

pub fn can_widen_named_paths(actual: &Path, expected: &Path) -> bool {
    PrimitiveTypeOrder::standard().can_widen_named_paths(actual, expected)
}

pub fn join_named_paths(left: &Path, right: &Path) -> Option<Path> {
    PrimitiveTypeOrder::standard().join_named_paths(left, right)
}

pub fn join_types(left: &Type, right: &Type) -> Option<Type> {
    PrimitiveTypeOrder::standard().join_types(left, right)
}

pub fn normalize_union_members(items: Vec<Type>) -> Vec<Type> {
    PrimitiveTypeOrder::standard().normalize_union_members(items)
}

fn standard_primitive_type_nodes() -> Vec<PrimitiveTypeGraphNode> {
    vec![
        PrimitiveTypeGraphNode {
            family: PrimitiveTypeFamily::Int,
            path: bare_path("int"),
        },
        PrimitiveTypeGraphNode {
            family: PrimitiveTypeFamily::Frac,
            path: std_path("frac", "frac"),
        },
        PrimitiveTypeGraphNode {
            family: PrimitiveTypeFamily::Float,
            path: bare_path("float"),
        },
        PrimitiveTypeGraphNode {
            family: PrimitiveTypeFamily::Str,
            path: std_path("str", "str"),
        },
        PrimitiveTypeGraphNode {
            family: PrimitiveTypeFamily::Path,
            path: std_path("path", "path"),
        },
    ]
}

fn bare_path(name: &str) -> Path {
    Path::from_name(Name(name.to_string()))
}

fn std_path(module: &str, name: &str) -> Path {
    Path::new(vec![
        Name("std".to_string()),
        Name(module.to_string()),
        Name(name.to_string()),
    ])
}

#[cfg(test)]
mod tests {
    use super::{
        PrimitiveTypeOrder, can_widen_named_paths, join_named_paths, join_types,
        normalize_union_members,
    };
    use crate::{Name, Path, PrimitiveTypeFamily, PrimitiveTypeGraphNode, Type};

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
    fn widens_int_to_frac_and_frac_to_float() {
        let frac = path("std::frac::frac");
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
    fn widens_str_to_path() {
        assert!(can_widen_named_paths(
            &path("std::str::str"),
            &path("std::path::path"),
        ));
        assert!(!can_widen_named_paths(
            &path("std::path::path"),
            &path("std::str::str"),
        ));
        assert_eq!(
            join_named_paths(&path("std::str::str"), &path("std::path::path")),
            Some(path("std::path::path"))
        );
    }

    #[test]
    fn widens_graph_registered_full_paths() {
        let order = PrimitiveTypeOrder::from_primitive_types(&[
            PrimitiveTypeGraphNode {
                family: PrimitiveTypeFamily::Int,
                path: path("std::int::int"),
            },
            PrimitiveTypeGraphNode {
                family: PrimitiveTypeFamily::Frac,
                path: path("std::frac::frac"),
            },
            PrimitiveTypeGraphNode {
                family: PrimitiveTypeFamily::Float,
                path: path("std::float::float"),
            },
        ]);

        assert!(order.can_widen_named_paths(&path("std::int::int"), &path("std::float::float")));
        assert!(!order.can_widen_named_paths(&path("int"), &path("std::float::float")));
        assert_eq!(
            order.join_named_paths(&path("std::int::int"), &path("std::float::float")),
            Some(path("std::float::float"))
        );
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

    fn path(path: &str) -> Path {
        Path::new(
            path.split("::")
                .map(|segment| Name(segment.to_string()))
                .collect(),
        )
    }
}
