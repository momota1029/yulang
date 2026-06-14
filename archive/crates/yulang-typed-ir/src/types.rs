use crate::names::{Name, Path};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Scheme {
    pub requirements: Vec<RoleRequirement>,
    pub body: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeSubstitution {
    pub var: TypeVar,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RecordType {
    pub fields: Vec<RecordField<Type>>,
    pub spread: Option<RecordSpread>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VariantType {
    pub cases: Vec<VariantCase>,
    pub tail: Option<Box<Type>>,
}

#[derive(Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    /// Internal evidence hole. This is not the top type.
    ///
    /// `Any` means "all values"; `Unknown` means "the exporter/runtime does not
    /// have a precise type for this slot yet". Runtime specialization must not
    /// use this as a completed substitution.
    Unknown,
    Never,
    Any,
    Var(TypeVar),
    Named {
        path: Path,
        args: Vec<TypeArg>,
    },
    Fun {
        param: Box<Type>,
        param_effect: Box<Type>,
        ret_effect: Box<Type>,
        ret: Box<Type>,
    },
    Tuple(Vec<Type>),
    Record(RecordType),
    Variant(VariantType),
    Row {
        items: Vec<Type>,
        tail: Box<Type>,
    },
    Union(Vec<Type>),
    Inter(Vec<Type>),
    Recursive {
        var: TypeVar,
        body: Box<Type>,
    },
}

impl Clone for Type {
    fn clone(&self) -> Self {
        clone_type_without_spine_recursion(self)
    }
}

enum CloneTypeFrame<'a> {
    Fun {
        param: &'a Type,
        param_effect: &'a Type,
        ret_effect: &'a Type,
    },
    Row {
        items: &'a [Type],
    },
    Recursive {
        var: &'a TypeVar,
    },
}

fn clone_type_without_spine_recursion(ty: &Type) -> Type {
    let mut current = ty;
    let mut frames = Vec::new();
    loop {
        match current {
            Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                frames.push(CloneTypeFrame::Fun {
                    param,
                    param_effect,
                    ret_effect,
                });
                current = ret;
            }
            Type::Row { items, tail } => {
                frames.push(CloneTypeFrame::Row { items });
                current = tail;
            }
            Type::Recursive { var, body } => {
                frames.push(CloneTypeFrame::Recursive { var });
                current = body;
            }
            Type::Unknown => return rebuild_type_spine(Type::Unknown, frames),
            Type::Never => return rebuild_type_spine(Type::Never, frames),
            Type::Any => return rebuild_type_spine(Type::Any, frames),
            Type::Var(var) => return rebuild_type_spine(Type::Var(var.clone()), frames),
            Type::Named { path, args } => {
                return rebuild_type_spine(
                    Type::Named {
                        path: path.clone(),
                        args: clone_type_args(args),
                    },
                    frames,
                );
            }
            Type::Tuple(items) => {
                return rebuild_type_spine(Type::Tuple(clone_types(items)), frames);
            }
            Type::Record(record) => {
                return rebuild_type_spine(Type::Record(clone_record_type(record)), frames);
            }
            Type::Variant(variant) => {
                return rebuild_type_spine(Type::Variant(clone_variant_type(variant)), frames);
            }
            Type::Union(items) => {
                return rebuild_type_spine(Type::Union(clone_types(items)), frames);
            }
            Type::Inter(items) => {
                return rebuild_type_spine(Type::Inter(clone_types(items)), frames);
            }
        }
    }
}

fn rebuild_type_spine(mut cloned: Type, frames: Vec<CloneTypeFrame<'_>>) -> Type {
    for frame in frames.into_iter().rev() {
        cloned = match frame {
            CloneTypeFrame::Fun {
                param,
                param_effect,
                ret_effect,
            } => Type::Fun {
                param: Box::new(clone_type_without_spine_recursion(param)),
                param_effect: Box::new(clone_type_without_spine_recursion(param_effect)),
                ret_effect: Box::new(clone_type_without_spine_recursion(ret_effect)),
                ret: Box::new(cloned),
            },
            CloneTypeFrame::Row { items } => Type::Row {
                items: clone_types(items),
                tail: Box::new(cloned),
            },
            CloneTypeFrame::Recursive { var } => Type::Recursive {
                var: var.clone(),
                body: Box::new(cloned),
            },
        };
    }
    cloned
}

fn clone_types(items: &[Type]) -> Vec<Type> {
    items
        .iter()
        .map(clone_type_without_spine_recursion)
        .collect()
}

fn clone_type_args(args: &[TypeArg]) -> Vec<TypeArg> {
    args.iter().map(clone_type_arg).collect()
}

fn clone_type_arg(arg: &TypeArg) -> TypeArg {
    match arg {
        TypeArg::Type(ty) => TypeArg::Type(clone_type_without_spine_recursion(ty)),
        TypeArg::Bounds(bounds) => TypeArg::Bounds(clone_type_bounds(bounds)),
    }
}

fn clone_type_bounds(bounds: &TypeBounds) -> TypeBounds {
    TypeBounds {
        lower: bounds
            .lower
            .as_ref()
            .map(|ty| Box::new(clone_type_without_spine_recursion(ty))),
        upper: bounds
            .upper
            .as_ref()
            .map(|ty| Box::new(clone_type_without_spine_recursion(ty))),
    }
}

fn clone_record_type(record: &RecordType) -> RecordType {
    RecordType {
        fields: record
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: clone_type_without_spine_recursion(&field.value),
                optional: field.optional,
            })
            .collect(),
        spread: record.spread.as_ref().map(clone_record_spread),
    }
}

fn clone_record_spread(spread: &RecordSpread) -> RecordSpread {
    match spread {
        RecordSpread::Head(ty) => {
            RecordSpread::Head(Box::new(clone_type_without_spine_recursion(ty)))
        }
        RecordSpread::Tail(ty) => {
            RecordSpread::Tail(Box::new(clone_type_without_spine_recursion(ty)))
        }
    }
}

fn clone_variant_type(variant: &VariantType) -> VariantType {
    VariantType {
        cases: variant
            .cases
            .iter()
            .map(|case| VariantCase {
                name: case.name.clone(),
                payloads: clone_types(&case.payloads),
            })
            .collect(),
        tail: variant
            .tail
            .as_ref()
            .map(|tail| Box::new(clone_type_without_spine_recursion(tail))),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TypeVar(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RoleRequirement {
    pub role: Path,
    pub args: Vec<RoleRequirementArg>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RoleRequirementArg {
    Input(TypeBounds),
    Associated { name: Name, bounds: TypeBounds },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TypeArg {
    Type(Type),
    Bounds(TypeBounds),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct TypeBounds {
    pub lower: Option<Box<Type>>,
    pub upper: Option<Box<Type>>,
}

impl TypeBounds {
    pub fn exact(ty: Type) -> Self {
        Self {
            lower: Some(Box::new(ty.clone())),
            upper: Some(Box::new(ty)),
        }
    }

    pub fn lower(ty: Type) -> Self {
        Self {
            lower: Some(Box::new(ty)),
            upper: None,
        }
    }

    pub fn upper(ty: Type) -> Self {
        Self {
            lower: None,
            upper: Some(Box::new(ty)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RecordField<T> {
    pub name: Name,
    pub value: T,
    pub optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RecordSpread {
    Head(Box<Type>),
    Tail(Box<Type>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VariantCase {
    pub name: Name,
    pub payloads: Vec<Type>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clones_deep_function_type_without_recursing() {
        let mut ty = Type::Any;
        for _ in 0..20_000 {
            ty = Type::Fun {
                param: Box::new(Type::Unknown),
                param_effect: Box::new(Type::Never),
                ret_effect: Box::new(Type::Never),
                ret: Box::new(ty),
            };
        }

        let cloned = ty.clone();

        assert!(matches!(cloned, Type::Fun { .. }));
        std::mem::forget(ty);
        std::mem::forget(cloned);
    }

    #[test]
    fn clones_deep_row_type_without_recursing() {
        let mut ty = Type::Never;
        for _ in 0..20_000 {
            ty = Type::Row {
                items: vec![Type::Named {
                    path: Path {
                        segments: vec![Name("effect".to_string())],
                    },
                    args: Vec::new(),
                }],
                tail: Box::new(ty),
            };
        }

        let cloned = ty.clone();

        assert!(matches!(cloned, Type::Row { .. }));
        std::mem::forget(ty);
        std::mem::forget(cloned);
    }

    #[test]
    fn clones_deep_function_type_in_parameter_without_recursing() {
        let mut param = Type::Any;
        for _ in 0..20_000 {
            param = Type::Fun {
                param: Box::new(Type::Unknown),
                param_effect: Box::new(Type::Never),
                ret_effect: Box::new(Type::Never),
                ret: Box::new(param),
            };
        }
        let ty = Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(Type::Never),
            ret_effect: Box::new(Type::Never),
            ret: Box::new(Type::Any),
        };

        let cloned = ty.clone();

        assert!(matches!(cloned, Type::Fun { .. }));
        std::mem::forget(ty);
        std::mem::forget(cloned);
    }

    #[test]
    fn clones_deep_row_type_in_items_without_recursing() {
        let mut item = Type::Never;
        for _ in 0..20_000 {
            item = Type::Row {
                items: vec![Type::Unknown],
                tail: Box::new(item),
            };
        }
        let ty = Type::Row {
            items: vec![item],
            tail: Box::new(Type::Never),
        };

        let cloned = ty.clone();

        assert!(matches!(cloned, Type::Row { .. }));
        std::mem::forget(ty);
        std::mem::forget(cloned);
    }
}
