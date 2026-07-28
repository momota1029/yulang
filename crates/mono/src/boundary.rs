use crate::{Type, TypeField};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueBoundaryKind {
    Trivial,
    FunctionAdapter,
    Thunk(ThunkBoundaryKind),
    TupleElements,
    RecordFields,
    Unsupported,
}

impl ValueBoundaryKind {
    pub fn classify(source: &Type, target: &Type) -> Self {
        if equivalent_value_boundary_types(source, target)
            || matches!(target, Type::Any)
            || matches!(source, Type::Never)
        {
            return Self::Trivial;
        }
        match (source, target) {
            (Type::Fun { .. }, Type::Fun { .. }) => {
                if function_boundary_supported(source, target) {
                    Self::FunctionAdapter
                } else {
                    Self::Unsupported
                }
            }
            (Type::Thunk { value: source, .. }, Type::Thunk { value: target, .. }) => {
                if Self::classify(source, target).is_supported() {
                    Self::Thunk(ThunkBoundaryKind::ForceThenMake)
                } else {
                    Self::Unsupported
                }
            }
            (Type::Thunk { value: source, .. }, target) => {
                if Self::classify(source, target).is_supported() {
                    Self::Thunk(ThunkBoundaryKind::Force)
                } else {
                    Self::Unsupported
                }
            }
            (source, Type::Thunk { value: target, .. }) => {
                if Self::classify(source, target).is_supported() {
                    Self::Thunk(ThunkBoundaryKind::Make)
                } else {
                    Self::Unsupported
                }
            }
            (Type::Tuple(source_items), Type::Tuple(target_items))
                if source_items.len() == target_items.len()
                    && source_items
                        .iter()
                        .zip(target_items)
                        .all(|(source, target)| Self::classify(source, target).is_supported()) =>
            {
                Self::TupleElements
            }
            (Type::Record(source_fields), Type::Record(target_fields))
                if record_boundary_supported(source_fields, target_fields) =>
            {
                Self::RecordFields
            }
            _ => Self::Unsupported,
        }
    }

    pub const fn is_supported(self) -> bool {
        !matches!(self, Self::Unsupported)
    }

    pub const fn supports_generic_coerce(self) -> bool {
        matches!(
            self,
            Self::Trivial | Self::TupleElements | Self::RecordFields
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ThunkBoundaryKind {
    Make,
    Force,
    ForceThenMake,
}

pub fn equivalent_value_boundary_types(source: &Type, target: &Type) -> bool {
    if source == target || source.is_pure_effect() && target.is_pure_effect() {
        return true;
    }
    match (source, target) {
        (Type::EffectRow(items), target) if items.len() == 1 => {
            equivalent_value_boundary_types(&items[0], target)
        }
        (source, Type::EffectRow(items)) if items.len() == 1 => {
            equivalent_value_boundary_types(source, &items[0])
        }
        (source, Type::Thunk { effect, value }) if effect.is_pure_effect() => {
            equivalent_value_boundary_types(source, value)
        }
        (Type::Thunk { effect, value }, target) if effect.is_pure_effect() => {
            equivalent_value_boundary_types(value, target)
        }
        (
            Type::Con {
                path: source_path,
                args: source_args,
            },
            Type::Con {
                path: target_path,
                args: target_args,
            },
        ) => {
            source_path == target_path
                && source_args.len() == target_args.len()
                && source_args
                    .iter()
                    .zip(target_args)
                    .all(|(source, target)| equivalent_value_boundary_types(source, target))
        }
        (
            Type::Fun {
                arg: source_arg,
                arg_effect: source_arg_effect,
                ret_effect: source_ret_effect,
                ret: source_ret,
            },
            Type::Fun {
                arg: target_arg,
                arg_effect: target_arg_effect,
                ret_effect: target_ret_effect,
                ret: target_ret,
            },
        ) => {
            equivalent_value_boundary_types(source_arg, target_arg)
                && equivalent_effect_boundary_types(source_arg_effect, target_arg_effect)
                && equivalent_effect_boundary_types(source_ret_effect, target_ret_effect)
                && equivalent_value_boundary_types(source_ret, target_ret)
        }
        (Type::Tuple(source_items), Type::Tuple(target_items)) => {
            source_items.len() == target_items.len()
                && source_items
                    .iter()
                    .zip(target_items)
                    .all(|(source, target)| equivalent_value_boundary_types(source, target))
        }
        (Type::Record(source_fields), Type::Record(target_fields)) => {
            target_fields.iter().all(|target| {
                record_field_type(source_fields, &target.name).map_or(target.optional, |source| {
                    (target.optional || !source.optional)
                        && equivalent_value_boundary_types(&source.value, &target.value)
                })
            })
        }
        (Type::PolyVariant(source_variants), Type::PolyVariant(target_variants)) => {
            source_variants.iter().all(|source| {
                target_variants
                    .iter()
                    .find(|target| {
                        target.name == source.name && target.payloads.len() == source.payloads.len()
                    })
                    .is_some_and(|target| {
                        source
                            .payloads
                            .iter()
                            .zip(&target.payloads)
                            .all(|(source, target)| equivalent_value_boundary_types(source, target))
                    })
            })
        }
        (source, Type::Union(left, right)) => {
            equivalent_value_boundary_types(source, left)
                || equivalent_value_boundary_types(source, right)
        }
        (Type::Union(left, right), target) => {
            equivalent_value_boundary_types(left, target)
                && equivalent_value_boundary_types(right, target)
        }
        (source, Type::Intersection(left, right)) => {
            equivalent_value_boundary_types(source, left)
                && equivalent_value_boundary_types(source, right)
        }
        (Type::Intersection(left, right), target) => {
            equivalent_value_boundary_types(left, target)
                || equivalent_value_boundary_types(right, target)
        }
        (Type::EffectRow(source_items), Type::EffectRow(target_items)) => {
            equivalent_effect_rows(source_items, target_items)
        }
        (
            Type::Thunk {
                effect: source_effect,
                value: source_value,
            },
            Type::Thunk {
                effect: target_effect,
                value: target_value,
            },
        ) => {
            equivalent_effect_boundary_types(source_effect, target_effect)
                && equivalent_value_boundary_types(source_value, target_value)
        }
        _ => false,
    }
}

fn function_boundary_supported(source: &Type, target: &Type) -> bool {
    let (
        Type::Fun {
            arg: source_arg,
            ret: source_ret,
            ..
        },
        Type::Fun {
            arg: target_arg,
            ret: target_ret,
            ..
        },
    ) = (source, target)
    else {
        return false;
    };
    ValueBoundaryKind::classify(target_arg, source_arg).is_supported()
        && ValueBoundaryKind::classify(source_ret, target_ret).is_supported()
}

fn record_boundary_supported(source_fields: &[TypeField], target_fields: &[TypeField]) -> bool {
    target_fields.iter().all(|target| {
        record_field_type(source_fields, &target.name).map_or(target.optional, |source| {
            (target.optional || !source.optional)
                && ValueBoundaryKind::classify(&source.value, &target.value).is_supported()
        })
    })
}

fn equivalent_effect_rows(source_items: &[Type], target_items: &[Type]) -> bool {
    if source_items.len() != target_items.len() {
        return false;
    }
    let mut used = vec![false; target_items.len()];
    source_items.iter().all(|source| {
        let Some(index) = target_items.iter().enumerate().find_map(|(index, target)| {
            (!used[index] && equivalent_effect_item(source, target)).then_some(index)
        }) else {
            return false;
        };
        used[index] = true;
        true
    })
}

fn equivalent_effect_item(source: &Type, target: &Type) -> bool {
    match (source, target) {
        (
            Type::Con {
                path: source_path,
                args: source_args,
            },
            Type::Con {
                path: target_path,
                args: target_args,
            },
        ) if source_path == target_path && source_args.len() == target_args.len() => source_args
            .iter()
            .zip(target_args)
            .all(|(source, target)| equivalent_value_boundary_types(source, target)),
        _ => equivalent_value_boundary_types(source, target),
    }
}

fn equivalent_effect_boundary_types(source: &Type, target: &Type) -> bool {
    if equivalent_value_boundary_types(source, target) {
        return true;
    }
    match (source, target) {
        (Type::EffectRow(items), target) if items.len() == 1 => {
            equivalent_value_boundary_types(&items[0], target)
        }
        (source, Type::EffectRow(items)) if items.len() == 1 => {
            equivalent_value_boundary_types(source, &items[0])
        }
        _ => false,
    }
}

fn record_field_type<'a>(fields: &'a [TypeField], name: &str) -> Option<&'a TypeField> {
    fields.iter().find(|field| field.name == name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifies_equivalent_top_target_and_bottom_source_as_trivial() {
        let int = con("int");
        assert_eq!(
            ValueBoundaryKind::classify(&int, &int),
            ValueBoundaryKind::Trivial
        );
        assert_eq!(
            ValueBoundaryKind::classify(&int, &Type::Any),
            ValueBoundaryKind::Trivial
        );
        assert_eq!(
            ValueBoundaryKind::classify(&Type::Never, &int),
            ValueBoundaryKind::Trivial
        );
    }

    #[test]
    fn classifies_function_and_thunk_adapters_only_when_their_values_are_supported() {
        let source_function = function(Type::Any, Type::Never);
        let target_function = function(Type::Never, Type::Any);
        assert_eq!(
            ValueBoundaryKind::classify(&source_function, &target_function),
            ValueBoundaryKind::FunctionAdapter
        );

        let effect = Type::EffectRow(vec![con("effect")]);
        let int = con("int");
        let thunk_int = thunk(effect.clone(), int.clone());
        assert_eq!(
            ValueBoundaryKind::classify(&int, &thunk_int),
            ValueBoundaryKind::Thunk(ThunkBoundaryKind::Make)
        );
        assert_eq!(
            ValueBoundaryKind::classify(&thunk_int, &int),
            ValueBoundaryKind::Thunk(ThunkBoundaryKind::Force)
        );
        assert_eq!(
            ValueBoundaryKind::classify(&thunk_int, &thunk(effect, Type::Any)),
            ValueBoundaryKind::Thunk(ThunkBoundaryKind::ForceThenMake)
        );

        assert_eq!(
            ValueBoundaryKind::classify(&function(int.clone(), int.clone()), &int),
            ValueBoundaryKind::Unsupported
        );
    }

    #[test]
    fn classifies_recursive_tuple_and_record_adaptation() {
        let int = con("int");
        assert_eq!(
            ValueBoundaryKind::classify(
                &Type::Tuple(vec![Type::Never]),
                &Type::Tuple(vec![Type::Any]),
            ),
            ValueBoundaryKind::TupleElements
        );
        assert_eq!(
            ValueBoundaryKind::classify(
                &Type::Tuple(vec![int.clone()]),
                &Type::Tuple(vec![function(int.clone(), int.clone())]),
            ),
            ValueBoundaryKind::Unsupported
        );

        let source = Type::Record(vec![
            field("value", Type::Never, false),
            field("extra", int.clone(), false),
        ]);
        let target = Type::Record(vec![
            field("value", Type::Any, false),
            field("label", int.clone(), true),
        ]);
        assert_eq!(
            ValueBoundaryKind::classify(&source, &target),
            ValueBoundaryKind::RecordFields
        );
        assert_eq!(
            ValueBoundaryKind::classify(
                &Type::Record(vec![field("value", int.clone(), true)]),
                &Type::Record(vec![field("value", int.clone(), false)]),
            ),
            ValueBoundaryKind::Unsupported
        );
    }

    #[test]
    fn leaves_cross_shape_and_nominal_record_pairs_unsupported() {
        let int = con("int");
        let function = function(Type::unit(), Type::unit());
        assert_eq!(
            ValueBoundaryKind::classify(&int, &function),
            ValueBoundaryKind::Unsupported
        );
        assert_eq!(
            ValueBoundaryKind::classify(&con("point"), &Type::Record(vec![field("x", int, false)]),),
            ValueBoundaryKind::Unsupported
        );
    }

    fn con(name: &str) -> Type {
        Type::Con {
            path: vec![name.to_string()],
            args: Vec::new(),
        }
    }

    fn function(arg: Type, ret: Type) -> Type {
        Type::Fun {
            arg: Box::new(arg),
            arg_effect: Box::new(Type::pure_effect()),
            ret_effect: Box::new(Type::pure_effect()),
            ret: Box::new(ret),
        }
    }

    fn thunk(effect: Type, value: Type) -> Type {
        Type::Thunk {
            effect: Box::new(effect),
            value: Box::new(value),
        }
    }

    fn field(name: &str, value: Type, optional: bool) -> TypeField {
        TypeField {
            name: name.to_string(),
            value,
            optional,
        }
    }
}
