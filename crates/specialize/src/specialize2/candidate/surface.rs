use super::*;

pub(in crate::specialize2) fn value_candidate_subtype_thunk(
    graph: &TypeGraph<'_>,
    lower: &Type,
    upper: &Type,
) -> bool {
    let Type::Thunk { value, .. } = upper else {
        return false;
    };
    value_candidate_matches_thunk_value(graph, lower, value)
}

pub(in crate::specialize2) fn thunk_value_candidate_subtype(
    graph: &TypeGraph<'_>,
    lower: &Type,
    upper: &Type,
) -> bool {
    let Type::Thunk { value, .. } = lower else {
        return false;
    };
    thunk_value_matches_candidate(graph, value, upper)
}

pub(in crate::specialize2) fn value_candidate_matches_thunk_value(
    graph: &TypeGraph<'_>,
    value: &Type,
    thunk_value: &Type,
) -> bool {
    matches!(value, Type::OpenVar(_))
        || matches!(thunk_value, Type::OpenVar(_))
        || type_candidate_subtype(graph, value, thunk_value)
        || same_candidate_head(value, thunk_value)
        || match thunk_value {
            Type::Thunk { value: nested, .. } => {
                value_candidate_matches_thunk_value(graph, value, nested)
            }
            _ => false,
        }
}

pub(in crate::specialize2) fn thunk_value_matches_candidate(
    graph: &TypeGraph<'_>,
    thunk_value: &Type,
    value: &Type,
) -> bool {
    matches!(value, Type::OpenVar(_))
        || matches!(thunk_value, Type::OpenVar(_))
        || type_candidate_subtype(graph, thunk_value, value)
        || same_candidate_head(thunk_value, value)
        || match thunk_value {
            Type::Thunk { value: nested, .. } => {
                thunk_value_matches_candidate(graph, nested, value)
            }
            _ => false,
        }
}

pub(in crate::specialize2) fn prefer_more_resolved_candidate(left: Type, right: Type) -> Type {
    if open_var_count(&right) < open_var_count(&left) {
        right
    } else {
        left
    }
}

pub(in crate::specialize2) fn open_var_count(ty: &Type) -> usize {
    match ty {
        Type::OpenVar(_) => 1,
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().map(open_var_count).sum()
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            open_var_count(arg)
                + open_var_count(arg_effect)
                + open_var_count(ret_effect)
                + open_var_count(ret)
        }
        Type::Thunk { effect, value } => open_var_count(effect) + open_var_count(value),
        Type::Record(fields) => fields
            .iter()
            .map(|field| open_var_count(&field.value))
            .sum(),
        Type::PolyVariant(variants) => variants
            .iter()
            .flat_map(|variant| &variant.payloads)
            .map(open_var_count)
            .sum(),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            open_var_count(left) + open_var_count(right)
        }
        Type::Stack { inner, .. } => open_var_count(inner),
        Type::Any | Type::Never => 0,
    }
}

pub(in crate::specialize2) fn stack_weight_cannot_affect_type(
    graph: &TypeGraph<'_>,
    ty: &Type,
) -> bool {
    match ty {
        Type::Never => true,
        Type::Con { path, args } => args.is_empty() && !graph.is_effect_family_path(path),
        Type::Tuple(args) => args.is_empty(),
        Type::Record(fields) => fields.is_empty(),
        Type::PolyVariant(variants) => variants.iter().all(|variant| variant.payloads.is_empty()),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            stack_weight_cannot_affect_type(graph, left)
                && stack_weight_cannot_affect_type(graph, right)
        }
        Type::Any
        | Type::OpenVar(_)
        | Type::EffectRow(_)
        | Type::Fun { .. }
        | Type::Thunk { .. }
        | Type::Stack { .. } => false,
    }
}

pub(in crate::specialize2) fn type_contains_stack(ty: &Type) -> bool {
    match ty {
        Type::Stack { .. } => true,
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(type_contains_stack)
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_contains_stack(arg)
                || type_contains_stack(arg_effect)
                || type_contains_stack(ret_effect)
                || type_contains_stack(ret)
        }
        Type::Thunk { effect, value } => type_contains_stack(effect) || type_contains_stack(value),
        Type::Record(fields) => fields.iter().any(|field| type_contains_stack(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_contains_stack)),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_contains_stack(left) || type_contains_stack(right)
        }
        Type::Any | Type::Never | Type::OpenVar(_) => false,
    }
}

pub(in crate::specialize2) fn candidate_has_unresolved_stack(
    graph: &TypeGraph<'_>,
    slot_kind: TypeSlotKind,
    candidate: &Type,
) -> bool {
    if !type_contains_stack(candidate) {
        return false;
    }
    if slot_kind == TypeSlotKind::Effect && effect_candidate_stack_is_tail(graph, candidate) {
        return false;
    }
    true
}

pub(in crate::specialize2) fn effect_candidate_stack_is_tail(
    graph: &TypeGraph<'_>,
    candidate: &Type,
) -> bool {
    let Type::EffectRow(items) = candidate else {
        return false;
    };
    let (items, has_tail) = split_effect_candidate_tail(graph, items);
    has_tail && items.iter().all(|item| !type_contains_stack(item))
}

pub(in crate::specialize2) fn type_contains_open_var(ty: &Type) -> bool {
    match ty {
        Type::OpenVar(_) => true,
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(type_contains_open_var)
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_contains_open_var(arg)
                || type_contains_open_var(arg_effect)
                || type_contains_open_var(ret_effect)
                || type_contains_open_var(ret)
        }
        Type::Thunk { effect, value } => {
            type_contains_open_var(effect) || type_contains_open_var(value)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_contains_open_var(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_contains_open_var)),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_contains_open_var(left) || type_contains_open_var(right)
        }
        Type::Stack { inner, .. } => type_contains_open_var(inner),
        Type::Any | Type::Never => false,
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub(in crate::specialize2) struct OpenVarUse {
    positive: bool,
    negative: bool,
    effect: bool,
}

#[derive(Debug, Clone, Copy)]
pub(in crate::specialize2) enum TypePolarity {
    Positive,
    Negative,
}

impl TypePolarity {
    pub(in crate::specialize2) fn flip(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

pub(in crate::specialize2) fn erase_negative_only_open_vars(ty: Type) -> Type {
    let mut uses = HashMap::new();
    collect_open_var_uses(&ty, TypePolarity::Positive, TypeSlotKind::Value, &mut uses);
    substitute_negative_only_open_vars(ty, &uses, TypeSlotKind::Value)
}

pub(in crate::specialize2) fn collect_open_var_uses(
    ty: &Type,
    polarity: TypePolarity,
    context: TypeSlotKind,
    uses: &mut HashMap<u32, OpenVarUse>,
) {
    match ty {
        Type::OpenVar(slot) => {
            let use_ = uses.entry(*slot).or_default();
            match polarity {
                TypePolarity::Positive => use_.positive = true,
                TypePolarity::Negative => use_.negative = true,
            }
            if context == TypeSlotKind::Effect {
                use_.effect = true;
            }
        }
        Type::Con { args, .. } | Type::Tuple(args) => {
            for arg in args {
                collect_open_var_uses(arg, TypePolarity::Positive, TypeSlotKind::Value, uses);
                collect_open_var_uses(arg, TypePolarity::Negative, TypeSlotKind::Value, uses);
            }
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            let negative = polarity.flip();
            collect_open_var_uses(arg, negative, TypeSlotKind::Value, uses);
            collect_open_var_uses(arg_effect, negative, TypeSlotKind::Effect, uses);
            collect_open_var_uses(ret_effect, polarity, TypeSlotKind::Effect, uses);
            collect_open_var_uses(ret, polarity, TypeSlotKind::Value, uses);
        }
        Type::Thunk { effect, value } => {
            collect_open_var_uses(effect, polarity, TypeSlotKind::Effect, uses);
            collect_open_var_uses(value, polarity, TypeSlotKind::Value, uses);
        }
        Type::Record(fields) => {
            for field in fields {
                collect_open_var_uses(&field.value, polarity, TypeSlotKind::Value, uses);
            }
        }
        Type::PolyVariant(variants) => {
            for variant in variants {
                for payload in &variant.payloads {
                    collect_open_var_uses(payload, polarity, TypeSlotKind::Value, uses);
                }
            }
        }
        Type::EffectRow(items) => {
            for item in items {
                collect_open_var_uses(item, polarity, TypeSlotKind::Effect, uses);
            }
        }
        Type::Stack { inner, .. } => {
            collect_open_var_uses(inner, polarity, context, uses);
        }
        Type::Union(left, right) | Type::Intersection(left, right) => {
            collect_open_var_uses(left, polarity, context, uses);
            collect_open_var_uses(right, polarity, context, uses);
        }
        Type::Any | Type::Never => {}
    }
}

pub(in crate::specialize2) fn substitute_negative_only_open_vars(
    ty: Type,
    uses: &HashMap<u32, OpenVarUse>,
    context: TypeSlotKind,
) -> Type {
    match ty {
        Type::OpenVar(slot) => {
            if uses
                .get(&slot)
                .is_some_and(|use_| use_.negative && !use_.positive)
            {
                if context == TypeSlotKind::Effect {
                    Type::pure_effect()
                } else {
                    Type::unit()
                }
            } else {
                Type::OpenVar(slot)
            }
        }
        Type::Con { path, args } => Type::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| substitute_negative_only_open_vars(arg, uses, TypeSlotKind::Value))
                .collect(),
        },
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(substitute_negative_only_open_vars(
                *arg,
                uses,
                TypeSlotKind::Value,
            )),
            arg_effect: Box::new(substitute_negative_only_open_vars(
                *arg_effect,
                uses,
                TypeSlotKind::Effect,
            )),
            ret_effect: Box::new(substitute_negative_only_open_vars(
                *ret_effect,
                uses,
                TypeSlotKind::Effect,
            )),
            ret: Box::new(substitute_negative_only_open_vars(
                *ret,
                uses,
                TypeSlotKind::Value,
            )),
        },
        Type::Thunk { effect, value } => types::runtime_shape(
            substitute_negative_only_open_vars(*effect, uses, TypeSlotKind::Effect),
            substitute_negative_only_open_vars(*value, uses, TypeSlotKind::Value),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    value: substitute_negative_only_open_vars(
                        field.value,
                        uses,
                        TypeSlotKind::Value,
                    ),
                    optional: field.optional,
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
                        .map(|payload| {
                            substitute_negative_only_open_vars(payload, uses, TypeSlotKind::Value)
                        })
                        .collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(|item| substitute_negative_only_open_vars(item, uses, TypeSlotKind::Value))
                .collect(),
        ),
        Type::EffectRow(items) => types::simplify_type(Type::EffectRow(
            items
                .into_iter()
                .map(|item| substitute_negative_only_open_vars(item, uses, TypeSlotKind::Effect))
                .collect(),
        )),
        Type::Stack { inner, weight } => types::simplify_stack_type(
            substitute_negative_only_open_vars(*inner, uses, context),
            weight,
        ),
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(substitute_negative_only_open_vars(*left, uses, context)),
            Box::new(substitute_negative_only_open_vars(*right, uses, context)),
        )),
        Type::Intersection(left, right) => types::simplify_type(Type::Intersection(
            Box::new(substitute_negative_only_open_vars(*left, uses, context)),
            Box::new(substitute_negative_only_open_vars(*right, uses, context)),
        )),
        Type::Any | Type::Never => ty,
    }
}

pub(in crate::specialize2) fn close_resolved_runtime_surface(
    ty: Type,
    context: TypeSlotKind,
) -> Type {
    close_runtime_type_surface(erase_negative_only_open_vars(ty), context)
}

pub(in crate::specialize2) fn close_resolved_inference_surface(
    ty: Type,
    context: TypeSlotKind,
) -> Type {
    close_inference_type_surface(erase_negative_only_open_vars(ty), context)
}

pub(in crate::specialize2) fn close_inference_type_surface(
    ty: Type,
    context: TypeSlotKind,
) -> Type {
    match ty {
        Type::OpenVar(_) => match context {
            TypeSlotKind::Value => Type::unit(),
            TypeSlotKind::Effect => Type::pure_effect(),
        },
        Type::Con { path, args } => Type::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| close_inference_type_surface(arg, TypeSlotKind::Value))
                .collect(),
        },
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(close_inference_type_surface(*arg, TypeSlotKind::Value)),
            arg_effect: Box::new(close_inference_type_surface(
                *arg_effect,
                TypeSlotKind::Effect,
            )),
            ret_effect: Box::new(close_inference_type_surface(
                *ret_effect,
                TypeSlotKind::Effect,
            )),
            ret: Box::new(close_inference_type_surface(*ret, TypeSlotKind::Value)),
        },
        Type::Thunk { effect, value } => types::runtime_shape(
            close_inference_type_surface(*effect, TypeSlotKind::Effect),
            close_inference_type_surface(*value, TypeSlotKind::Value),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    value: close_inference_type_surface(field.value, TypeSlotKind::Value),
                    optional: field.optional,
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
                        .map(|payload| close_inference_type_surface(payload, TypeSlotKind::Value))
                        .collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(|item| close_inference_type_surface(item, TypeSlotKind::Value))
                .collect(),
        ),
        Type::EffectRow(items) => types::simplify_type(Type::EffectRow(
            items
                .into_iter()
                .map(|item| close_inference_type_surface(item, TypeSlotKind::Effect))
                .collect(),
        )),
        Type::Stack { inner, weight } => {
            types::simplify_stack_type(close_inference_type_surface(*inner, context), weight)
        }
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(close_inference_type_surface(*left, context)),
            Box::new(close_inference_type_surface(*right, context)),
        )),
        Type::Intersection(left, right) => types::simplify_type(Type::Intersection(
            Box::new(close_inference_type_surface(*left, context)),
            Box::new(close_inference_type_surface(*right, context)),
        )),
        Type::Any | Type::Never => ty,
    }
}

pub(in crate::specialize2) fn close_runtime_type_surface(ty: Type, context: TypeSlotKind) -> Type {
    match ty {
        Type::OpenVar(_) => match context {
            TypeSlotKind::Value => Type::unit(),
            TypeSlotKind::Effect => Type::pure_effect(),
        },
        Type::Con { path, args } => Type::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| close_runtime_type_surface(arg, TypeSlotKind::Value))
                .collect(),
        },
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            let arg = close_runtime_type_surface(*arg, TypeSlotKind::Value);
            let arg_effect = close_runtime_type_surface(*arg_effect, TypeSlotKind::Effect);
            let ret_effect = close_runtime_type_surface(*ret_effect, TypeSlotKind::Effect);
            let ret = close_runtime_type_surface(*ret, TypeSlotKind::Value);
            Type::Fun {
                arg: Box::new(types::runtime_shape(arg_effect, arg)),
                arg_effect: Box::new(Type::pure_effect()),
                ret_effect: Box::new(Type::pure_effect()),
                ret: Box::new(types::runtime_shape(ret_effect, ret)),
            }
        }
        Type::Thunk { effect, value } => types::runtime_shape(
            close_runtime_type_surface(*effect, TypeSlotKind::Effect),
            close_runtime_type_surface(*value, TypeSlotKind::Value),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    value: close_runtime_type_surface(field.value, TypeSlotKind::Value),
                    optional: field.optional,
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
                        .map(|payload| close_runtime_type_surface(payload, TypeSlotKind::Value))
                        .collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(|item| close_runtime_type_surface(item, TypeSlotKind::Value))
                .collect(),
        ),
        Type::EffectRow(items) => types::simplify_type(Type::EffectRow(
            items
                .into_iter()
                .map(|item| close_runtime_type_surface(item, TypeSlotKind::Effect))
                .collect(),
        )),
        Type::Stack { inner, weight } => {
            types::simplify_stack_type(close_runtime_type_surface(*inner, context), weight)
        }
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(close_runtime_type_surface(*left, context)),
            Box::new(close_runtime_type_surface(*right, context)),
        )),
        Type::Intersection(left, right) => types::simplify_type(Type::Intersection(
            Box::new(close_runtime_type_surface(*left, context)),
            Box::new(close_runtime_type_surface(*right, context)),
        )),
        Type::Any | Type::Never => ty,
    }
}

pub(in crate::specialize2) fn direct_cast_rule<'a>(
    arena: &'a poly_expr::Arena,
    actual: &Type,
    expected: &Type,
) -> Option<&'a poly_expr::CastRule> {
    let (
        Type::Con {
            path: source_path, ..
        },
        Type::Con {
            path: target_path, ..
        },
    ) = (actual, expected)
    else {
        return None;
    };
    if source_path == target_path {
        return None;
    }
    #[cfg(test)]
    observe_ordinary_cast_resolution(
        arena,
        OrdinaryCastShadowSeam::EmissionSelection,
        source_path,
        target_path,
    );
    arena.cast_rules.iter().find(|rule| {
        rule.kind == poly_expr::CastRuleKind::Value
            && rule.source == *source_path
            && rule.target == *target_path
    })
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::specialize2) enum OrdinaryCastShadowSeam {
    TypeGraphConstraint,
    EmissionSelection,
    BooleanSubtypeEvidence,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::specialize2) enum OrdinaryCastShadowOutcome {
    Missing,
    Unique,
    Ambiguous,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::specialize2) struct OrdinaryCastShadowWitness {
    pub(in crate::specialize2) seam: OrdinaryCastShadowSeam,
    pub(in crate::specialize2) source: Vec<String>,
    pub(in crate::specialize2) target: Vec<String>,
    pub(in crate::specialize2) outcome: OrdinaryCastShadowOutcome,
    pub(in crate::specialize2) candidate_defs: Vec<poly_expr::DefId>,
}

#[cfg(test)]
thread_local! {
    static ORDINARY_CAST_SHADOW_WITNESSES:
        std::cell::RefCell<Option<Vec<OrdinaryCastShadowWitness>>> = const {
            std::cell::RefCell::new(None)
        };
}

#[cfg(test)]
pub(in crate::specialize2) fn begin_ordinary_cast_shadow_capture() {
    ORDINARY_CAST_SHADOW_WITNESSES.with(|witnesses| {
        *witnesses.borrow_mut() = Some(Vec::new());
    });
}

#[cfg(test)]
pub(in crate::specialize2) fn finish_ordinary_cast_shadow_capture() -> Vec<OrdinaryCastShadowWitness>
{
    ORDINARY_CAST_SHADOW_WITNESSES
        .with(|witnesses| witnesses.borrow_mut().take().unwrap_or_default())
}

#[cfg(test)]
pub(in crate::specialize2) fn observe_ordinary_cast_resolution(
    arena: &poly_expr::Arena,
    seam: OrdinaryCastShadowSeam,
    source: &[String],
    target: &[String],
) {
    let capture_enabled =
        ORDINARY_CAST_SHADOW_WITNESSES.with(|witnesses| witnesses.borrow().is_some());
    if !capture_enabled {
        return;
    }

    let resolution = arena.resolve_value_cast(source, target);
    let (outcome, candidate_defs) = match resolution {
        poly::cast_resolution::OrdinaryCastResolution::Missing => {
            (OrdinaryCastShadowOutcome::Missing, Vec::new())
        }
        poly::cast_resolution::OrdinaryCastResolution::Unique(rule) => {
            (OrdinaryCastShadowOutcome::Unique, vec![rule.def])
        }
        poly::cast_resolution::OrdinaryCastResolution::Ambiguous(rules) => (
            OrdinaryCastShadowOutcome::Ambiguous,
            rules.into_iter().map(|rule| rule.def).collect(),
        ),
    };
    let witness = OrdinaryCastShadowWitness {
        seam,
        source: source.to_vec(),
        target: target.to_vec(),
        outcome,
        candidate_defs,
    };
    ORDINARY_CAST_SHADOW_WITNESSES.with(|witnesses| {
        if let Some(witnesses) = witnesses.borrow_mut().as_mut() {
            witnesses.push(witness);
        }
    });
}
