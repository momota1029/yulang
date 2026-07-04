use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};

use mono::{
    EffectFamilies, EffectFamily, Signature, StackWeightEntry, Type, TypeField, TypeVariant,
};
use poly::expr as poly_expr;
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicateArg, Scheme, StackWeight,
    Subtractability, TypeArena, TypeVar,
};

use crate::{SpecializeError, std_types};

mod collect;
mod match_types;
mod materialize;
mod setup;
mod type_ops;

pub(crate) use type_ops::*;

pub(crate) fn signature_for_scheme(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    expected: Option<&Type>,
) -> Result<Signature, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_open_vars(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    if let Some(expected) = expected {
        materializer.match_pos(scheme.predicate, expected, TypeContext::Value)?;
    }
    materializer.default_unbound_quantifiers();
    Ok(Signature {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
    })
}

pub(crate) fn role_predicates_for_scheme_signature(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    expected: Option<&Type>,
) -> Result<Vec<InstantiatedRolePredicate>, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    if let Some(expected) = expected {
        materializer.match_pos(scheme.predicate, expected, TypeContext::Value)?;
    }
    materializer.default_unbound_quantifiers();
    materializer.materialize_role_predicates(scheme)
}

pub(crate) fn instantiate_scheme_with_fresh_and_roles(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedScheme, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_open_vars(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    for quantifier in &scheme.quantifiers {
        let kind = materializer
            .kind_for(*quantifier)
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    Ok(InstantiatedScheme {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
        role_predicates: materializer.materialize_role_predicates(scheme)?,
        recursive_bounds: materializer.materialize_recursive_bounds(scheme)?,
    })
}

pub(crate) fn instantiate_principal_scheme_for_inference_with_fresh_and_roles(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedScheme, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_all_vars(&arena.typ, def, scheme);
    materializer.use_inference_functions();
    materializer.use_inline_bounds();
    materializer.collect_scheme_kinds(scheme);
    for quantifier in &scheme.quantifiers {
        let kind = materializer
            .kind_for(*quantifier)
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    materializer.substitute_empty_bounds(&mut fresh);
    materializer.substitute_inline_bounds(&mut fresh);
    let mut recursive_bounds = materializer.materialize_inline_bounds()?;
    recursive_bounds.extend(materializer.materialize_recursive_bounds(scheme)?);
    Ok(InstantiatedScheme {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
        role_predicates: materializer.materialize_role_predicates(scheme)?,
        recursive_bounds,
    })
}

pub(crate) fn instantiate_scheme_with_expected_fresh_and_roles(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    expected: &Type,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedScheme, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_all_vars(&arena.typ, def, scheme);
    materializer.use_inline_bounds();
    materializer.collect_scheme_kinds(scheme);
    materializer.match_pos(scheme.predicate, expected, TypeContext::Value)?;
    for quantifier in &scheme.quantifiers {
        if materializer.substitution.contains_key(quantifier) {
            continue;
        }
        let kind = materializer
            .kind_for(*quantifier)
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    materializer.substitute_empty_bounds(&mut fresh);
    materializer.substitute_inline_bounds(&mut fresh);
    let mut recursive_bounds = materializer.materialize_inline_bounds()?;
    recursive_bounds.extend(materializer.materialize_recursive_bounds(scheme)?);
    Ok(InstantiatedScheme {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
        role_predicates: materializer.materialize_role_predicates(scheme)?,
        recursive_bounds,
    })
}

pub(crate) fn instantiate_monomorphic_scheme_with_fresh_and_roles(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedScheme, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_all_vars(&arena.typ, def, scheme);
    materializer.use_inline_bounds();
    materializer.collect_scheme_kinds(scheme);
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    materializer.substitute_empty_bounds(&mut fresh);
    materializer.substitute_inline_bounds(&mut fresh);
    let mut recursive_bounds = materializer.materialize_inline_bounds()?;
    recursive_bounds.extend(materializer.materialize_recursive_bounds(scheme)?);
    Ok(InstantiatedScheme {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
        role_predicates: materializer.materialize_role_predicates(scheme)?,
        recursive_bounds,
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedScheme {
    pub(crate) ty: Type,
    pub(crate) role_predicates: Vec<InstantiatedRolePredicate>,
    pub(crate) recursive_bounds: Vec<InstantiatedRecursiveBound>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedRecursiveBound {
    pub(crate) value: Type,
    pub(crate) lower: Type,
    pub(crate) upper: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedRolePredicate {
    pub(crate) role: Vec<String>,
    pub(crate) inputs: Vec<InstantiatedRoleArg>,
    pub(crate) associated: Vec<InstantiatedRoleAssociatedType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedRoleArg {
    pub(crate) lower: Type,
    pub(crate) upper: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedRoleAssociatedType {
    pub(crate) name: String,
    pub(crate) lower: Type,
    pub(crate) upper: Type,
}

pub(crate) fn pure_function_type(arg: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(arg),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(Type::pure_effect()),
        ret: Box::new(ret),
    }
}

fn runtime_function_type(arg: Type, arg_effect: Type, ret_effect: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(runtime_shape(arg_effect, arg)),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(Type::pure_effect()),
        ret: Box::new(runtime_shape(ret_effect, ret)),
    }
}

fn inference_function_type(arg: Type, arg_effect: Type, ret_effect: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(arg),
        arg_effect: Box::new(arg_effect),
        ret_effect: Box::new(ret_effect),
        ret: Box::new(ret),
    }
}

pub(crate) fn runtime_shape(effect: Type, value: Type) -> Type {
    if effect.is_pure_effect() {
        return value;
    }
    Type::Thunk {
        effect: Box::new(effect),
        value: Box::new(value),
    }
}

fn split_runtime_shape(shape: &Type, legacy_effect: &Type) -> (Type, Type) {
    match shape {
        Type::Thunk { effect, value } => (value.as_ref().clone(), effect.as_ref().clone()),
        _ => (shape.clone(), legacy_effect.clone()),
    }
}

fn reject_unsupported_scheme_features(
    def: poly_expr::DefId,
    scheme: &Scheme,
) -> Result<(), SpecializeError> {
    let _ = def;
    let _ = scheme;
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SchemeQuantifierKind {
    Value,
    Effect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeContext {
    Value,
    Effect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FunctionMaterialization {
    Runtime,
    Inference,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundMaterialization {
    Structural,
    Fresh,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QuantifierKind {
    Value,
    Effect,
}

impl From<QuantifierKind> for SchemeQuantifierKind {
    fn from(kind: QuantifierKind) -> Self {
        match kind {
            QuantifierKind::Value => Self::Value,
            QuantifierKind::Effect => Self::Effect,
        }
    }
}

impl From<QuantifierKind> for TypeContext {
    fn from(kind: QuantifierKind) -> Self {
        match kind {
            QuantifierKind::Value => Self::Value,
            QuantifierKind::Effect => Self::Effect,
        }
    }
}

impl QuantifierKind {
    fn from_context(context: TypeContext) -> Self {
        match context {
            TypeContext::Value => Self::Value,
            TypeContext::Effect => Self::Effect,
        }
    }

    fn default_type(self) -> Type {
        match self {
            Self::Value => Type::unit(),
            Self::Effect => Type::pure_effect(),
        }
    }
}

fn con_arg_context(path: &[String], index: usize) -> TypeContext {
    if std_types::is_ref_effect_arg(path, index) {
        TypeContext::Effect
    } else {
        TypeContext::Value
    }
}

struct SchemeMaterializer<'a> {
    arena: &'a TypeArena,
    def: poly_expr::DefId,
    quantifiers: HashSet<TypeVar>,
    substitution: HashMap<TypeVar, Type>,
    kinds: HashMap<TypeVar, QuantifierKind>,
    default_kinds: HashMap<TypeVar, QuantifierKind>,
    track_unquantified: bool,
    track_empty_bounds: bool,
    empty_bound_kinds: Vec<TypeContext>,
    empty_bound_types: RefCell<VecDeque<Type>>,
    function_materialization: FunctionMaterialization,
    bound_materialization: BoundMaterialization,
    inline_bound_kinds: HashMap<NeuId, QuantifierKind>,
    inline_bound_order: Vec<NeuId>,
    inline_bound_substitution: HashMap<NeuId, Type>,
}

#[cfg(test)]
mod tests {
    use mono::Type;
    use poly::expr as poly_expr;
    use poly::types::{Neg, Neu, Pos, Scheme, TypeArena, TypeVar};

    use super::{
        SchemeQuantifierKind, instantiate_principal_scheme_for_inference_with_fresh_and_roles,
        simplify_type,
    };

    #[test]
    fn nominal_arg_default_value_kind_loses_to_structural_ref_effect_kind() {
        let mut arena = poly_expr::Arena::new();
        let effect_var = TypeVar(0);
        let effect = bounds_var(&mut arena.typ, effect_var);
        let str_ty = con_neu(&mut arena.typ, &["str"]);
        let lines = arena.typ.alloc_pos(Pos::Con(
            path(&["std", "text", "str", "ref_lines"]),
            vec![effect],
        ));
        let source = arena
            .typ
            .alloc_pos(Pos::Con(ref_path(), vec![effect, str_ty]));
        let predicate = arena.typ.alloc_pos(Pos::Tuple(vec![lines, source]));
        let scheme = scheme(predicate, effect_var);

        let instantiated = instantiate_principal_scheme_for_inference_with_fresh_and_roles(
            &arena,
            poly_expr::DefId(0),
            &scheme,
            fresh_for_kind,
        )
        .unwrap();

        assert_eq!(
            instantiated.ty,
            Type::Tuple(vec![
                Type::Con {
                    path: path(&["std", "text", "str", "ref_lines"]),
                    args: vec![Type::OpenVar(200)],
                },
                Type::Con {
                    path: ref_path(),
                    args: vec![Type::OpenVar(200), str_type()],
                },
            ])
        );
    }

    #[test]
    fn nominal_arg_default_kind_stays_value_without_structural_effect_use() {
        let mut arena = poly_expr::Arena::new();
        let value_var = TypeVar(0);
        let value = bounds_var(&mut arena.typ, value_var);
        let predicate = arena.typ.alloc_pos(Pos::Con(
            path(&["std", "text", "str", "ref_lines"]),
            vec![value],
        ));
        let scheme = scheme(predicate, value_var);

        let instantiated = instantiate_principal_scheme_for_inference_with_fresh_and_roles(
            &arena,
            poly_expr::DefId(0),
            &scheme,
            fresh_for_kind,
        )
        .unwrap();

        assert_eq!(
            instantiated.ty,
            Type::Con {
                path: path(&["std", "text", "str", "ref_lines"]),
                args: vec![Type::OpenVar(100)],
            }
        );
    }

    #[test]
    fn effect_row_intersection_deduplicates_repeated_family() {
        let nondet = effect("nondet");
        let ty = simplify_type(Type::Intersection(
            Box::new(Type::EffectRow(vec![nondet.clone()])),
            Box::new(Type::EffectRow(vec![nondet.clone(), nondet.clone()])),
        ));

        assert_eq!(ty, Type::EffectRow(vec![nondet]));
    }

    #[test]
    fn effect_row_flattens_simplified_tail() {
        let nondet = effect("nondet");
        let tail = Type::Intersection(
            Box::new(Type::EffectRow(vec![nondet.clone()])),
            Box::new(Type::EffectRow(vec![nondet.clone(), nondet.clone()])),
        );
        let ty = simplify_type(Type::EffectRow(vec![nondet.clone(), tail]));

        assert_eq!(ty, Type::EffectRow(vec![nondet]));
    }

    #[test]
    fn effect_row_union_deduplicates_repeated_family() {
        let nondet = effect("nondet");
        let ty = simplify_type(Type::Union(
            Box::new(Type::EffectRow(vec![nondet.clone()])),
            Box::new(Type::EffectRow(vec![nondet.clone(), nondet.clone()])),
        ));

        assert_eq!(ty, Type::EffectRow(vec![nondet]));
    }

    #[test]
    fn value_union_keeps_open_var_with_concrete_candidate() {
        let ty = simplify_type(Type::Union(
            Box::new(Type::OpenVar(0)),
            Box::new(int_type()),
        ));

        assert!(matches!(ty, Type::Union(_, _)), "{ty:?}");
    }

    #[test]
    fn value_intersection_keeps_open_var_with_concrete_candidate() {
        let ty = simplify_type(Type::Intersection(
            Box::new(Type::OpenVar(0)),
            Box::new(int_type()),
        ));

        assert!(matches!(ty, Type::Intersection(_, _)), "{ty:?}");
    }

    fn int_type() -> Type {
        Type::Con {
            path: vec!["int".to_string()],
            args: Vec::new(),
        }
    }

    fn effect(name: &str) -> Type {
        Type::Con {
            path: vec![name.to_string()],
            args: Vec::new(),
        }
    }

    fn fresh_for_kind(kind: SchemeQuantifierKind) -> Type {
        match kind {
            SchemeQuantifierKind::Value => Type::OpenVar(100),
            SchemeQuantifierKind::Effect => Type::OpenVar(200),
        }
    }

    fn scheme(predicate: poly::types::PosId, quantifier: TypeVar) -> Scheme {
        Scheme {
            quantifiers: vec![quantifier],
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        }
    }

    fn bounds_var(typ: &mut TypeArena, var: TypeVar) -> poly::types::NeuId {
        let lower = typ.alloc_pos(Pos::Var(var));
        let upper = typ.alloc_neg(Neg::Var(var));
        typ.alloc_neu(Neu::Bounds(lower, upper))
    }

    fn con_neu(typ: &mut TypeArena, names: &[&str]) -> poly::types::NeuId {
        typ.alloc_neu(Neu::Con(path(names), Vec::new()))
    }

    fn str_type() -> Type {
        Type::Con {
            path: path(&["str"]),
            args: Vec::new(),
        }
    }

    fn ref_path() -> Vec<String> {
        path(&["std", "control", "var", "ref"])
    }

    fn path(names: &[&str]) -> Vec<String> {
        names.iter().map(|name| (*name).to_string()).collect()
    }
}
