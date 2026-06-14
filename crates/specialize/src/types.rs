use std::collections::{HashMap, HashSet};

use mono::{
    EffectFamilies, EffectFamily, Signature, StackWeightEntry, Type, TypeField, TypeVariant,
};
use poly::expr as poly_expr;
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicateArg, Scheme, StackWeight,
    Subtractability, TypeArena, TypeVar,
};

use crate::SpecializeError;

pub(crate) fn signature_for_scheme(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    expected: Option<&Type>,
) -> Result<Signature, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new(&arena.typ, def, scheme);
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
    let mut materializer = SchemeMaterializer::new(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    for quantifier in &scheme.quantifiers {
        let kind = materializer
            .kinds
            .get(quantifier)
            .copied()
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    Ok(InstantiatedScheme {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
        role_predicates: materializer.materialize_role_predicates(scheme)?,
        recursive_bounds: materializer.materialize_recursive_bounds(scheme)?,
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

struct SchemeMaterializer<'a> {
    arena: &'a TypeArena,
    def: poly_expr::DefId,
    quantifiers: HashSet<TypeVar>,
    substitution: HashMap<TypeVar, Type>,
    kinds: HashMap<TypeVar, QuantifierKind>,
}

impl<'a> SchemeMaterializer<'a> {
    fn new(arena: &'a TypeArena, def: poly_expr::DefId, scheme: &Scheme) -> Self {
        Self {
            arena,
            def,
            quantifiers: scheme.quantifiers.iter().copied().collect(),
            substitution: HashMap::new(),
            kinds: HashMap::new(),
        }
    }

    fn collect_scheme_kinds(&mut self, scheme: &Scheme) {
        self.collect_pos_kind(scheme.predicate, TypeContext::Value);
        for predicate in &scheme.role_predicates {
            for input in &predicate.inputs {
                match input {
                    RolePredicateArg::Covariant(pos) => {
                        self.collect_pos_kind(*pos, TypeContext::Value);
                    }
                    RolePredicateArg::Contravariant(neg) => {
                        self.collect_neg_kind(*neg, TypeContext::Value);
                    }
                    RolePredicateArg::Invariant(neu) => {
                        self.collect_neu_kind(*neu, TypeContext::Value);
                    }
                }
            }
            for associated in &predicate.associated {
                self.collect_neu_kind(associated.value, TypeContext::Value);
            }
        }
    }

    fn default_unbound_quantifiers(&mut self) {
        for quantifier in &self.quantifiers {
            if self.substitution.contains_key(quantifier) {
                continue;
            }
            let kind = self
                .kinds
                .get(quantifier)
                .copied()
                .unwrap_or(QuantifierKind::Value);
            self.substitution.insert(*quantifier, kind.default_type());
        }
    }

    fn bind_var(&mut self, var: TypeVar, ty: &Type) -> Result<(), SpecializeError> {
        let ty = simplify_type(ty.clone());
        if let Some(existing) = self.substitution.get(&var) {
            if existing == &ty {
                return Ok(());
            }
            if existing.is_pure_effect() && ty.is_pure_effect() {
                return Ok(());
            }
            if self
                .kinds
                .get(&var)
                .is_some_and(|kind| *kind == QuantifierKind::Effect)
            {
                let merged = merge_effect_substitution(existing.clone(), ty);
                self.substitution.insert(var, merged);
                return Ok(());
            }
            return Err(SpecializeError::ConflictingTypeSubstitution {
                def: mono::DefId(self.def.0),
                var: var.0,
                existing: existing.clone(),
                incoming: ty,
            });
        }
        self.substitution.insert(var, ty);
        Ok(())
    }

    fn record_kind(&mut self, var: TypeVar, context: TypeContext) {
        if !self.quantifiers.contains(&var) {
            return;
        }
        let incoming = QuantifierKind::from_context(context);
        self.kinds
            .entry(var)
            .and_modify(|kind| {
                if incoming == QuantifierKind::Value {
                    *kind = QuantifierKind::Value;
                }
            })
            .or_insert(incoming);
    }

    fn match_pos(
        &mut self,
        id: PosId,
        expected: &Type,
        context: TypeContext,
    ) -> Result<(), SpecializeError> {
        match self.arena.pos(id) {
            Pos::Var(var) => self.bind_var(*var, expected),
            Pos::Con(path, args) => {
                let Type::Con {
                    path: expected_path,
                    args: expected_args,
                } = expected
                else {
                    return Ok(());
                };
                if path != expected_path || args.len() != expected_args.len() {
                    return Ok(());
                }
                for (arg, expected) in args.iter().zip(expected_args) {
                    self.match_neu(*arg, expected, TypeContext::Value)?;
                }
                Ok(())
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let Type::Fun {
                    arg: expected_arg,
                    arg_effect: expected_arg_eff,
                    ret_effect: expected_ret_eff,
                    ret: expected_ret,
                } = expected
                else {
                    return Ok(());
                };
                let (expected_arg, expected_arg_eff) =
                    split_runtime_shape(expected_arg, expected_arg_eff);
                let (expected_ret, expected_ret_eff) =
                    split_runtime_shape(expected_ret, expected_ret_eff);
                self.match_neg(*arg, &expected_arg, TypeContext::Value)?;
                self.match_neg(*arg_eff, &expected_arg_eff, TypeContext::Effect)?;
                self.match_pos(*ret_eff, &expected_ret_eff, TypeContext::Effect)?;
                self.match_pos(*ret, &expected_ret, TypeContext::Value)
            }
            Pos::Record(fields) => {
                let Type::Record(expected_fields) = expected else {
                    return Ok(());
                };
                for (field, expected) in fields.iter().zip(expected_fields) {
                    if field.name == expected.name {
                        self.match_pos(field.value, &expected.value, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Pos::RecordTailSpread { fields, .. } | Pos::RecordHeadSpread { fields, .. } => {
                let Type::Record(expected_fields) = expected else {
                    return Ok(());
                };
                for field in fields {
                    if let Some(expected) =
                        expected_fields.iter().find(|item| item.name == field.name)
                    {
                        self.match_pos(field.value, &expected.value, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Pos::PolyVariant(variants) => {
                let Type::PolyVariant(expected_variants) = expected else {
                    return Ok(());
                };
                for (name, payloads) in variants {
                    let Some(expected) = expected_variants.iter().find(|item| item.name == *name)
                    else {
                        continue;
                    };
                    for (payload, expected) in payloads.iter().zip(&expected.payloads) {
                        self.match_pos(*payload, expected, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Pos::Tuple(items) => {
                let Type::Tuple(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_pos(*item, expected, TypeContext::Value)?;
                }
                Ok(())
            }
            Pos::Row(items) => {
                let Type::EffectRow(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_pos(*item, expected, TypeContext::Effect)?;
                }
                Ok(())
            }
            Pos::Stack { .. } => Ok(()),
            Pos::NonSubtract(inner, _) => self.match_pos(*inner, expected, context),
            Pos::Union(left, right) => {
                self.match_pos(*left, expected, context)?;
                self.match_pos(*right, expected, context)
            }
            Pos::Bot => Ok(()),
        }
    }

    fn match_neg(
        &mut self,
        id: NegId,
        expected: &Type,
        context: TypeContext,
    ) -> Result<(), SpecializeError> {
        match self.arena.neg(id) {
            Neg::Var(var) => self.bind_var(*var, expected),
            Neg::Con(path, args) => {
                let Type::Con {
                    path: expected_path,
                    args: expected_args,
                } = expected
                else {
                    return Ok(());
                };
                if path != expected_path || args.len() != expected_args.len() {
                    return Ok(());
                }
                for (arg, expected) in args.iter().zip(expected_args) {
                    self.match_neu(*arg, expected, TypeContext::Value)?;
                }
                Ok(())
            }
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let Type::Fun {
                    arg: expected_arg,
                    arg_effect: expected_arg_eff,
                    ret_effect: expected_ret_eff,
                    ret: expected_ret,
                } = expected
                else {
                    return Ok(());
                };
                let (expected_arg, expected_arg_eff) =
                    split_runtime_shape(expected_arg, expected_arg_eff);
                let (expected_ret, expected_ret_eff) =
                    split_runtime_shape(expected_ret, expected_ret_eff);
                self.match_pos(*arg, &expected_arg, TypeContext::Value)?;
                self.match_pos(*arg_eff, &expected_arg_eff, TypeContext::Effect)?;
                self.match_neg(*ret_eff, &expected_ret_eff, TypeContext::Effect)?;
                self.match_neg(*ret, &expected_ret, TypeContext::Value)
            }
            Neg::Record(fields) => {
                let Type::Record(expected_fields) = expected else {
                    return Ok(());
                };
                for field in fields {
                    if let Some(expected) =
                        expected_fields.iter().find(|item| item.name == field.name)
                    {
                        self.match_neg(field.value, &expected.value, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Neg::PolyVariant(variants) => {
                let Type::PolyVariant(expected_variants) = expected else {
                    return Ok(());
                };
                for (name, payloads) in variants {
                    let Some(expected) = expected_variants.iter().find(|item| item.name == *name)
                    else {
                        continue;
                    };
                    for (payload, expected) in payloads.iter().zip(&expected.payloads) {
                        self.match_neg(*payload, expected, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Neg::Tuple(items) => {
                let Type::Tuple(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_neg(*item, expected, TypeContext::Value)?;
                }
                Ok(())
            }
            Neg::Row(items, tail) => {
                let Type::EffectRow(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_neg(*item, expected, TypeContext::Effect)?;
                }
                if let Some(expected_tail) = expected_items.get(items.len()) {
                    self.match_neg(*tail, expected_tail, TypeContext::Effect)?;
                }
                Ok(())
            }
            Neg::Stack { .. } => Ok(()),
            Neg::Intersection(left, right) => {
                self.match_neg(*left, expected, context)?;
                self.match_neg(*right, expected, context)
            }
            Neg::Top | Neg::Bot => Ok(()),
        }
    }

    fn match_neu(
        &mut self,
        id: NeuId,
        expected: &Type,
        context: TypeContext,
    ) -> Result<(), SpecializeError> {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                self.match_pos(*lower, expected, context)?;
                self.match_neg(*upper, expected, context)
            }
            Neu::Con(path, args) => {
                let Type::Con {
                    path: expected_path,
                    args: expected_args,
                } = expected
                else {
                    return Ok(());
                };
                if path != expected_path || args.len() != expected_args.len() {
                    return Ok(());
                }
                for (arg, expected) in args.iter().zip(expected_args) {
                    self.match_neu(*arg, expected, TypeContext::Value)?;
                }
                Ok(())
            }
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let Type::Fun {
                    arg: expected_arg,
                    arg_effect: expected_arg_eff,
                    ret_effect: expected_ret_eff,
                    ret: expected_ret,
                } = expected
                else {
                    return Ok(());
                };
                let (expected_arg, expected_arg_eff) =
                    split_runtime_shape(expected_arg, expected_arg_eff);
                let (expected_ret, expected_ret_eff) =
                    split_runtime_shape(expected_ret, expected_ret_eff);
                self.match_neu(*arg, &expected_arg, TypeContext::Value)?;
                self.match_neu(*arg_eff, &expected_arg_eff, TypeContext::Effect)?;
                self.match_neu(*ret_eff, &expected_ret_eff, TypeContext::Effect)?;
                self.match_neu(*ret, &expected_ret, TypeContext::Value)
            }
            Neu::Record(fields) => {
                let Type::Record(expected_fields) = expected else {
                    return Ok(());
                };
                for field in fields {
                    if let Some(expected) =
                        expected_fields.iter().find(|item| item.name == field.name)
                    {
                        self.match_neu(field.value, &expected.value, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Neu::PolyVariant(variants) => {
                let Type::PolyVariant(expected_variants) = expected else {
                    return Ok(());
                };
                for (name, payloads) in variants {
                    let Some(expected) = expected_variants.iter().find(|item| item.name == *name)
                    else {
                        continue;
                    };
                    for (payload, expected) in payloads.iter().zip(&expected.payloads) {
                        self.match_neu(*payload, expected, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Neu::Tuple(items) => {
                let Type::Tuple(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_neu(*item, expected, TypeContext::Value)?;
                }
                Ok(())
            }
        }
    }

    fn materialize_pos(&self, id: PosId, context: TypeContext) -> Result<Type, SpecializeError> {
        Ok(match self.arena.pos(id) {
            Pos::Bot => Type::Never,
            Pos::Var(var) => self.materialize_var(*var, context),
            Pos::Con(path, args) => Type::Con {
                path: path.clone(),
                args: self.materialize_neus(args, TypeContext::Value)?,
            },
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => runtime_function_type(
                self.materialize_neg(*arg, TypeContext::Value)?,
                self.materialize_neg(*arg_eff, TypeContext::Effect)?,
                self.materialize_pos(*ret_eff, TypeContext::Effect)?,
                self.materialize_pos(*ret, TypeContext::Value)?,
            ),
            Pos::Record(fields) => Type::Record(self.materialize_fields(
                fields,
                TypeContext::Value,
                Self::materialize_pos,
            )?),
            Pos::RecordTailSpread { fields, tail } => {
                let mut fields =
                    self.materialize_fields(fields, TypeContext::Value, Self::materialize_pos)?;
                if let Type::Record(tail) = self.materialize_pos(*tail, TypeContext::Value)? {
                    fields.extend(tail);
                }
                Type::Record(fields)
            }
            Pos::RecordHeadSpread { tail, fields } => {
                let mut out = match self.materialize_pos(*tail, TypeContext::Value)? {
                    Type::Record(fields) => fields,
                    _ => Vec::new(),
                };
                out.extend(self.materialize_fields(
                    fields,
                    TypeContext::Value,
                    Self::materialize_pos,
                )?);
                Type::Record(out)
            }
            Pos::PolyVariant(variants) => {
                Type::PolyVariant(self.materialize_pos_variants(variants, TypeContext::Value)?)
            }
            Pos::Tuple(items) => Type::Tuple(self.materialize_poss(items, TypeContext::Value)?),
            Pos::Row(items) => Type::EffectRow(self.materialize_poss(items, TypeContext::Effect)?),
            Pos::Stack { inner, weight } => stack_type(
                self.materialize_pos(*inner, context)?,
                self.materialize_stack_weight(weight)?,
            ),
            Pos::NonSubtract(inner, subtract) => stack_type(
                self.materialize_pos(*inner, context)?,
                mono::StackWeight {
                    entries: vec![StackWeightEntry {
                        id: subtract.0,
                        pops: 1,
                        floor: Vec::new(),
                        stack: Vec::new(),
                    }],
                },
            ),
            Pos::Union(left, right) => simplify_union_type(
                self.materialize_pos(*left, context)?,
                self.materialize_pos(*right, context)?,
            ),
        })
    }

    fn materialize_neg(&self, id: NegId, context: TypeContext) -> Result<Type, SpecializeError> {
        Ok(match self.arena.neg(id) {
            Neg::Top => Type::Any,
            Neg::Bot => Type::Never,
            Neg::Var(var) => self.materialize_var(*var, context),
            Neg::Con(path, args) => Type::Con {
                path: path.clone(),
                args: self.materialize_neus(args, TypeContext::Value)?,
            },
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => runtime_function_type(
                self.materialize_pos(*arg, TypeContext::Value)?,
                self.materialize_pos(*arg_eff, TypeContext::Effect)?,
                self.materialize_neg(*ret_eff, TypeContext::Effect)?,
                self.materialize_neg(*ret, TypeContext::Value)?,
            ),
            Neg::Record(fields) => Type::Record(self.materialize_fields(
                fields,
                TypeContext::Value,
                Self::materialize_neg,
            )?),
            Neg::PolyVariant(variants) => {
                Type::PolyVariant(self.materialize_neg_variants(variants, TypeContext::Value)?)
            }
            Neg::Tuple(items) => Type::Tuple(self.materialize_negs(items, TypeContext::Value)?),
            Neg::Row(items, tail) => {
                let mut items = self.materialize_negs(items, TypeContext::Effect)?;
                let tail = self.materialize_neg(*tail, TypeContext::Effect)?;
                match tail {
                    Type::EffectRow(tail_items) => items.extend(tail_items),
                    Type::Any | Type::Never => {}
                    tail if tail.is_pure_effect() => {}
                    tail => items.push(tail),
                }
                Type::EffectRow(items)
            }
            Neg::Stack { inner, weight } => stack_type(
                self.materialize_neg(*inner, context)?,
                self.materialize_stack_weight(weight)?,
            ),
            Neg::Intersection(left, right) => simplify_intersection_type(
                self.materialize_neg(*left, context)?,
                self.materialize_neg(*right, context)?,
            ),
        })
    }

    fn materialize_neu(&self, id: NeuId, context: TypeContext) -> Result<Type, SpecializeError> {
        Ok(match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                let has_lower = !matches!(self.arena.pos(*lower), Pos::Bot);
                let has_upper = !matches!(self.arena.neg(*upper), Neg::Top);
                match (has_lower, has_upper) {
                    (true, true) => simplify_intersection_type(
                        self.materialize_pos(*lower, context)?,
                        self.materialize_neg(*upper, context)?,
                    ),
                    (true, false) => self.materialize_pos(*lower, context)?,
                    (false, true) => self.materialize_neg(*upper, context)?,
                    (false, false) => match context {
                        TypeContext::Value => Type::unit(),
                        TypeContext::Effect => Type::pure_effect(),
                    },
                }
            }
            Neu::Con(path, args) => Type::Con {
                path: path.clone(),
                args: self.materialize_neus(args, TypeContext::Value)?,
            },
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => runtime_function_type(
                self.materialize_neu(*arg, TypeContext::Value)?,
                self.materialize_neu(*arg_eff, TypeContext::Effect)?,
                self.materialize_neu(*ret_eff, TypeContext::Effect)?,
                self.materialize_neu(*ret, TypeContext::Value)?,
            ),
            Neu::Record(fields) => Type::Record(self.materialize_fields(
                fields,
                TypeContext::Value,
                Self::materialize_neu,
            )?),
            Neu::PolyVariant(variants) => {
                Type::PolyVariant(self.materialize_neu_variants(variants, TypeContext::Value)?)
            }
            Neu::Tuple(items) => Type::Tuple(self.materialize_neus(items, TypeContext::Value)?),
        })
    }

    fn materialize_var(&self, var: TypeVar, context: TypeContext) -> Type {
        if let Some(ty) = self.substitution.get(&var) {
            return ty.clone();
        }
        if self.quantifiers.contains(&var) {
            return QuantifierKind::from_context(context).default_type();
        }
        Type::OpenVar(var.0)
    }

    fn materialize_fields<T>(
        &self,
        fields: &[RecordField<T>],
        context: TypeContext,
        materialize: fn(&Self, T, TypeContext) -> Result<Type, SpecializeError>,
    ) -> Result<Vec<TypeField>, SpecializeError>
    where
        T: Copy,
    {
        fields
            .iter()
            .map(|field| {
                Ok(TypeField {
                    name: field.name.clone(),
                    value: materialize(self, field.value, context)?,
                    optional: field.optional,
                })
            })
            .collect()
    }

    fn materialize_pos_variants(
        &self,
        variants: &[(String, Vec<PosId>)],
        context: TypeContext,
    ) -> Result<Vec<TypeVariant>, SpecializeError> {
        variants
            .iter()
            .map(|(name, payloads)| {
                Ok(TypeVariant {
                    name: name.clone(),
                    payloads: self.materialize_poss(payloads, context)?,
                })
            })
            .collect()
    }

    fn materialize_neg_variants(
        &self,
        variants: &[(String, Vec<NegId>)],
        context: TypeContext,
    ) -> Result<Vec<TypeVariant>, SpecializeError> {
        variants
            .iter()
            .map(|(name, payloads)| {
                Ok(TypeVariant {
                    name: name.clone(),
                    payloads: self.materialize_negs(payloads, context)?,
                })
            })
            .collect()
    }

    fn materialize_neu_variants(
        &self,
        variants: &[(String, Vec<NeuId>)],
        context: TypeContext,
    ) -> Result<Vec<TypeVariant>, SpecializeError> {
        variants
            .iter()
            .map(|(name, payloads)| {
                Ok(TypeVariant {
                    name: name.clone(),
                    payloads: self.materialize_neus(payloads, context)?,
                })
            })
            .collect()
    }

    fn materialize_poss(
        &self,
        ids: &[PosId],
        context: TypeContext,
    ) -> Result<Vec<Type>, SpecializeError> {
        ids.iter()
            .map(|id| self.materialize_pos(*id, context))
            .collect()
    }

    fn materialize_negs(
        &self,
        ids: &[NegId],
        context: TypeContext,
    ) -> Result<Vec<Type>, SpecializeError> {
        ids.iter()
            .map(|id| self.materialize_neg(*id, context))
            .collect()
    }

    fn materialize_neus(
        &self,
        ids: &[NeuId],
        context: TypeContext,
    ) -> Result<Vec<Type>, SpecializeError> {
        ids.iter()
            .map(|id| self.materialize_neu(*id, context))
            .collect()
    }

    fn materialize_stack_weight(
        &self,
        weight: &StackWeight,
    ) -> Result<mono::StackWeight, SpecializeError> {
        Ok(mono::StackWeight {
            entries: weight
                .entries()
                .iter()
                .map(|entry| {
                    Ok(StackWeightEntry {
                        id: entry.id.0,
                        pops: entry.pops,
                        floor: self.materialize_subtractabilities(&entry.floor)?,
                        stack: self.materialize_subtractabilities(&entry.stack)?,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    fn materialize_subtractabilities(
        &self,
        items: &[Subtractability],
    ) -> Result<Vec<EffectFamilies>, SpecializeError> {
        items
            .iter()
            .map(|item| self.materialize_subtractability(item))
            .collect()
    }

    fn materialize_subtractability(
        &self,
        item: &Subtractability,
    ) -> Result<EffectFamilies, SpecializeError> {
        Ok(match item {
            Subtractability::Empty => EffectFamilies::Empty,
            Subtractability::All => EffectFamilies::All,
            Subtractability::AllExcept(path, args) => {
                EffectFamilies::AllExcept(vec![self.materialize_effect_family(path, args)?])
            }
            Subtractability::AllExceptMany(families) => EffectFamilies::AllExcept(
                families
                    .iter()
                    .map(|(path, args)| self.materialize_effect_family(path, args))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Subtractability::Set(path, args) => {
                EffectFamilies::Set(vec![self.materialize_effect_family(path, args)?])
            }
            Subtractability::SetMany(families) => EffectFamilies::Set(
                families
                    .iter()
                    .map(|(path, args)| self.materialize_effect_family(path, args))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        })
    }

    fn materialize_effect_family(
        &self,
        path: &[String],
        args: &[NeuId],
    ) -> Result<EffectFamily, SpecializeError> {
        Ok(EffectFamily {
            path: path.to_vec(),
            args: self.materialize_neus(args, TypeContext::Value)?,
        })
    }

    fn materialize_role_predicates(
        &self,
        scheme: &Scheme,
    ) -> Result<Vec<InstantiatedRolePredicate>, SpecializeError> {
        scheme
            .role_predicates
            .iter()
            .map(|predicate| {
                Ok(InstantiatedRolePredicate {
                    role: predicate.role.clone(),
                    inputs: predicate
                        .inputs
                        .iter()
                        .map(|arg| self.materialize_role_arg(*arg))
                        .collect::<Result<Vec<_>, _>>()?,
                    associated: predicate
                        .associated
                        .iter()
                        .map(|associated| {
                            let arg = self.materialize_role_neu_arg(associated.value)?;
                            Ok(InstantiatedRoleAssociatedType {
                                name: associated.name.clone(),
                                lower: arg.lower,
                                upper: arg.upper,
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                })
            })
            .collect()
    }

    fn materialize_recursive_bounds(
        &self,
        scheme: &Scheme,
    ) -> Result<Vec<InstantiatedRecursiveBound>, SpecializeError> {
        scheme
            .recursive_bounds
            .iter()
            .map(|bound| {
                let value = self.materialize_type_var(bound.var);
                let bounds = self.materialize_role_neu_arg(bound.bounds)?;
                Ok(InstantiatedRecursiveBound {
                    value,
                    lower: bounds.lower,
                    upper: bounds.upper,
                })
            })
            .collect()
    }

    fn materialize_role_arg(
        &self,
        arg: RolePredicateArg,
    ) -> Result<InstantiatedRoleArg, SpecializeError> {
        match arg {
            RolePredicateArg::Covariant(lower) => Ok(InstantiatedRoleArg {
                lower: self.materialize_pos(lower, TypeContext::Value)?,
                upper: Type::Any,
            }),
            RolePredicateArg::Contravariant(upper) => Ok(InstantiatedRoleArg {
                lower: Type::Never,
                upper: self.materialize_neg(upper, TypeContext::Value)?,
            }),
            RolePredicateArg::Invariant(value) => self.materialize_role_neu_arg(value),
        }
    }

    fn materialize_role_neu_arg(&self, id: NeuId) -> Result<InstantiatedRoleArg, SpecializeError> {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => Ok(InstantiatedRoleArg {
                lower: self.materialize_pos(*lower, TypeContext::Value)?,
                upper: self.materialize_neg(*upper, TypeContext::Value)?,
            }),
            _ => {
                let ty = self.materialize_neu(id, TypeContext::Value)?;
                Ok(InstantiatedRoleArg {
                    lower: ty.clone(),
                    upper: ty,
                })
            }
        }
    }

    fn materialize_type_var(&self, var: TypeVar) -> Type {
        self.substitution.get(&var).cloned().unwrap_or_else(|| {
            self.kinds
                .get(&var)
                .copied()
                .unwrap_or(QuantifierKind::Value)
                .default_type()
        })
    }

    fn collect_pos_kind(&mut self, id: PosId, context: TypeContext) {
        match self.arena.pos(id) {
            Pos::Var(var) => self.record_kind(*var, context),
            Pos::Con(_, args) => self.collect_neu_kinds(args, TypeContext::Value),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_neg_kind(*arg, TypeContext::Value);
                self.collect_neg_kind(*arg_eff, TypeContext::Effect);
                self.collect_pos_kind(*ret_eff, TypeContext::Effect);
                self.collect_pos_kind(*ret, TypeContext::Value);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.collect_pos_kind(field.value, TypeContext::Value);
                }
            }
            Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { tail, fields } => {
                for field in fields {
                    self.collect_pos_kind(field.value, TypeContext::Value);
                }
                self.collect_pos_kind(*tail, TypeContext::Value);
            }
            Pos::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    self.collect_pos_kinds(payloads, TypeContext::Value);
                }
            }
            Pos::Tuple(items) => self.collect_pos_kinds(items, TypeContext::Value),
            Pos::Row(items) => self.collect_pos_kinds(items, TypeContext::Effect),
            Pos::Stack { inner, weight } => {
                self.collect_pos_kind(*inner, context);
                self.collect_stack_weight_kinds(weight);
            }
            Pos::NonSubtract(inner, _) => self.collect_pos_kind(*inner, context),
            Pos::Union(left, right) => {
                self.collect_pos_kind(*left, context);
                self.collect_pos_kind(*right, context);
            }
            Pos::Bot => {}
        }
    }

    fn collect_neg_kind(&mut self, id: NegId, context: TypeContext) {
        match self.arena.neg(id) {
            Neg::Var(var) => self.record_kind(*var, context),
            Neg::Con(_, args) => self.collect_neu_kinds(args, TypeContext::Value),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_pos_kind(*arg, TypeContext::Value);
                self.collect_pos_kind(*arg_eff, TypeContext::Effect);
                self.collect_neg_kind(*ret_eff, TypeContext::Effect);
                self.collect_neg_kind(*ret, TypeContext::Value);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.collect_neg_kind(field.value, TypeContext::Value);
                }
            }
            Neg::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    self.collect_neg_kinds(payloads, TypeContext::Value);
                }
            }
            Neg::Tuple(items) => self.collect_neg_kinds(items, TypeContext::Value),
            Neg::Row(items, tail) => {
                self.collect_neg_kinds(items, TypeContext::Effect);
                self.collect_neg_kind(*tail, TypeContext::Effect);
            }
            Neg::Stack { inner, weight } => {
                self.collect_neg_kind(*inner, context);
                self.collect_stack_weight_kinds(weight);
            }
            Neg::Intersection(left, right) => {
                self.collect_neg_kind(*left, context);
                self.collect_neg_kind(*right, context);
            }
            Neg::Top | Neg::Bot => {}
        }
    }

    fn collect_neu_kind(&mut self, id: NeuId, context: TypeContext) {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                self.collect_pos_kind(*lower, context);
                self.collect_neg_kind(*upper, context);
            }
            Neu::Con(_, args) => self.collect_neu_kinds(args, TypeContext::Value),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_neu_kind(*arg, TypeContext::Value);
                self.collect_neu_kind(*arg_eff, TypeContext::Effect);
                self.collect_neu_kind(*ret_eff, TypeContext::Effect);
                self.collect_neu_kind(*ret, TypeContext::Value);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.collect_neu_kind(field.value, TypeContext::Value);
                }
            }
            Neu::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    self.collect_neu_kinds(payloads, TypeContext::Value);
                }
            }
            Neu::Tuple(items) => self.collect_neu_kinds(items, TypeContext::Value),
        }
    }

    fn collect_pos_kinds(&mut self, ids: &[PosId], context: TypeContext) {
        for id in ids {
            self.collect_pos_kind(*id, context);
        }
    }

    fn collect_neg_kinds(&mut self, ids: &[NegId], context: TypeContext) {
        for id in ids {
            self.collect_neg_kind(*id, context);
        }
    }

    fn collect_neu_kinds(&mut self, ids: &[NeuId], context: TypeContext) {
        for id in ids {
            self.collect_neu_kind(*id, context);
        }
    }

    fn collect_stack_weight_kinds(&mut self, weight: &StackWeight) {
        for entry in weight.entries() {
            for item in entry.floor.iter().chain(&entry.stack) {
                self.collect_subtractability_kinds(item);
            }
        }
    }

    fn collect_subtractability_kinds(&mut self, item: &Subtractability) {
        match item {
            Subtractability::Empty | Subtractability::All => {}
            Subtractability::AllExcept(_, args) | Subtractability::Set(_, args) => {
                self.collect_neu_kinds(args, TypeContext::Value);
            }
            Subtractability::AllExceptMany(families) | Subtractability::SetMany(families) => {
                for (_, args) in families {
                    self.collect_neu_kinds(args, TypeContext::Value);
                }
            }
        }
    }
}

fn merge_effect_substitution(existing: Type, incoming: Type) -> Type {
    if existing.is_pure_effect() {
        return incoming;
    }
    if incoming.is_pure_effect() {
        return existing;
    }
    match (existing, incoming) {
        (Type::EffectRow(mut existing), Type::EffectRow(incoming)) => {
            for item in incoming {
                if !existing.contains(&item) {
                    existing.push(item);
                }
            }
            Type::EffectRow(existing)
        }
        (existing, incoming) => simplify_type(Type::Union(Box::new(existing), Box::new(incoming))),
    }
}

fn stack_type(inner: Type, weight: mono::StackWeight) -> Type {
    if weight.entries.is_empty() {
        return inner;
    }
    simplify_stack_type(inner, weight)
}

pub(crate) fn simplify_stack_type(inner: Type, weight: mono::StackWeight) -> Type {
    if weight.entries.is_empty() {
        return inner;
    }
    if !type_may_contain_effects(&inner) {
        return inner;
    }
    if let Some(effect) = apply_stack_to_effect(inner.clone(), &weight) {
        return effect;
    }
    Type::Stack {
        inner: Box::new(inner),
        weight,
    }
}

fn apply_stack_to_effect(effect: Type, weight: &mono::StackWeight) -> Option<Type> {
    match effect {
        Type::EffectRow(items) => Some(Type::EffectRow(filter_effect_row(items, weight))),
        Type::Intersection(left, right) => {
            let left = apply_stack_to_effect(*left, weight)?;
            let right = apply_stack_to_effect(*right, weight)?;
            Some(simplify_effect_intersection(left, right))
        }
        Type::Union(left, right) => {
            let left = apply_stack_to_effect(*left, weight)?;
            let right = apply_stack_to_effect(*right, weight)?;
            Some(simplify_effect_union(left, right))
        }
        Type::Any | Type::Never => Some(effect),
        Type::Stack {
            inner,
            weight: inner_weight,
        } => Some(stack_type(stack_type(*inner, inner_weight), weight.clone())),
        Type::Con { .. }
        | Type::Fun { .. }
        | Type::Thunk { .. }
        | Type::Record(_)
        | Type::PolyVariant(_)
        | Type::Tuple(_)
        | Type::OpenVar(_) => None,
    }
}

fn filter_effect_row(items: Vec<Type>, weight: &mono::StackWeight) -> Vec<Type> {
    let mut out = Vec::new();
    for item in flatten_effect_row_items(items) {
        if effect_item_survives_stack(&item, weight) && !out.contains(&item) {
            out.push(item);
        }
    }
    out
}

fn flatten_effect_row_items(items: Vec<Type>) -> Vec<Type> {
    let mut out = Vec::new();
    for item in items {
        match item {
            Type::EffectRow(nested) => out.extend(flatten_effect_row_items(nested)),
            other => out.push(other),
        }
    }
    out
}

fn effect_item_survives_stack(item: &Type, weight: &mono::StackWeight) -> bool {
    weight
        .entries
        .iter()
        .flat_map(|entry| entry.floor.iter().chain(&entry.stack))
        .all(|families| effect_families_allow_item(families, item))
}

fn effect_families_allow_item(families: &EffectFamilies, item: &Type) -> bool {
    match families {
        EffectFamilies::Empty => false,
        EffectFamilies::All => true,
        EffectFamilies::Set(allowed) => allowed
            .iter()
            .any(|family| effect_family_matches_item(family, item)),
        EffectFamilies::AllExcept(excluded) => !excluded
            .iter()
            .any(|family| effect_family_matches_item(family, item)),
    }
}

fn effect_family_matches_item(family: &EffectFamily, item: &Type) -> bool {
    let Type::Con { path, args } = item else {
        return false;
    };
    path == &family.path && args == &family.args
}

fn simplify_effect_intersection(left: Type, right: Type) -> Type {
    let simplified = simplify_intersection_type(left, right);
    if matches!(simplified, Type::Intersection(_, _)) {
        return simplified;
    }
    if simplified.is_pure_effect() {
        return Type::pure_effect();
    }
    simplified
}

fn simplify_intersection_type(left: Type, right: Type) -> Type {
    let mut parts = Vec::new();
    collect_intersection_parts(left, &mut parts);
    collect_intersection_parts(right, &mut parts);
    if parts.iter().any(|part| matches!(part, Type::Never)) {
        return Type::Never;
    }
    let mut unique = Vec::new();
    for part in parts {
        if matches!(part, Type::Any) || unique.contains(&part) {
            continue;
        }
        unique.push(part);
    }
    match unique.as_slice() {
        [] => Type::Any,
        [single] => single.clone(),
        _ if unique.iter().all(|part| matches!(part, Type::EffectRow(_))) => {
            intersect_effect_rows(unique)
        }
        _ if unique.iter().all(Type::is_pure_effect) => Type::pure_effect(),
        _ => unique
            .into_iter()
            .reduce(|left, right| Type::Intersection(Box::new(left), Box::new(right)))
            .expect("non-empty intersection parts"),
    }
}

pub(crate) fn simplify_type(ty: Type) -> Type {
    match ty {
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(simplify_type(*arg)),
            arg_effect: Box::new(simplify_type(*arg_effect)),
            ret_effect: Box::new(simplify_type(*ret_effect)),
            ret: Box::new(simplify_type(*ret)),
        },
        Type::Thunk { effect, value } => Type::Thunk {
            effect: Box::new(simplify_type(*effect)),
            value: Box::new(simplify_type(*value)),
        },
        Type::Con { path, args } => Type::Con {
            path,
            args: args.into_iter().map(simplify_type).collect(),
        },
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    value: simplify_type(field.value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::PolyVariant(variants) => Type::PolyVariant(
            variants
                .into_iter()
                .map(|variant| TypeVariant {
                    name: variant.name,
                    payloads: variant.payloads.into_iter().map(simplify_type).collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(items.into_iter().map(simplify_type).collect()),
        Type::EffectRow(items) => simplify_effect_row(items),
        Type::Stack { inner, weight } => simplify_stack_type(simplify_type(*inner), weight),
        Type::Union(left, right) => {
            simplify_union_type(simplify_type(*left), simplify_type(*right))
        }
        Type::Intersection(left, right) => {
            simplify_intersection_type(simplify_type(*left), simplify_type(*right))
        }
        Type::Any | Type::Never | Type::OpenVar(_) => ty,
    }
}

fn type_may_contain_effects(ty: &Type) -> bool {
    match ty {
        Type::Any
        | Type::OpenVar(_)
        | Type::EffectRow(_)
        | Type::Thunk { .. }
        | Type::Fun { .. } => true,
        Type::Con { args, .. } | Type::Tuple(args) => args.iter().any(type_may_contain_effects),
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_may_contain_effects(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_may_contain_effects)),
        Type::Stack { .. } => true,
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_may_contain_effects(left) || type_may_contain_effects(right)
        }
        Type::Never => false,
    }
}

fn collect_intersection_parts(ty: Type, out: &mut Vec<Type>) {
    match ty {
        Type::Intersection(left, right) => {
            collect_intersection_parts(*left, out);
            collect_intersection_parts(*right, out);
        }
        ty => out.push(ty),
    }
}

fn simplify_effect_union(left: Type, right: Type) -> Type {
    let simplified = simplify_union_type(left, right);
    if matches!(simplified, Type::Union(_, _)) {
        return simplified;
    }
    if simplified.is_pure_effect() {
        return Type::pure_effect();
    }
    simplified
}

fn simplify_union_type(left: Type, right: Type) -> Type {
    if left == right {
        return left;
    }
    if matches!(left, Type::Never) {
        return right;
    }
    if matches!(right, Type::Never) {
        return left;
    }
    if matches!(left, Type::Any) || matches!(right, Type::Any) {
        return Type::Any;
    }
    if let (Type::EffectRow(left), Type::EffectRow(right)) = (left.clone(), right.clone()) {
        return union_effect_rows(left, right);
    }
    if left.is_pure_effect() && right.is_pure_effect() {
        return Type::pure_effect();
    }
    Type::Union(Box::new(left), Box::new(right))
}

fn simplify_effect_row(items: Vec<Type>) -> Type {
    let mut out = Vec::new();
    push_effect_row_items(&mut out, items);
    Type::EffectRow(out)
}

fn push_effect_row_items(out: &mut Vec<Type>, items: Vec<Type>) {
    for item in items {
        match simplify_type(item) {
            item if item.is_pure_effect() => {}
            Type::EffectRow(items) => push_effect_row_items(out, items),
            item if out.contains(&item) => {}
            item => out.push(item),
        }
    }
}

fn union_effect_rows(left: Vec<Type>, right: Vec<Type>) -> Type {
    let mut out = Vec::new();
    push_effect_row_items(&mut out, left);
    push_effect_row_items(&mut out, right);
    Type::EffectRow(out)
}

fn intersect_effect_rows(rows: Vec<Type>) -> Type {
    let mut rows = rows.into_iter().map(effect_row_items);
    let Some(first) = rows.next() else {
        return Type::pure_effect();
    };
    let mut out = first;
    for row in rows {
        out.retain(|item| row.contains(item));
    }
    Type::EffectRow(out)
}

fn effect_row_items(row: Type) -> Vec<Type> {
    let Type::EffectRow(items) = row else {
        return Vec::new();
    };
    let mut out = Vec::new();
    push_effect_row_items(&mut out, items);
    out
}

#[cfg(test)]
mod tests {
    use mono::Type;

    use super::simplify_type;

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

    fn effect(name: &str) -> Type {
        Type::Con {
            path: vec![name.to_string()],
            args: Vec::new(),
        }
    }
}
