use std::collections::{HashMap, HashSet};

use mono::{
    EffectFamilies, EffectFamily, Signature, StackWeightEntry, Type, TypeField, TypeVariant,
};
use poly::expr as poly_expr;
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicateArg, Scheme, StackWeight,
    Subtractability, TypeArena, TypeVar,
};

use crate::{SchemeFeature, SpecializeError};

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

pub(crate) fn type_hint_for_scheme(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
) -> Result<Option<Type>, SpecializeError> {
    if has_type_quantifiers(scheme) {
        return Ok(None);
    }
    Ok(Some(signature_for_scheme(arena, def, scheme, None)?.ty))
}

pub(crate) fn function_signature_for_scheme(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    arg: Option<&Type>,
    ret: Option<&Type>,
) -> Result<Option<Signature>, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let Pos::Fun {
        arg: scheme_arg,
        ret: scheme_ret,
        ..
    } = arena.typ.pos(scheme.predicate)
    else {
        return Ok(None);
    };
    let mut materializer = SchemeMaterializer::new(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    if let Some(arg) = arg {
        materializer.match_neg(*scheme_arg, arg, TypeContext::Value)?;
    }
    if let Some(ret) = ret {
        materializer.match_pos(*scheme_ret, ret, TypeContext::Value)?;
    }
    materializer.default_unbound_quantifiers();
    Ok(Some(Signature {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
    }))
}

pub(crate) fn function_return_hint_for_scheme(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    arg: Option<&Type>,
) -> Result<Option<Type>, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let Pos::Fun {
        arg: scheme_arg,
        ret: scheme_ret,
        ..
    } = arena.typ.pos(scheme.predicate)
    else {
        return Ok(None);
    };
    let mut materializer = SchemeMaterializer::new(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    if let Some(arg) = arg {
        materializer.match_neg(*scheme_arg, arg, TypeContext::Value)?;
    }
    materializer.default_unbound_quantifiers();
    Ok(Some(
        materializer.materialize_pos(*scheme_ret, TypeContext::Value)?,
    ))
}

pub(crate) fn has_type_quantifiers(scheme: &Scheme) -> bool {
    !scheme.quantifiers.is_empty()
        || !scheme.role_predicates.is_empty()
        || !scheme.recursive_bounds.is_empty()
        || !scheme.stack_quantifiers.is_empty()
}

pub(crate) fn pure_function_type(arg: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(arg),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(Type::pure_effect()),
        ret: Box::new(ret),
    }
}

fn reject_unsupported_scheme_features(
    def: poly_expr::DefId,
    scheme: &Scheme,
) -> Result<(), SpecializeError> {
    if !scheme.role_predicates.is_empty() {
        return Err(SpecializeError::UnsupportedSchemeFeature {
            def: mono::DefId(def.0),
            feature: SchemeFeature::RolePredicates,
        });
    }
    if !scheme.recursive_bounds.is_empty() {
        return Err(SpecializeError::UnsupportedSchemeFeature {
            def: mono::DefId(def.0),
            feature: SchemeFeature::RecursiveBounds,
        });
    }
    if !scheme.stack_quantifiers.is_empty() {
        return Err(SpecializeError::UnsupportedSchemeFeature {
            def: mono::DefId(def.0),
            feature: SchemeFeature::StackQuantifiers,
        });
    }
    Ok(())
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
        if !self.quantifiers.contains(&var) {
            return Ok(());
        }
        if let Some(existing) = self.substitution.get(&var) {
            if existing == ty {
                return Ok(());
            }
            return Err(SpecializeError::ConflictingTypeSubstitution {
                def: mono::DefId(self.def.0),
                var: var.0,
                existing: existing.clone(),
                incoming: ty.clone(),
            });
        }
        self.substitution.insert(var, ty.clone());
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
                self.match_neg(*arg, expected_arg, TypeContext::Value)?;
                self.match_neg(*arg_eff, expected_arg_eff, TypeContext::Effect)?;
                self.match_pos(*ret_eff, expected_ret_eff, TypeContext::Effect)?;
                self.match_pos(*ret, expected_ret, TypeContext::Value)
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
            Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => {
                self.match_pos(*inner, expected, context)
            }
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
                self.match_pos(*arg, expected_arg, TypeContext::Value)?;
                self.match_pos(*arg_eff, expected_arg_eff, TypeContext::Effect)?;
                self.match_neg(*ret_eff, expected_ret_eff, TypeContext::Effect)?;
                self.match_neg(*ret, expected_ret, TypeContext::Value)
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
            Neg::Stack { inner, .. } => self.match_neg(*inner, expected, context),
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
                self.match_neu(*arg, expected_arg, TypeContext::Value)?;
                self.match_neu(*arg_eff, expected_arg_eff, TypeContext::Effect)?;
                self.match_neu(*ret_eff, expected_ret_eff, TypeContext::Effect)?;
                self.match_neu(*ret, expected_ret, TypeContext::Value)
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
            } => Type::Fun {
                arg: Box::new(self.materialize_neg(*arg, TypeContext::Value)?),
                arg_effect: Box::new(self.materialize_neg(*arg_eff, TypeContext::Effect)?),
                ret_effect: Box::new(self.materialize_pos(*ret_eff, TypeContext::Effect)?),
                ret: Box::new(self.materialize_pos(*ret, TypeContext::Value)?),
            },
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
            Pos::Stack { inner, weight } => Type::Stack {
                inner: Box::new(self.materialize_pos(*inner, context)?),
                weight: self.materialize_stack_weight(weight)?,
            },
            Pos::NonSubtract(inner, subtract) => Type::Stack {
                inner: Box::new(self.materialize_pos(*inner, context)?),
                weight: mono::StackWeight {
                    entries: vec![StackWeightEntry {
                        id: subtract.0,
                        pops: 1,
                        floor: Vec::new(),
                        stack: Vec::new(),
                    }],
                },
            },
            Pos::Union(left, right) => Type::Union(
                Box::new(self.materialize_pos(*left, context)?),
                Box::new(self.materialize_pos(*right, context)?),
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
            } => Type::Fun {
                arg: Box::new(self.materialize_pos(*arg, TypeContext::Value)?),
                arg_effect: Box::new(self.materialize_pos(*arg_eff, TypeContext::Effect)?),
                ret_effect: Box::new(self.materialize_neg(*ret_eff, TypeContext::Effect)?),
                ret: Box::new(self.materialize_neg(*ret, TypeContext::Value)?),
            },
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
                if !matches!(tail, Type::Any | Type::Never) && !tail.is_pure_effect() {
                    items.push(tail);
                }
                Type::EffectRow(items)
            }
            Neg::Stack { inner, weight } => Type::Stack {
                inner: Box::new(self.materialize_neg(*inner, context)?),
                weight: self.materialize_stack_weight(weight)?,
            },
            Neg::Intersection(left, right) => Type::Intersection(
                Box::new(self.materialize_neg(*left, context)?),
                Box::new(self.materialize_neg(*right, context)?),
            ),
        })
    }

    fn materialize_neu(&self, id: NeuId, context: TypeContext) -> Result<Type, SpecializeError> {
        Ok(match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                if !matches!(self.arena.pos(*lower), Pos::Bot) {
                    self.materialize_pos(*lower, context)?
                } else if !matches!(self.arena.neg(*upper), Neg::Top) {
                    self.materialize_neg(*upper, context)?
                } else {
                    match context {
                        TypeContext::Value => Type::unit(),
                        TypeContext::Effect => Type::pure_effect(),
                    }
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
            } => Type::Fun {
                arg: Box::new(self.materialize_neu(*arg, TypeContext::Value)?),
                arg_effect: Box::new(self.materialize_neu(*arg_eff, TypeContext::Effect)?),
                ret_effect: Box::new(self.materialize_neu(*ret_eff, TypeContext::Effect)?),
                ret: Box::new(self.materialize_neu(*ret, TypeContext::Value)?),
            },
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
