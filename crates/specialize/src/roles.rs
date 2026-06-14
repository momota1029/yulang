use std::collections::HashMap;

use mono::{Type, TypeField, TypeVariant};
use poly::roles as poly_roles;
use poly::types::{Neg, NegId, Neu, NeuId, Pos, PosId, TypeArena, TypeVar};

use crate::types;

pub(crate) struct RoleCandidateApplication {
    pub(crate) associated: Vec<(Type, Type, Type)>,
    pub(crate) prerequisites: Vec<types::InstantiatedRolePredicate>,
}

pub(crate) fn candidate_application(
    arena: &TypeArena,
    demand: &types::InstantiatedRolePredicate,
    candidate: &poly_roles::RoleImplCandidate,
    input_types: &[Type],
) -> Option<RoleCandidateApplication> {
    if candidate.inputs.len() != input_types.len() {
        return None;
    }
    if !demand.associated.iter().all(|associated| {
        candidate
            .associated
            .iter()
            .any(|candidate| candidate.name == associated.name)
    }) {
        return None;
    }

    let mut matcher = RoleCandidateMatcher::new(arena);
    for (candidate_arg, demand_type) in candidate.inputs.iter().zip(input_types) {
        if !matcher.match_arg(candidate_arg, demand_type) {
            return None;
        }
    }

    let materializer = matcher.materializer();
    let mut associated = Vec::with_capacity(demand.associated.len());
    for demand_associated in &demand.associated {
        let candidate_associated = candidate
            .associated
            .iter()
            .find(|candidate| candidate.name == demand_associated.name)?;
        let candidate_type = materializer.materialize_arg_exact(&candidate_associated.value)?;
        associated.push((
            demand_associated.lower.clone(),
            candidate_type,
            demand_associated.upper.clone(),
        ));
    }

    let prerequisites = candidate
        .prerequisites
        .iter()
        .map(|prerequisite| materializer.materialize_constraint(prerequisite))
        .collect::<Option<Vec<_>>>()?;
    Some(RoleCandidateApplication {
        associated,
        prerequisites,
    })
}

struct RoleCandidateMatcher<'a> {
    arena: &'a TypeArena,
    substitution: HashMap<TypeVar, Type>,
}

impl<'a> RoleCandidateMatcher<'a> {
    fn new(arena: &'a TypeArena) -> Self {
        Self {
            arena,
            substitution: HashMap::new(),
        }
    }

    fn materializer(&self) -> RoleCandidateMaterializer<'_> {
        RoleCandidateMaterializer {
            arena: self.arena,
            substitution: &self.substitution,
        }
    }

    fn match_arg(&mut self, arg: &poly_roles::RoleConstraintArg, demand: &Type) -> bool {
        self.match_pos(arg.lower, demand) && self.match_neg(arg.upper, demand)
    }

    fn bind_var(&mut self, var: TypeVar, ty: &Type) -> bool {
        let ty = types::simplify_type(ty.clone());
        match self.substitution.get(&var) {
            Some(existing) => type_candidates_equivalent(existing, &ty),
            None => {
                self.substitution.insert(var, ty);
                true
            }
        }
    }

    fn match_pos(&mut self, id: PosId, demand: &Type) -> bool {
        match self.arena.pos(id) {
            Pos::Bot => true,
            Pos::Var(var) => self.bind_var(*var, demand),
            Pos::Con(path, args) => self.match_con(path, args, demand),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let Type::Fun {
                    arg: demand_arg,
                    arg_effect: demand_arg_eff,
                    ret_effect: demand_ret_eff,
                    ret: demand_ret,
                } = demand
                else {
                    return false;
                };
                let (demand_arg, demand_arg_eff) = split_runtime_shape(demand_arg, demand_arg_eff);
                let (demand_ret, demand_ret_eff) = split_runtime_shape(demand_ret, demand_ret_eff);
                self.match_neg(*arg, &demand_arg)
                    && self.match_neg(*arg_eff, &demand_arg_eff)
                    && self.match_pos(*ret_eff, &demand_ret_eff)
                    && self.match_pos(*ret, &demand_ret)
            }
            Pos::Record(fields) => self.match_record_pos(fields, demand),
            Pos::RecordTailSpread { fields, tail } => {
                self.match_record_pos(fields, demand) && self.match_pos(*tail, demand)
            }
            Pos::RecordHeadSpread { tail, fields } => {
                self.match_pos(*tail, demand) && self.match_record_pos(fields, demand)
            }
            Pos::PolyVariant(variants) => self.match_poly_variant_pos(variants, demand),
            Pos::Tuple(items) => {
                let Type::Tuple(demand_items) = demand else {
                    return false;
                };
                items.len() == demand_items.len()
                    && items
                        .iter()
                        .zip(demand_items)
                        .all(|(item, demand)| self.match_pos(*item, demand))
            }
            Pos::Row(items) => {
                let Type::EffectRow(demand_items) = demand else {
                    return false;
                };
                items.len() == demand_items.len()
                    && items
                        .iter()
                        .zip(demand_items)
                        .all(|(item, demand)| self.match_pos(*item, demand))
            }
            Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => self.match_pos(*inner, demand),
            Pos::Union(left, right) => {
                self.match_pos(*left, demand) || self.match_pos(*right, demand)
            }
        }
    }

    fn match_neg(&mut self, id: NegId, demand: &Type) -> bool {
        match self.arena.neg(id) {
            Neg::Top => true,
            Neg::Bot => matches!(demand, Type::Never),
            Neg::Var(var) => self.bind_var(*var, demand),
            Neg::Con(path, args) => self.match_con(path, args, demand),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let Type::Fun {
                    arg: demand_arg,
                    arg_effect: demand_arg_eff,
                    ret_effect: demand_ret_eff,
                    ret: demand_ret,
                } = demand
                else {
                    return false;
                };
                let (demand_arg, demand_arg_eff) = split_runtime_shape(demand_arg, demand_arg_eff);
                let (demand_ret, demand_ret_eff) = split_runtime_shape(demand_ret, demand_ret_eff);
                self.match_pos(*arg, &demand_arg)
                    && self.match_pos(*arg_eff, &demand_arg_eff)
                    && self.match_neg(*ret_eff, &demand_ret_eff)
                    && self.match_neg(*ret, &demand_ret)
            }
            Neg::Record(fields) => self.match_record_neg(fields, demand),
            Neg::PolyVariant(variants) => self.match_poly_variant_neg(variants, demand),
            Neg::Tuple(items) => {
                let Type::Tuple(demand_items) = demand else {
                    return false;
                };
                items.len() == demand_items.len()
                    && items
                        .iter()
                        .zip(demand_items)
                        .all(|(item, demand)| self.match_neg(*item, demand))
            }
            Neg::Row(items, tail) => {
                let Type::EffectRow(demand_items) = demand else {
                    return false;
                };
                if demand_items.len() < items.len() {
                    return false;
                }
                items
                    .iter()
                    .zip(demand_items.iter())
                    .all(|(item, demand)| self.match_neg(*item, demand))
                    && match demand_items.get(items.len()) {
                        Some(tail_item) => self.match_neg(*tail, tail_item),
                        None => self.match_neg(*tail, &Type::pure_effect()),
                    }
            }
            Neg::Stack { inner, .. } => self.match_neg(*inner, demand),
            Neg::Intersection(left, right) => {
                self.match_neg(*left, demand) && self.match_neg(*right, demand)
            }
        }
    }

    fn match_neu(&mut self, id: NeuId, demand: &Type) -> bool {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                self.match_pos(*lower, demand) && self.match_neg(*upper, demand)
            }
            Neu::Con(path, args) => self.match_con(path, args, demand),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let Type::Fun {
                    arg: demand_arg,
                    arg_effect: demand_arg_eff,
                    ret_effect: demand_ret_eff,
                    ret: demand_ret,
                } = demand
                else {
                    return false;
                };
                let (demand_arg, demand_arg_eff) = split_runtime_shape(demand_arg, demand_arg_eff);
                let (demand_ret, demand_ret_eff) = split_runtime_shape(demand_ret, demand_ret_eff);
                self.match_neu(*arg, &demand_arg)
                    && self.match_neu(*arg_eff, &demand_arg_eff)
                    && self.match_neu(*ret_eff, &demand_ret_eff)
                    && self.match_neu(*ret, &demand_ret)
            }
            Neu::Record(fields) => self.match_record_neu(fields, demand),
            Neu::PolyVariant(variants) => self.match_poly_variant_neu(variants, demand),
            Neu::Tuple(items) => {
                let Type::Tuple(demand_items) = demand else {
                    return false;
                };
                items.len() == demand_items.len()
                    && items
                        .iter()
                        .zip(demand_items)
                        .all(|(item, demand)| self.match_neu(*item, demand))
            }
        }
    }

    fn match_con(&mut self, path: &[String], args: &[NeuId], demand: &Type) -> bool {
        let Type::Con {
            path: demand_path,
            args: demand_args,
        } = demand
        else {
            return false;
        };
        path == demand_path
            && args.len() == demand_args.len()
            && args
                .iter()
                .zip(demand_args)
                .all(|(arg, demand)| self.match_neu(*arg, demand))
    }

    fn match_record_pos(
        &mut self,
        fields: &[poly::types::RecordField<PosId>],
        demand: &Type,
    ) -> bool {
        let Type::Record(demand_fields) = demand else {
            return false;
        };
        fields.iter().all(|field| {
            demand_fields
                .iter()
                .find(|demand| demand.name == field.name)
                .is_some_and(|demand| self.match_pos(field.value, &demand.value))
        })
    }

    fn match_record_neg(
        &mut self,
        fields: &[poly::types::RecordField<NegId>],
        demand: &Type,
    ) -> bool {
        let Type::Record(demand_fields) = demand else {
            return false;
        };
        fields.iter().all(|field| {
            demand_fields
                .iter()
                .find(|demand| demand.name == field.name)
                .is_some_and(|demand| self.match_neg(field.value, &demand.value))
        })
    }

    fn match_record_neu(
        &mut self,
        fields: &[poly::types::RecordField<NeuId>],
        demand: &Type,
    ) -> bool {
        let Type::Record(demand_fields) = demand else {
            return false;
        };
        fields.iter().all(|field| {
            demand_fields
                .iter()
                .find(|demand| demand.name == field.name)
                .is_some_and(|demand| self.match_neu(field.value, &demand.value))
        })
    }

    fn match_poly_variant_pos(&mut self, variants: &[(String, Vec<PosId>)], demand: &Type) -> bool {
        let Type::PolyVariant(demand_variants) = demand else {
            return false;
        };
        variants.iter().all(|(name, payloads)| {
            demand_variants
                .iter()
                .find(|demand| demand.name == *name && demand.payloads.len() == payloads.len())
                .is_some_and(|demand| {
                    payloads
                        .iter()
                        .zip(&demand.payloads)
                        .all(|(payload, demand)| self.match_pos(*payload, demand))
                })
        })
    }

    fn match_poly_variant_neg(&mut self, variants: &[(String, Vec<NegId>)], demand: &Type) -> bool {
        let Type::PolyVariant(demand_variants) = demand else {
            return false;
        };
        variants.iter().all(|(name, payloads)| {
            demand_variants
                .iter()
                .find(|demand| demand.name == *name && demand.payloads.len() == payloads.len())
                .is_some_and(|demand| {
                    payloads
                        .iter()
                        .zip(&demand.payloads)
                        .all(|(payload, demand)| self.match_neg(*payload, demand))
                })
        })
    }

    fn match_poly_variant_neu(&mut self, variants: &[(String, Vec<NeuId>)], demand: &Type) -> bool {
        let Type::PolyVariant(demand_variants) = demand else {
            return false;
        };
        variants.iter().all(|(name, payloads)| {
            demand_variants
                .iter()
                .find(|demand| demand.name == *name && demand.payloads.len() == payloads.len())
                .is_some_and(|demand| {
                    payloads
                        .iter()
                        .zip(&demand.payloads)
                        .all(|(payload, demand)| self.match_neu(*payload, demand))
                })
        })
    }
}

struct RoleCandidateMaterializer<'a> {
    arena: &'a TypeArena,
    substitution: &'a HashMap<TypeVar, Type>,
}

impl<'a> RoleCandidateMaterializer<'a> {
    fn materialize_constraint(
        &self,
        constraint: &poly_roles::RoleConstraint,
    ) -> Option<types::InstantiatedRolePredicate> {
        Some(types::InstantiatedRolePredicate {
            role: constraint.role.clone(),
            inputs: constraint
                .inputs
                .iter()
                .map(|arg| self.materialize_arg(arg))
                .collect::<Option<Vec<_>>>()?,
            associated: constraint
                .associated
                .iter()
                .map(|associated| {
                    let arg = self.materialize_arg(&associated.value)?;
                    Some(types::InstantiatedRoleAssociatedType {
                        name: associated.name.clone(),
                        lower: arg.lower,
                        upper: arg.upper,
                    })
                })
                .collect::<Option<Vec<_>>>()?,
        })
    }

    fn materialize_arg_exact(&self, arg: &poly_roles::RoleConstraintArg) -> Option<Type> {
        let arg = self.materialize_arg(arg)?;
        choose_role_arg_exact_type(arg.lower, arg.upper)
    }

    fn materialize_arg(
        &self,
        arg: &poly_roles::RoleConstraintArg,
    ) -> Option<types::InstantiatedRoleArg> {
        Some(types::InstantiatedRoleArg {
            lower: self.materialize_pos(arg.lower)?,
            upper: self.materialize_neg(arg.upper)?,
        })
    }

    fn materialize_pos(&self, id: PosId) -> Option<Type> {
        Some(match self.arena.pos(id) {
            Pos::Bot => Type::Never,
            Pos::Var(var) => self.substitution.get(var)?.clone(),
            Pos::Con(path, args) => Type::Con {
                path: path.clone(),
                args: self.materialize_neus(args)?,
            },
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => role_runtime_function_type(
                self.materialize_neg(*arg)?,
                self.materialize_neg(*arg_eff)?,
                self.materialize_pos(*ret_eff)?,
                self.materialize_pos(*ret)?,
            ),
            Pos::Record(fields) => {
                Type::Record(self.materialize_fields(fields, Self::materialize_pos)?)
            }
            Pos::RecordTailSpread { fields, tail } => {
                let mut fields = self.materialize_fields(fields, Self::materialize_pos)?;
                if let Type::Record(tail) = self.materialize_pos(*tail)? {
                    fields.extend(tail);
                }
                Type::Record(fields)
            }
            Pos::RecordHeadSpread { tail, fields } => {
                let mut out = match self.materialize_pos(*tail)? {
                    Type::Record(fields) => fields,
                    _ => Vec::new(),
                };
                out.extend(self.materialize_fields(fields, Self::materialize_pos)?);
                Type::Record(out)
            }
            Pos::PolyVariant(variants) => Type::PolyVariant(
                variants
                    .iter()
                    .map(|(name, payloads)| {
                        Some(TypeVariant {
                            name: name.clone(),
                            payloads: self.materialize_poss(payloads)?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
            Pos::Tuple(items) => Type::Tuple(self.materialize_poss(items)?),
            Pos::Row(items) => Type::EffectRow(self.materialize_poss(items)?),
            Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => {
                self.materialize_pos(*inner)?
            }
            Pos::Union(left, right) => types::simplify_type(Type::Union(
                Box::new(self.materialize_pos(*left)?),
                Box::new(self.materialize_pos(*right)?),
            )),
        })
    }

    fn materialize_neg(&self, id: NegId) -> Option<Type> {
        Some(match self.arena.neg(id) {
            Neg::Top => Type::Any,
            Neg::Bot => Type::Never,
            Neg::Var(var) => self.substitution.get(var)?.clone(),
            Neg::Con(path, args) => Type::Con {
                path: path.clone(),
                args: self.materialize_neus(args)?,
            },
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => role_runtime_function_type(
                self.materialize_pos(*arg)?,
                self.materialize_pos(*arg_eff)?,
                self.materialize_neg(*ret_eff)?,
                self.materialize_neg(*ret)?,
            ),
            Neg::Record(fields) => {
                Type::Record(self.materialize_fields(fields, Self::materialize_neg)?)
            }
            Neg::PolyVariant(variants) => Type::PolyVariant(
                variants
                    .iter()
                    .map(|(name, payloads)| {
                        Some(TypeVariant {
                            name: name.clone(),
                            payloads: self.materialize_negs(payloads)?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
            Neg::Tuple(items) => Type::Tuple(self.materialize_negs(items)?),
            Neg::Row(items, tail) => {
                let mut items = self.materialize_negs(items)?;
                match self.materialize_neg(*tail)? {
                    Type::EffectRow(tail_items) => items.extend(tail_items),
                    Type::Any | Type::Never => {}
                    tail if tail.is_pure_effect() => {}
                    tail => items.push(tail),
                }
                Type::EffectRow(items)
            }
            Neg::Stack { inner, .. } => self.materialize_neg(*inner)?,
            Neg::Intersection(left, right) => types::simplify_type(Type::Intersection(
                Box::new(self.materialize_neg(*left)?),
                Box::new(self.materialize_neg(*right)?),
            )),
        })
    }

    fn materialize_neu(&self, id: NeuId) -> Option<Type> {
        Some(match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => choose_role_arg_exact_type(
                self.materialize_pos(*lower)?,
                self.materialize_neg(*upper)?,
            )?,
            Neu::Con(path, args) => Type::Con {
                path: path.clone(),
                args: self.materialize_neus(args)?,
            },
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => role_runtime_function_type(
                self.materialize_neu(*arg)?,
                self.materialize_neu(*arg_eff)?,
                self.materialize_neu(*ret_eff)?,
                self.materialize_neu(*ret)?,
            ),
            Neu::Record(fields) => {
                Type::Record(self.materialize_fields(fields, Self::materialize_neu)?)
            }
            Neu::PolyVariant(variants) => Type::PolyVariant(
                variants
                    .iter()
                    .map(|(name, payloads)| {
                        Some(TypeVariant {
                            name: name.clone(),
                            payloads: self.materialize_neus(payloads)?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
            Neu::Tuple(items) => Type::Tuple(self.materialize_neus(items)?),
        })
    }

    fn materialize_fields<T>(
        &self,
        fields: &[poly::types::RecordField<T>],
        materialize: fn(&Self, T) -> Option<Type>,
    ) -> Option<Vec<TypeField>>
    where
        T: Copy,
    {
        fields
            .iter()
            .map(|field| {
                Some(TypeField {
                    name: field.name.clone(),
                    value: materialize(self, field.value)?,
                    optional: field.optional,
                })
            })
            .collect()
    }

    fn materialize_poss(&self, ids: &[PosId]) -> Option<Vec<Type>> {
        ids.iter().map(|id| self.materialize_pos(*id)).collect()
    }

    fn materialize_negs(&self, ids: &[NegId]) -> Option<Vec<Type>> {
        ids.iter().map(|id| self.materialize_neg(*id)).collect()
    }

    fn materialize_neus(&self, ids: &[NeuId]) -> Option<Vec<Type>> {
        ids.iter().map(|id| self.materialize_neu(*id)).collect()
    }
}

fn choose_role_arg_exact_type(lower: Type, upper: Type) -> Option<Type> {
    let lower = non_trivial_role_bound(RoleArgBound::Lower, lower);
    let upper = non_trivial_role_bound(RoleArgBound::Upper, upper);
    match (lower, upper) {
        (Some(lower), Some(upper)) if type_candidates_equivalent(&lower, &upper) => Some(lower),
        (Some(lower), None) => Some(lower),
        (None, Some(upper)) => Some(upper),
        (None, None) => None,
        _ => None,
    }
}

fn role_runtime_function_type(arg: Type, arg_effect: Type, ret_effect: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(types::runtime_shape(arg_effect, arg)),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(Type::pure_effect()),
        ret: Box::new(types::runtime_shape(ret_effect, ret)),
    }
}

fn split_runtime_shape(shape: &Type, legacy_effect: &Type) -> (Type, Type) {
    match shape {
        Type::Thunk { effect, value } => (value.as_ref().clone(), effect.as_ref().clone()),
        _ => (shape.clone(), legacy_effect.clone()),
    }
}

#[derive(Debug, Clone, Copy)]
enum RoleArgBound {
    Lower,
    Upper,
}

fn non_trivial_role_bound(side: RoleArgBound, ty: Type) -> Option<Type> {
    match (side, &ty) {
        (RoleArgBound::Lower, Type::Never) | (RoleArgBound::Upper, Type::Any) => None,
        _ => Some(ty),
    }
}

fn type_candidates_equivalent(left: &Type, right: &Type) -> bool {
    left == right || left.is_pure_effect() && right.is_pure_effect()
}
