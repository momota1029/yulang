//! Generalized scheme を use-site の infer arena へ展開する入口。
//!
//! `poly::Scheme` は final IR 側の `TypeArena` に載るため、量化済み def を参照する use-site では
//! predicate を infer arena へ fresh clone してから通常の subtype 制約として戻す。

use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, Scheme, SubtractId, Subtractability,
    TypeArena, TypeVar,
};
use rustc_hash::FxHashMap;

use crate::arena::Arena as InferArena;
use crate::constraints::TypeLevel;

pub(crate) fn instantiate_scheme(
    source: &TypeArena,
    target: &mut InferArena,
    level: TypeLevel,
    scheme: &Scheme,
) -> PosId {
    let mut instantiator = SchemeInstantiator::new(source, target, level);
    instantiator.instantiate_scheme(scheme)
}

struct SchemeInstantiator<'a> {
    source: &'a TypeArena,
    target: &'a mut InferArena,
    level: TypeLevel,
    vars: FxHashMap<TypeVar, TypeVar>,
    subtracts: FxHashMap<SubtractId, SubtractId>,
}

impl<'a> SchemeInstantiator<'a> {
    fn new(source: &'a TypeArena, target: &'a mut InferArena, level: TypeLevel) -> Self {
        Self {
            source,
            target,
            level,
            vars: FxHashMap::default(),
            subtracts: FxHashMap::default(),
        }
    }

    fn instantiate_scheme(&mut self, scheme: &Scheme) -> PosId {
        for var in &scheme.quantifiers {
            self.fresh_var(*var);
        }
        for (_, subtract) in &scheme.subtracts {
            self.fresh_subtract(*subtract);
        }
        self.clone_scheme_subtract_facts(scheme);
        self.clone_pos(scheme.predicate)
    }

    fn fresh_var(&mut self, source: TypeVar) -> TypeVar {
        if let Some(target) = self.vars.get(&source).copied() {
            return target;
        }
        let target = self.target.fresh_type_var_at(self.level);
        self.vars.insert(source, target);
        target
    }

    fn fresh_subtract(&mut self, source: SubtractId) -> SubtractId {
        if let Some(target) = self.subtracts.get(&source).copied() {
            return target;
        }
        let target = self.target.fresh_subtract_id();
        self.subtracts.insert(source, target);
        target
    }

    fn clone_var(&self, source: TypeVar) -> TypeVar {
        self.vars.get(&source).copied().unwrap_or(source)
    }

    fn clone_subtract(&self, source: SubtractId) -> SubtractId {
        self.subtracts.get(&source).copied().unwrap_or(source)
    }

    fn clone_pos(&mut self, id: PosId) -> PosId {
        let pos = match self.source.pos(id).clone() {
            Pos::Bot => Pos::Bot,
            Pos::Var(var) => Pos::Var(self.clone_var(var)),
            Pos::Con(path, args) => {
                Pos::Con(path, args.iter().map(|arg| self.clone_neu(*arg)).collect())
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Pos::Fun {
                arg: self.clone_neg(arg),
                arg_eff: self.clone_neg(arg_eff),
                ret_eff: self.clone_pos(ret_eff),
                ret: self.clone_pos(ret),
            },
            Pos::Record(fields) => Pos::Record(self.clone_fields(&fields, Self::clone_pos)),
            Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
                fields: self.clone_fields(&fields, Self::clone_pos),
                tail: self.clone_pos(tail),
            },
            Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
                tail: self.clone_pos(tail),
                fields: self.clone_fields(&fields, Self::clone_pos),
            },
            Pos::PolyVariant(variants) => Pos::PolyVariant(
                variants
                    .into_iter()
                    .map(|(name, args)| {
                        (
                            name,
                            args.into_iter().map(|arg| self.clone_pos(arg)).collect(),
                        )
                    })
                    .collect(),
            ),
            Pos::Tuple(items) => {
                Pos::Tuple(items.into_iter().map(|item| self.clone_pos(item)).collect())
            }
            Pos::Row(items) => {
                Pos::Row(items.into_iter().map(|item| self.clone_pos(item)).collect())
            }
            Pos::NonSubtract(pos, subtract) => {
                Pos::NonSubtract(self.clone_pos(pos), self.clone_subtract(subtract))
            }
            Pos::Union(left, right) => Pos::Union(self.clone_pos(left), self.clone_pos(right)),
        };
        self.target.alloc_pos(pos)
    }

    fn clone_neg(&mut self, id: NegId) -> NegId {
        let neg = match self.source.neg(id).clone() {
            Neg::Top => Neg::Top,
            Neg::Bot => Neg::Bot,
            Neg::Var(var) => Neg::Var(self.clone_var(var)),
            Neg::Con(path, args) => Neg::Con(
                path,
                args.into_iter().map(|arg| self.clone_neu(arg)).collect(),
            ),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neg::Fun {
                arg: self.clone_pos(arg),
                arg_eff: self.clone_pos(arg_eff),
                ret_eff: self.clone_neg(ret_eff),
                ret: self.clone_neg(ret),
            },
            Neg::Record(fields) => Neg::Record(self.clone_fields(&fields, Self::clone_neg)),
            Neg::PolyVariant(variants) => Neg::PolyVariant(
                variants
                    .into_iter()
                    .map(|(name, args)| {
                        (
                            name,
                            args.into_iter().map(|arg| self.clone_neg(arg)).collect(),
                        )
                    })
                    .collect(),
            ),
            Neg::Tuple(items) => {
                Neg::Tuple(items.into_iter().map(|item| self.clone_neg(item)).collect())
            }
            Neg::Row(items, tail) => Neg::Row(
                items.into_iter().map(|item| self.clone_neg(item)).collect(),
                self.clone_neg(tail),
            ),
            Neg::Intersection(left, right) => {
                Neg::Intersection(self.clone_neg(left), self.clone_neg(right))
            }
        };
        self.target.alloc_neg(neg)
    }

    fn clone_neu(&mut self, id: NeuId) -> NeuId {
        let neu = match self.source.neu(id).clone() {
            Neu::Bounds(lower, var, upper) => Neu::Bounds(
                self.clone_pos(lower),
                self.clone_var(var),
                self.clone_neg(upper),
            ),
            Neu::Con(path, args) => Neu::Con(
                path,
                args.into_iter().map(|arg| self.clone_neu(arg)).collect(),
            ),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neu::Fun {
                arg: self.clone_neu(arg),
                arg_eff: self.clone_neu(arg_eff),
                ret_eff: self.clone_neu(ret_eff),
                ret: self.clone_neu(ret),
            },
            Neu::Record(fields) => Neu::Record(self.clone_fields(&fields, Self::clone_neu)),
            Neu::PolyVariant(variants) => Neu::PolyVariant(
                variants
                    .into_iter()
                    .map(|(name, args)| {
                        (
                            name,
                            args.into_iter().map(|arg| self.clone_neu(arg)).collect(),
                        )
                    })
                    .collect(),
            ),
            Neu::Tuple(items) => {
                Neu::Tuple(items.into_iter().map(|item| self.clone_neu(item)).collect())
            }
        };
        self.target.alloc_neu(neu)
    }

    fn clone_scheme_subtract_facts(&mut self, scheme: &Scheme) {
        for (source_var, source_id) in &scheme.subtracts {
            let Some(subtractability) = self.source_subtractability(*source_var, *source_id) else {
                continue;
            };
            let target_var = self.clone_var(*source_var);
            let target_id = self.clone_subtract(*source_id);
            let subtractability = self.clone_subtractability(subtractability);
            self.target
                .subtract_fact(target_var, target_id, subtractability);
        }
    }

    fn source_subtractability(
        &self,
        source_var: TypeVar,
        source_id: SubtractId,
    ) -> Option<Subtractability> {
        self.target
            .constraints()
            .subtracts()
            .facts(source_var)
            .iter()
            .find(|fact| fact.id == source_id)
            .or_else(|| self.target.constraints().subtracts().fact_by_id(source_id))
            .map(|fact| fact.subtractability.clone())
    }

    fn clone_subtractability(&mut self, subtractability: Subtractability) -> Subtractability {
        match subtractability {
            Subtractability::Empty => Subtractability::Empty,
            Subtractability::All => Subtractability::All,
            Subtractability::AllExcept(names, types) => Subtractability::AllExcept(
                names,
                types.into_iter().map(|ty| self.clone_neu(ty)).collect(),
            ),
            Subtractability::Set(names, types) => Subtractability::Set(
                names,
                types.into_iter().map(|ty| self.clone_neu(ty)).collect(),
            ),
        }
    }

    fn clone_fields<T>(
        &mut self,
        fields: &[RecordField<T>],
        mut clone_value: impl FnMut(&mut Self, T) -> T,
    ) -> Vec<RecordField<T>>
    where
        T: Copy,
    {
        fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: clone_value(self, field.value),
                optional: field.optional,
            })
            .collect()
    }
}
