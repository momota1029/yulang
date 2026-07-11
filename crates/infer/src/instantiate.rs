//! Generalized scheme を use-site の infer arena へ展開する入口。
//!
//! `poly::Scheme` は final IR 側の `TypeArena` に載るため、量化済み def を参照する use-site では
//! predicate を infer arena へ fresh clone してから通常の subtype 制約として戻す。

use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RoleAssociatedType, RolePredicate,
    RolePredicateArg, Scheme, StackWeight, SubtractId, Subtractability, TypeArena, TypeVar,
};
use rustc_hash::FxHashMap;

use crate::arena::Arena as InferArena;
use crate::constraints::TypeLevel;
use crate::interface_oracle::ClosureScan;
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate,
};

/// Session-lifetime mapping for unit-owned variables imported from one or more compiled units.
///
/// Boundary bounds are installed once when the analysis session is created. Later Stage 3 slices
/// preload this same mapping into scheme instantiation and role-candidate freshening.
#[derive(Debug, Default)]
pub(crate) struct ImportedBoundarySubstitution {
    vars: FxHashMap<TypeVar, TypeVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SchemeInstantiationError {
    UnmappedFreeTypeVar { var: TypeVar },
    BoundaryBinderIsPerUse { var: TypeVar },
}

pub(crate) fn seed_imported_boundary(
    source: &TypeArena,
    target: &mut InferArena,
    boundary: &crate::CompiledBoundaryInterface,
) -> ImportedBoundarySubstitution {
    let mut vars = FxHashMap::default();
    for bound in &boundary.bounds {
        vars.entry(bound.var)
            .or_insert_with(|| target.fresh_type_var_at(TypeLevel::root()));
    }

    let mut instantiator =
        SchemeInstantiator::new_with_vars(source, target, TypeLevel::root(), vars);
    instantiator.clone_boundary_bounds(boundary);
    ImportedBoundarySubstitution {
        vars: instantiator.vars,
    }
}

impl ImportedBoundarySubstitution {
    #[cfg(test)]
    pub(crate) fn get(&self, source: TypeVar) -> Option<TypeVar> {
        self.vars.get(&source).copied()
    }
}

pub(crate) fn instantiate_scheme(
    source: &TypeArena,
    target: &mut InferArena,
    level: TypeLevel,
    scheme: &Scheme,
) -> PosId {
    let mut instantiator = SchemeInstantiator::new(source, target, level);
    instantiator.instantiate_scheme(scheme)
}

pub(crate) fn instantiate_scheme_with_roles(
    source: &TypeArena,
    target: &mut InferArena,
    level: TypeLevel,
    scheme: &Scheme,
) -> InstantiatedScheme {
    let mut instantiator = SchemeInstantiator::new(source, target, level);
    instantiator.instantiate_scheme_with_roles(scheme)
}

pub(crate) fn instantiate_validated_imported_scheme_with_roles(
    source: &TypeArena,
    target: &mut InferArena,
    level: TypeLevel,
    scheme: &Scheme,
    boundary: &ImportedBoundarySubstitution,
) -> InstantiatedScheme {
    let mut instantiator =
        SchemeInstantiator::new_with_preloaded_vars(source, target, level, &boundary.vars);
    instantiator.instantiate_scheme_with_roles(scheme)
}

pub(crate) fn validate_imported_scheme_for_instantiation(
    source: &TypeArena,
    scheme: &Scheme,
    boundary: &ImportedBoundarySubstitution,
) -> Result<(), SchemeInstantiationError> {
    validate_imported_scheme_vars(source, scheme, boundary)
}

pub(crate) fn freshen_role_impl_candidate(
    source: &TypeArena,
    target: &mut InferArena,
    candidate: &RoleImplCandidate,
    boundary: &ImportedBoundarySubstitution,
) -> RoleImplCandidate {
    let mut instantiator = SchemeInstantiator::new_freshening_all_with_preloaded_vars(
        source,
        target,
        TypeLevel::root(),
        &boundary.vars,
    );
    instantiator.clone_role_impl_candidate(candidate)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstantiatedScheme {
    pub(crate) predicate: PosId,
    pub(crate) role_predicates: Vec<RolePredicate>,
}

struct SchemeInstantiator<'a> {
    source: &'a TypeArena,
    target: &'a mut InferArena,
    level: TypeLevel,
    vars: FxHashMap<TypeVar, TypeVar>,
    preloaded_vars: Option<&'a FxHashMap<TypeVar, TypeVar>>,
    subtracts: FxHashMap<SubtractId, SubtractId>,
    pos_nodes: FxHashMap<PosId, PosId>,
    neg_nodes: FxHashMap<NegId, NegId>,
    neu_nodes: FxHashMap<NeuId, NeuId>,
    freshen_unmapped: bool,
}

impl<'a> SchemeInstantiator<'a> {
    fn new(source: &'a TypeArena, target: &'a mut InferArena, level: TypeLevel) -> Self {
        Self {
            source,
            target,
            level,
            vars: FxHashMap::default(),
            preloaded_vars: None,
            subtracts: FxHashMap::default(),
            pos_nodes: FxHashMap::default(),
            neg_nodes: FxHashMap::default(),
            neu_nodes: FxHashMap::default(),
            freshen_unmapped: false,
        }
    }

    fn new_freshening_all_with_preloaded_vars(
        source: &'a TypeArena,
        target: &'a mut InferArena,
        level: TypeLevel,
        preloaded_vars: &'a FxHashMap<TypeVar, TypeVar>,
    ) -> Self {
        Self {
            source,
            target,
            level,
            vars: FxHashMap::default(),
            preloaded_vars: Some(preloaded_vars),
            subtracts: FxHashMap::default(),
            pos_nodes: FxHashMap::default(),
            neg_nodes: FxHashMap::default(),
            neu_nodes: FxHashMap::default(),
            freshen_unmapped: true,
        }
    }

    fn new_with_vars(
        source: &'a TypeArena,
        target: &'a mut InferArena,
        level: TypeLevel,
        vars: FxHashMap<TypeVar, TypeVar>,
    ) -> Self {
        Self {
            source,
            target,
            level,
            vars,
            preloaded_vars: None,
            subtracts: FxHashMap::default(),
            pos_nodes: FxHashMap::default(),
            neg_nodes: FxHashMap::default(),
            neu_nodes: FxHashMap::default(),
            freshen_unmapped: false,
        }
    }

    fn new_with_preloaded_vars(
        source: &'a TypeArena,
        target: &'a mut InferArena,
        level: TypeLevel,
        preloaded_vars: &'a FxHashMap<TypeVar, TypeVar>,
    ) -> Self {
        Self {
            source,
            target,
            level,
            vars: FxHashMap::default(),
            preloaded_vars: Some(preloaded_vars),
            subtracts: FxHashMap::default(),
            pos_nodes: FxHashMap::default(),
            neg_nodes: FxHashMap::default(),
            neu_nodes: FxHashMap::default(),
            freshen_unmapped: false,
        }
    }

    fn instantiate_scheme(&mut self, scheme: &Scheme) -> PosId {
        self.instantiate_scheme_with_roles(scheme).predicate
    }

    fn instantiate_scheme_with_roles(&mut self, scheme: &Scheme) -> InstantiatedScheme {
        for var in &scheme.quantifiers {
            self.fresh_var(*var);
        }
        for bound in &scheme.recursive_bounds {
            self.fresh_var(bound.var);
        }
        for id in &scheme.stack_quantifiers {
            self.fresh_subtract(*id);
        }
        self.clone_recursive_bounds(scheme);
        let predicate = self.clone_pos(scheme.predicate);
        let predicate = self.wrap_predicate_with_stack_pops(predicate, &scheme.stack_quantifiers);
        let role_predicates = scheme
            .role_predicates
            .iter()
            .map(|predicate| self.clone_role_predicate(predicate))
            .collect();
        InstantiatedScheme {
            predicate,
            role_predicates,
        }
    }

    fn clone_role_predicate(&mut self, predicate: &RolePredicate) -> RolePredicate {
        RolePredicate {
            role: predicate.role.clone(),
            inputs: predicate
                .inputs
                .iter()
                .map(|input| self.clone_role_predicate_arg(*input))
                .collect(),
            associated: predicate
                .associated
                .iter()
                .map(|associated| RoleAssociatedType {
                    name: associated.name.clone(),
                    value: self.clone_neu(associated.value),
                })
                .collect(),
        }
    }

    fn clone_role_predicate_arg(&mut self, arg: RolePredicateArg) -> RolePredicateArg {
        match arg {
            RolePredicateArg::Covariant(pos) => RolePredicateArg::Covariant(self.clone_pos(pos)),
            RolePredicateArg::Contravariant(neg) => {
                RolePredicateArg::Contravariant(self.clone_neg(neg))
            }
            RolePredicateArg::Invariant(neu) => RolePredicateArg::Invariant(self.clone_neu(neu)),
        }
    }

    fn clone_role_impl_candidate(&mut self, candidate: &RoleImplCandidate) -> RoleImplCandidate {
        RoleImplCandidate {
            impl_def: candidate.impl_def,
            role: candidate.role.clone(),
            inputs: candidate
                .inputs
                .iter()
                .map(|arg| self.clone_role_constraint_arg(*arg))
                .collect(),
            associated: candidate
                .associated
                .iter()
                .map(|associated| RoleAssociatedConstraint {
                    name: associated.name.clone(),
                    value: self.clone_role_constraint_arg(associated.value),
                })
                .collect(),
            prerequisites: candidate
                .prerequisites
                .iter()
                .map(|constraint| self.clone_role_constraint(constraint))
                .collect(),
            methods: candidate.methods.clone(),
        }
    }

    fn clone_role_constraint(&mut self, constraint: &RoleConstraint) -> RoleConstraint {
        RoleConstraint {
            role: constraint.role.clone(),
            inputs: constraint
                .inputs
                .iter()
                .map(|arg| self.clone_role_constraint_arg(*arg))
                .collect(),
            associated: constraint
                .associated
                .iter()
                .map(|associated| RoleAssociatedConstraint {
                    name: associated.name.clone(),
                    value: self.clone_role_constraint_arg(associated.value),
                })
                .collect(),
        }
    }

    fn clone_role_constraint_arg(&mut self, arg: RoleConstraintArg) -> RoleConstraintArg {
        RoleConstraintArg {
            lower: self.clone_pos(arg.lower),
            upper: self.clone_neg(arg.upper),
        }
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

    fn clone_var(&mut self, source: TypeVar) -> TypeVar {
        if let Some(target) = self.vars.get(&source).copied().or_else(|| {
            self.preloaded_vars
                .and_then(|vars| vars.get(&source).copied())
        }) {
            return target;
        }
        if self.freshen_unmapped {
            return self.fresh_var(source);
        }
        source
    }

    fn clone_subtract(&mut self, source: SubtractId) -> SubtractId {
        if self.freshen_unmapped {
            return self.fresh_subtract(source);
        }
        self.subtracts.get(&source).copied().unwrap_or(source)
    }

    fn wrap_predicate_with_stack_pops(
        &mut self,
        predicate: PosId,
        stack_quantifiers: &[SubtractId],
    ) -> PosId {
        if stack_quantifiers.is_empty() {
            return predicate;
        }
        let mut weight = StackWeight::empty();
        for id in stack_quantifiers {
            weight = weight.compose(&StackWeight::pops(self.clone_subtract(*id), u32::MAX));
        }
        self.target.alloc_pos(Pos::Stack {
            inner: predicate,
            weight,
        })
    }

    fn clone_pos(&mut self, id: PosId) -> PosId {
        if let Some(cloned) = self.pos_nodes.get(&id).copied() {
            return cloned;
        }
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
            Pos::NonSubtract(pos, weight) => {
                Pos::NonSubtract(self.clone_pos(pos), self.clone_stack_weight(weight))
            }
            Pos::Stack { inner, weight } => Pos::Stack {
                inner: self.clone_pos(inner),
                weight: self.clone_stack_weight(weight),
            },
            Pos::Union(left, right) => Pos::Union(self.clone_pos(left), self.clone_pos(right)),
        };
        let cloned = self.target.alloc_pos(pos);
        self.pos_nodes.insert(id, cloned);
        cloned
    }

    fn clone_neg(&mut self, id: NegId) -> NegId {
        if let Some(cloned) = self.neg_nodes.get(&id).copied() {
            return cloned;
        }
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
            Neg::Stack { inner, weight } => Neg::Stack {
                inner: self.clone_neg(inner),
                weight: self.clone_stack_weight(weight),
            },
            Neg::Intersection(left, right) => {
                Neg::Intersection(self.clone_neg(left), self.clone_neg(right))
            }
        };
        let cloned = self.target.alloc_neg(neg);
        self.neg_nodes.insert(id, cloned);
        cloned
    }

    fn clone_neu(&mut self, id: NeuId) -> NeuId {
        if let Some(cloned) = self.neu_nodes.get(&id).copied() {
            return cloned;
        }
        let neu = match self.source.neu(id).clone() {
            Neu::Bounds(lower, upper) => Neu::Bounds(self.clone_pos(lower), self.clone_neg(upper)),
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
        let cloned = self.target.alloc_neu(neu);
        self.neu_nodes.insert(id, cloned);
        cloned
    }

    fn clone_subtractability(&mut self, subtractability: Subtractability) -> Subtractability {
        match subtractability {
            Subtractability::Empty => Subtractability::Empty,
            Subtractability::All => Subtractability::All,
            Subtractability::AllExcept(names, types) => Subtractability::AllExcept(
                names,
                types.into_iter().map(|ty| self.clone_neu(ty)).collect(),
            ),
            Subtractability::AllExceptMany(families) => Subtractability::AllExceptMany(
                families
                    .into_iter()
                    .map(|(names, types)| {
                        (
                            names,
                            types.into_iter().map(|ty| self.clone_neu(ty)).collect(),
                        )
                    })
                    .collect(),
            ),
            Subtractability::Set(names, types) => Subtractability::Set(
                names,
                types.into_iter().map(|ty| self.clone_neu(ty)).collect(),
            ),
            Subtractability::SetMany(families) => Subtractability::SetMany(
                families
                    .into_iter()
                    .map(|(names, types)| {
                        (
                            names,
                            types.into_iter().map(|ty| self.clone_neu(ty)).collect(),
                        )
                    })
                    .collect(),
            ),
        }
    }

    fn clone_stack_weight(&mut self, weight: StackWeight) -> StackWeight {
        let mut out = StackWeight::filter(self.clone_subtractability(weight.filter_set().clone()));
        for entry in weight.entries() {
            let id = self.clone_subtract(entry.id);
            for subtractability in &entry.floor {
                let cloned = self.clone_subtractability(subtractability.clone());
                out = out.compose(&StackWeight::floor(id, cloned));
            }
            out = out.compose(&StackWeight::pops(id, entry.pops));
            for subtractability in &entry.stack {
                out = out.compose(&StackWeight::push(
                    id,
                    self.clone_subtractability(subtractability.clone()),
                ));
            }
        }
        out
    }

    fn clone_recursive_bounds(&mut self, scheme: &Scheme) {
        let mut constraints = Vec::with_capacity(scheme.recursive_bounds.len() * 2);
        for bound in &scheme.recursive_bounds {
            let target_var = self.clone_var(bound.var);
            let target_bounds = self.clone_neu(bound.bounds);
            let (lower, upper) = self.project_recursive_neu_bounds(target_bounds);
            let target_neg = self.target.alloc_neg(Neg::Var(target_var));
            constraints.push((lower, target_neg));
            let target_pos = self.target.alloc_pos(Pos::Var(target_var));
            constraints.push((target_pos, upper));
        }
        if !constraints.is_empty() {
            self.target.subtypes(constraints);
        }
    }

    fn clone_boundary_bounds(&mut self, boundary: &crate::CompiledBoundaryInterface) {
        let mut constraints = Vec::with_capacity(boundary.bounds.len() * 2);
        for bound in &boundary.bounds {
            let target_var = self.clone_var(bound.var);
            let target_bounds = self.clone_neu(bound.bounds);
            let (lower, upper) = self.project_recursive_neu_bounds(target_bounds);
            let target_neg = self.target.alloc_neg(Neg::Var(target_var));
            constraints.push((lower, target_neg));
            let target_pos = self.target.alloc_pos(Pos::Var(target_var));
            constraints.push((target_pos, upper));
        }
        if !constraints.is_empty() {
            self.target.subtypes(constraints);
        }
    }

    fn project_recursive_neu_bounds(&mut self, id: NeuId) -> (PosId, NegId) {
        match self.target.constraints().types().neu(id).clone() {
            Neu::Bounds(lower, upper) => (lower, upper),
            _ => self.project_neu_bounds(id),
        }
    }

    fn project_neu_bounds(&mut self, id: NeuId) -> (PosId, NegId) {
        match self.target.constraints().types().neu(id).clone() {
            Neu::Bounds(lower, upper) => (lower, upper),
            Neu::Con(path, args) => (
                self.target.alloc_pos(Pos::Con(path.clone(), args.clone())),
                self.target.alloc_neg(Neg::Con(path, args)),
            ),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let (arg_pos, arg_neg) = self.project_neu_bounds(arg);
                let (arg_eff_pos, arg_eff_neg) = self.project_neu_bounds(arg_eff);
                let (ret_eff_pos, ret_eff_neg) = self.project_neu_bounds(ret_eff);
                let (ret_pos, ret_neg) = self.project_neu_bounds(ret);
                (
                    self.target.alloc_pos(Pos::Fun {
                        arg: arg_neg,
                        arg_eff: arg_eff_neg,
                        ret_eff: ret_eff_pos,
                        ret: ret_pos,
                    }),
                    self.target.alloc_neg(Neg::Fun {
                        arg: arg_pos,
                        arg_eff: arg_eff_pos,
                        ret_eff: ret_eff_neg,
                        ret: ret_neg,
                    }),
                )
            }
            Neu::Record(fields) => {
                let mut pos = Vec::with_capacity(fields.len());
                let mut neg = Vec::with_capacity(fields.len());
                for field in fields {
                    let (lower, upper) = self.project_neu_bounds(field.value);
                    pos.push(RecordField {
                        name: field.name.clone(),
                        value: lower,
                        optional: field.optional,
                    });
                    neg.push(RecordField {
                        name: field.name,
                        value: upper,
                        optional: field.optional,
                    });
                }
                (
                    self.target.alloc_pos(Pos::Record(pos)),
                    self.target.alloc_neg(Neg::Record(neg)),
                )
            }
            Neu::PolyVariant(items) => {
                let mut pos = Vec::with_capacity(items.len());
                let mut neg = Vec::with_capacity(items.len());
                for (name, payloads) in items {
                    let mut pos_payloads = Vec::with_capacity(payloads.len());
                    let mut neg_payloads = Vec::with_capacity(payloads.len());
                    for payload in payloads {
                        let (lower, upper) = self.project_neu_bounds(payload);
                        pos_payloads.push(lower);
                        neg_payloads.push(upper);
                    }
                    pos.push((name.clone(), pos_payloads));
                    neg.push((name, neg_payloads));
                }
                (
                    self.target.alloc_pos(Pos::PolyVariant(pos)),
                    self.target.alloc_neg(Neg::PolyVariant(neg)),
                )
            }
            Neu::Tuple(items) => {
                let mut pos = Vec::with_capacity(items.len());
                let mut neg = Vec::with_capacity(items.len());
                for item in items {
                    let (lower, upper) = self.project_neu_bounds(item);
                    pos.push(lower);
                    neg.push(upper);
                }
                (
                    self.target.alloc_pos(Pos::Tuple(pos)),
                    self.target.alloc_neg(Neg::Tuple(neg)),
                )
            }
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

fn validate_imported_scheme_vars(
    source: &TypeArena,
    scheme: &Scheme,
    boundary: &ImportedBoundarySubstitution,
) -> Result<(), SchemeInstantiationError> {
    let mut per_use = scheme
        .quantifiers
        .iter()
        .copied()
        .collect::<rustc_hash::FxHashSet<_>>();
    per_use.extend(scheme.recursive_bounds.iter().map(|bound| bound.var));
    if let Some(var) = per_use
        .iter()
        .copied()
        .filter(|var| boundary.vars.contains_key(var))
        .min_by_key(|var| var.0)
    {
        return Err(SchemeInstantiationError::BoundaryBinderIsPerUse { var });
    }

    let mut scan = ClosureScan::new(source);
    scan.pos(scheme.predicate);
    for predicate in &scheme.role_predicates {
        scan.scheme_role_predicate(predicate);
    }
    for bound in &scheme.recursive_bounds {
        scan.vars.insert(bound.var);
        scan.neu(bound.bounds);
    }
    if let Some(var) = scan
        .vars
        .into_iter()
        .filter(|var| !per_use.contains(var) && !boundary.vars.contains_key(var))
        .min_by_key(|var| var.0)
    {
        return Err(SchemeInstantiationError::UnmappedFreeTypeVar { var });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instantiate_freshens_stack_quantifier_and_adds_root_pop() {
        let mut source = TypeArena::new();
        let source_var = TypeVar(42);
        let source_stack = SubtractId(7);
        let inner = source.alloc_pos(Pos::Var(source_var));
        let predicate = source.alloc_pos(Pos::Stack {
            inner,
            weight: StackWeight::push(source_stack, Subtractability::Empty),
        });
        let scheme = Scheme {
            quantifiers: vec![source_var],
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: vec![source_stack],
            predicate,
        };
        let mut target = InferArena::new();

        let instantiated = instantiate_scheme(&source, &mut target, TypeLevel::root(), &scheme);

        let Pos::Stack {
            inner: cloned_predicate,
            weight: root_weight,
        } = target.constraints().types().pos(instantiated)
        else {
            panic!("instantiated predicate should receive root stack pop");
        };
        let root_entry = root_weight.entries().first().expect("root pop entry");
        assert_ne!(root_entry.id, source_stack);
        assert_eq!(root_entry.pops, u32::MAX);
        assert!(root_entry.stack.is_empty());

        let Pos::Stack {
            inner: cloned_inner,
            weight: inner_weight,
        } = target.constraints().types().pos(*cloned_predicate)
        else {
            panic!("scheme stack wrapper should be cloned");
        };
        let inner_entry = inner_weight.entries().first().expect("inner stack entry");
        assert_eq!(inner_entry.id, root_entry.id);
        assert_eq!(inner_entry.pops, 0);
        assert_eq!(inner_entry.stack, vec![Subtractability::Empty]);

        let Pos::Var(fresh_var) = target.constraints().types().pos(*cloned_inner) else {
            panic!("scheme variable should be cloned");
        };
        assert_ne!(*fresh_var, source_var);
    }
}
