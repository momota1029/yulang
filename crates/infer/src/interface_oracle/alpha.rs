use std::collections::{HashMap, HashSet};

use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicate, RolePredicateArg, Scheme,
    StackWeight, SubtractId, Subtractability, TypeArena, TypeVar,
};

use super::{
    BoundaryBound, BoundaryInterface, ClosureScan, InterfaceViolation, scan_scheme_closure,
};

/// Structural scheme view with disjoint per-use, boundary, and stack binders.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemeAlphaView {
    pub predicate: AlphaPos,
    pub role_predicates: Vec<AlphaRolePredicate>,
    pub recursive_bounds: Vec<AlphaRecursiveBound>,
    pub boundary_bounds: Vec<AlphaBoundaryBound>,
    pub per_use_binder_count: usize,
    pub boundary_binder_count: usize,
    pub stack_binder_count: usize,
    pub unbound_binder_count: usize,
    pub unbound_stack_binder_count: usize,
}

impl SchemeAlphaView {
    /// Validate closure, then discard every arena-local/raw binder number.
    pub fn from_scheme(
        arena: &TypeArena,
        scheme: &Scheme,
        boundary: BoundaryInterface<'_>,
    ) -> Result<Self, Vec<InterfaceViolation>> {
        scan_scheme_closure(arena, scheme, boundary)?;
        Ok(Self::build(
            arena,
            scheme,
            boundary,
            HashSet::new(),
            HashSet::new(),
        ))
    }

    /// Preserve current malformed free binders in a separate namespace.
    ///
    /// This is a characterization-only escape hatch.  Callers must inspect the
    /// returned violations; it never reclassifies a free variable as `B`.
    pub fn characterize_current_scheme(
        arena: &TypeArena,
        scheme: &Scheme,
        boundary: BoundaryInterface<'_>,
    ) -> SchemeAlphaCharacterization {
        let violations = scan_scheme_closure(arena, scheme, boundary)
            .err()
            .unwrap_or_default();
        let per_use = per_use_binders(scheme);
        let boundary_binders = boundary.binders.iter().copied().collect::<HashSet<_>>();
        let stack_binders = scheme
            .stack_quantifiers
            .iter()
            .copied()
            .collect::<HashSet<_>>();
        let mut reachable = ClosureScan::new(arena);
        reachable.pos(scheme.predicate);
        for predicate in &scheme.role_predicates {
            reachable.scheme_role_predicate(predicate);
        }
        for bound in &scheme.recursive_bounds {
            reachable.vars.insert(bound.var);
            reachable.neu(bound.bounds);
        }
        let unbound = reachable
            .vars
            .difference(&per_use)
            .copied()
            .filter(|var| !boundary_binders.contains(var))
            .collect();
        let unbound_stack = reachable
            .subtracts
            .difference(&stack_binders)
            .copied()
            .collect();
        SchemeAlphaCharacterization {
            view: Self::build(arena, scheme, boundary, unbound, unbound_stack),
            violations,
        }
    }

    fn build(
        arena: &TypeArena,
        scheme: &Scheme,
        boundary: BoundaryInterface<'_>,
        unbound: HashSet<TypeVar>,
        unbound_stack: HashSet<SubtractId>,
    ) -> Self {
        let per_use = per_use_binders(scheme);
        let boundary_binders = boundary.binders.iter().copied().collect::<HashSet<_>>();
        let stack_binders = scheme
            .stack_quantifiers
            .iter()
            .copied()
            .collect::<HashSet<_>>();
        let mut builder = AlphaBuilder::new(
            arena,
            per_use.clone(),
            boundary_binders.clone(),
            stack_binders.clone(),
            unbound.clone(),
            unbound_stack.clone(),
        );

        // Ordered scheme structure owns first occurrence.  Unordered side
        // collections receive an alpha-invariant local key before traversal.
        let predicate = builder.pos(scheme.predicate);

        let mut role_predicates = scheme.role_predicates.iter().collect::<Vec<_>>();
        role_predicates.sort_by_key(|predicate| {
            standalone_role_key(
                arena,
                predicate,
                &per_use,
                &boundary_binders,
                &stack_binders,
                &unbound,
                &unbound_stack,
            )
        });
        let role_predicates = role_predicates
            .into_iter()
            .map(|predicate| builder.role_predicate(predicate))
            .collect();

        let mut recursive_bounds = scheme.recursive_bounds.iter().collect::<Vec<_>>();
        recursive_bounds.sort_by_key(|bound| {
            standalone_recursive_key(
                arena,
                bound.var,
                bound.bounds,
                &per_use,
                &boundary_binders,
                &stack_binders,
                &unbound,
                &unbound_stack,
            )
        });
        let recursive_bounds = recursive_bounds
            .into_iter()
            .map(|bound| AlphaRecursiveBound {
                binder: builder.binder(bound.var),
                bounds: builder.neu(bound.bounds),
            })
            .collect();

        let mut boundary_bounds = boundary.bounds.iter().collect::<Vec<_>>();
        boundary_bounds.sort_by_key(|bound| {
            standalone_boundary_key(
                arena,
                bound,
                &per_use,
                &boundary_binders,
                &stack_binders,
                &unbound,
                &unbound_stack,
            )
        });
        let boundary_bounds = boundary_bounds
            .into_iter()
            .map(|bound| AlphaBoundaryBound {
                binder: builder.binder(bound.var),
                lower: builder.pos(bound.lower),
                upper: builder.neg(bound.upper),
            })
            .collect();

        Self {
            predicate,
            role_predicates,
            recursive_bounds,
            boundary_bounds,
            per_use_binder_count: per_use.len(),
            boundary_binder_count: boundary_binders.len(),
            stack_binder_count: stack_binders.len(),
            unbound_binder_count: unbound.len(),
            unbound_stack_binder_count: unbound_stack.len(),
        }
    }

    /// Small diagnostic for characterization tests; equality remains the full view equality.
    pub fn first_difference(&self, other: &Self) -> Option<SchemeAlphaDifference> {
        if self.predicate != other.predicate {
            return Some(alpha_difference(
                "predicate",
                &self.predicate,
                &other.predicate,
            ));
        }
        if self.role_predicates.len() != other.role_predicates.len() {
            return Some(SchemeAlphaDifference {
                path: "role_predicates.len".into(),
                left: self.role_predicates.len().to_string(),
                right: other.role_predicates.len().to_string(),
            });
        }
        for (index, (left, right)) in self
            .role_predicates
            .iter()
            .zip(&other.role_predicates)
            .enumerate()
        {
            if left != right {
                return Some(alpha_difference(
                    format!("role_predicates[{index}]"),
                    left,
                    right,
                ));
            }
        }
        if self.recursive_bounds.len() != other.recursive_bounds.len() {
            return Some(SchemeAlphaDifference {
                path: "recursive_bounds.len".into(),
                left: self.recursive_bounds.len().to_string(),
                right: other.recursive_bounds.len().to_string(),
            });
        }
        for (index, (left, right)) in self
            .recursive_bounds
            .iter()
            .zip(&other.recursive_bounds)
            .enumerate()
        {
            if left != right {
                return Some(alpha_difference(
                    format!("recursive_bounds[{index}]"),
                    left,
                    right,
                ));
            }
        }
        if self.boundary_bounds != other.boundary_bounds {
            return Some(alpha_difference(
                "boundary_bounds",
                &self.boundary_bounds,
                &other.boundary_bounds,
            ));
        }
        if self.per_use_binder_count != other.per_use_binder_count {
            return Some(count_difference(
                "per_use_binder_count",
                self.per_use_binder_count,
                other.per_use_binder_count,
            ));
        }
        if self.boundary_binder_count != other.boundary_binder_count {
            return Some(count_difference(
                "boundary_binder_count",
                self.boundary_binder_count,
                other.boundary_binder_count,
            ));
        }
        if self.stack_binder_count != other.stack_binder_count {
            return Some(count_difference(
                "stack_binder_count",
                self.stack_binder_count,
                other.stack_binder_count,
            ));
        }
        if self.unbound_binder_count != other.unbound_binder_count {
            return Some(count_difference(
                "unbound_binder_count",
                self.unbound_binder_count,
                other.unbound_binder_count,
            ));
        }
        if self.unbound_stack_binder_count != other.unbound_stack_binder_count {
            return Some(count_difference(
                "unbound_stack_binder_count",
                self.unbound_stack_binder_count,
                other.unbound_stack_binder_count,
            ));
        }
        None
    }

    pub fn summary(&self) -> SchemeAlphaSummary {
        SchemeAlphaSummary {
            per_use_binders: self.per_use_binder_count,
            boundary_binders: self.boundary_binder_count,
            stack_binders: self.stack_binder_count,
            role_predicates: self.role_predicates.len(),
            recursive_bounds: self.recursive_bounds.len(),
            boundary_bounds: self.boundary_bounds.len(),
            unbound_binders: self.unbound_binder_count,
            unbound_stack_binders: self.unbound_stack_binder_count,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemeAlphaDifference {
    pub path: String,
    pub left: String,
    pub right: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemeAlphaCharacterization {
    pub view: SchemeAlphaView,
    pub violations: Vec<InterfaceViolation>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchemeAlphaSummary {
    pub per_use_binders: usize,
    pub boundary_binders: usize,
    pub stack_binders: usize,
    pub role_predicates: usize,
    pub recursive_bounds: usize,
    pub boundary_bounds: usize,
    pub unbound_binders: usize,
    pub unbound_stack_binders: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AlphaTypeBinder {
    PerUse(u32),
    Boundary(u32),
    Unbound(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AlphaStackBinder {
    Bound(u32),
    Unbound(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AlphaPos {
    Bot,
    Var(AlphaTypeBinder),
    Con(Vec<String>, Vec<AlphaNeu>),
    Fun {
        arg: Box<AlphaNeg>,
        arg_eff: Box<AlphaNeg>,
        ret_eff: Box<AlphaPos>,
        ret: Box<AlphaPos>,
    },
    Record(Vec<AlphaField<AlphaPos>>),
    RecordTailSpread {
        fields: Vec<AlphaField<AlphaPos>>,
        tail: Box<AlphaPos>,
    },
    RecordHeadSpread {
        tail: Box<AlphaPos>,
        fields: Vec<AlphaField<AlphaPos>>,
    },
    PolyVariant(Vec<(String, Vec<AlphaPos>)>),
    Tuple(Vec<AlphaPos>),
    Row(Vec<AlphaPos>),
    Stack {
        inner: Box<AlphaPos>,
        weight: AlphaStackWeight,
    },
    NonSubtract(Box<AlphaPos>, AlphaStackWeight),
    Union(Box<AlphaPos>, Box<AlphaPos>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AlphaNeg {
    Top,
    Bot,
    Var(AlphaTypeBinder),
    Con(Vec<String>, Vec<AlphaNeu>),
    Fun {
        arg: Box<AlphaPos>,
        arg_eff: Box<AlphaPos>,
        ret_eff: Box<AlphaNeg>,
        ret: Box<AlphaNeg>,
    },
    Record(Vec<AlphaField<AlphaNeg>>),
    PolyVariant(Vec<(String, Vec<AlphaNeg>)>),
    Tuple(Vec<AlphaNeg>),
    Row(Vec<AlphaNeg>, Box<AlphaNeg>),
    Stack {
        inner: Box<AlphaNeg>,
        weight: AlphaStackWeight,
    },
    Intersection(Box<AlphaNeg>, Box<AlphaNeg>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AlphaNeu {
    Bounds(Box<AlphaPos>, Box<AlphaNeg>),
    Con(Vec<String>, Vec<AlphaNeu>),
    Fun {
        arg: Box<AlphaNeu>,
        arg_eff: Box<AlphaNeu>,
        ret_eff: Box<AlphaNeu>,
        ret: Box<AlphaNeu>,
    },
    Record(Vec<AlphaField<AlphaNeu>>),
    PolyVariant(Vec<(String, Vec<AlphaNeu>)>),
    Tuple(Vec<AlphaNeu>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaField<T> {
    pub name: String,
    pub value: T,
    pub optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaRolePredicate {
    pub role: Vec<String>,
    pub inputs: Vec<AlphaRolePredicateArg>,
    pub associated: Vec<AlphaAssociatedType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AlphaRolePredicateArg {
    Covariant(AlphaPos),
    Contravariant(AlphaNeg),
    Invariant(AlphaNeu),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaAssociatedType {
    pub name: String,
    pub value: AlphaNeu,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaRecursiveBound {
    pub binder: AlphaTypeBinder,
    pub bounds: AlphaNeu,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaBoundaryBound {
    pub binder: AlphaTypeBinder,
    pub lower: AlphaPos,
    pub upper: AlphaNeg,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaStackWeight {
    pub filter: AlphaSubtractability,
    pub entries: Vec<AlphaStackWeightEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaStackWeightEntry {
    pub binder: AlphaStackBinder,
    pub pops: u32,
    pub floor: Vec<AlphaSubtractability>,
    pub stack: Vec<AlphaSubtractability>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AlphaSubtractability {
    Empty,
    All,
    AllExcept(Vec<String>, Vec<AlphaNeu>),
    AllExceptMany(Vec<(Vec<String>, Vec<AlphaNeu>)>),
    Set(Vec<String>, Vec<AlphaNeu>),
    SetMany(Vec<(Vec<String>, Vec<AlphaNeu>)>),
}

struct AlphaBuilder<'a> {
    arena: &'a TypeArena,
    per_use: HashSet<TypeVar>,
    boundary: HashSet<TypeVar>,
    stack: HashSet<SubtractId>,
    unbound: HashSet<TypeVar>,
    unbound_stack: HashSet<SubtractId>,
    per_use_map: HashMap<TypeVar, u32>,
    boundary_map: HashMap<TypeVar, u32>,
    stack_map: HashMap<SubtractId, u32>,
    unbound_map: HashMap<TypeVar, u32>,
    unbound_stack_map: HashMap<SubtractId, u32>,
    pos_nodes: HashMap<PosId, AlphaPos>,
    neg_nodes: HashMap<NegId, AlphaNeg>,
    neu_nodes: HashMap<NeuId, AlphaNeu>,
}

impl<'a> AlphaBuilder<'a> {
    fn new(
        arena: &'a TypeArena,
        per_use: HashSet<TypeVar>,
        boundary: HashSet<TypeVar>,
        stack: HashSet<SubtractId>,
        unbound: HashSet<TypeVar>,
        unbound_stack: HashSet<SubtractId>,
    ) -> Self {
        Self {
            arena,
            per_use,
            boundary,
            stack,
            unbound,
            unbound_stack,
            per_use_map: HashMap::new(),
            boundary_map: HashMap::new(),
            stack_map: HashMap::new(),
            unbound_map: HashMap::new(),
            unbound_stack_map: HashMap::new(),
            pos_nodes: HashMap::new(),
            neg_nodes: HashMap::new(),
            neu_nodes: HashMap::new(),
        }
    }

    fn binder(&mut self, var: TypeVar) -> AlphaTypeBinder {
        if self.per_use.contains(&var) {
            let next = self.per_use_map.len() as u32;
            return AlphaTypeBinder::PerUse(*self.per_use_map.entry(var).or_insert(next));
        }
        if self.boundary.contains(&var) {
            let next = self.boundary_map.len() as u32;
            return AlphaTypeBinder::Boundary(*self.boundary_map.entry(var).or_insert(next));
        }
        debug_assert!(self.unbound.contains(&var));
        let next = self.unbound_map.len() as u32;
        AlphaTypeBinder::Unbound(*self.unbound_map.entry(var).or_insert(next))
    }

    fn stack_binder(&mut self, id: SubtractId) -> AlphaStackBinder {
        if self.stack.contains(&id) {
            let next = self.stack_map.len() as u32;
            return AlphaStackBinder::Bound(*self.stack_map.entry(id).or_insert(next));
        }
        debug_assert!(self.unbound_stack.contains(&id));
        let next = self.unbound_stack_map.len() as u32;
        AlphaStackBinder::Unbound(*self.unbound_stack_map.entry(id).or_insert(next))
    }

    fn pos(&mut self, id: PosId) -> AlphaPos {
        if let Some(pos) = self.pos_nodes.get(&id) {
            return pos.clone();
        }
        let pos = match self.arena.pos(id) {
            Pos::Bot => AlphaPos::Bot,
            Pos::Var(var) => AlphaPos::Var(self.binder(*var)),
            Pos::Con(path, args) => AlphaPos::Con(path.clone(), self.neu_slice(args)),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => AlphaPos::Fun {
                arg: Box::new(self.neg(*arg)),
                arg_eff: Box::new(self.neg(*arg_eff)),
                ret_eff: Box::new(self.pos(*ret_eff)),
                ret: Box::new(self.pos(*ret)),
            },
            Pos::Record(fields) => AlphaPos::Record(self.pos_fields(fields)),
            Pos::RecordTailSpread { fields, tail } => AlphaPos::RecordTailSpread {
                fields: self.pos_fields(fields),
                tail: Box::new(self.pos(*tail)),
            },
            Pos::RecordHeadSpread { tail, fields } => AlphaPos::RecordHeadSpread {
                tail: Box::new(self.pos(*tail)),
                fields: self.pos_fields(fields),
            },
            Pos::PolyVariant(variants) => AlphaPos::PolyVariant(
                variants
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads.iter().map(|payload| self.pos(*payload)).collect(),
                        )
                    })
                    .collect(),
            ),
            Pos::Tuple(items) => {
                AlphaPos::Tuple(items.iter().map(|item| self.pos(*item)).collect())
            }
            Pos::Row(items) => AlphaPos::Row(items.iter().map(|item| self.pos(*item)).collect()),
            Pos::Stack { inner, weight } => AlphaPos::Stack {
                inner: Box::new(self.pos(*inner)),
                weight: self.weight(weight),
            },
            Pos::NonSubtract(inner, weight) => {
                AlphaPos::NonSubtract(Box::new(self.pos(*inner)), self.weight(weight))
            }
            Pos::Union(left, right) => {
                AlphaPos::Union(Box::new(self.pos(*left)), Box::new(self.pos(*right)))
            }
        };
        self.pos_nodes.insert(id, pos.clone());
        pos
    }

    fn neg(&mut self, id: NegId) -> AlphaNeg {
        if let Some(neg) = self.neg_nodes.get(&id) {
            return neg.clone();
        }
        let neg = match self.arena.neg(id) {
            Neg::Top => AlphaNeg::Top,
            Neg::Bot => AlphaNeg::Bot,
            Neg::Var(var) => AlphaNeg::Var(self.binder(*var)),
            Neg::Con(path, args) => AlphaNeg::Con(path.clone(), self.neu_slice(args)),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => AlphaNeg::Fun {
                arg: Box::new(self.pos(*arg)),
                arg_eff: Box::new(self.pos(*arg_eff)),
                ret_eff: Box::new(self.neg(*ret_eff)),
                ret: Box::new(self.neg(*ret)),
            },
            Neg::Record(fields) => AlphaNeg::Record(self.neg_fields(fields)),
            Neg::PolyVariant(variants) => AlphaNeg::PolyVariant(
                variants
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads.iter().map(|payload| self.neg(*payload)).collect(),
                        )
                    })
                    .collect(),
            ),
            Neg::Tuple(items) => {
                AlphaNeg::Tuple(items.iter().map(|item| self.neg(*item)).collect())
            }
            Neg::Row(items, tail) => AlphaNeg::Row(
                items.iter().map(|item| self.neg(*item)).collect(),
                Box::new(self.neg(*tail)),
            ),
            Neg::Stack { inner, weight } => AlphaNeg::Stack {
                inner: Box::new(self.neg(*inner)),
                weight: self.weight(weight),
            },
            Neg::Intersection(left, right) => {
                AlphaNeg::Intersection(Box::new(self.neg(*left)), Box::new(self.neg(*right)))
            }
        };
        self.neg_nodes.insert(id, neg.clone());
        neg
    }

    fn neu(&mut self, id: NeuId) -> AlphaNeu {
        if let Some(neu) = self.neu_nodes.get(&id) {
            return neu.clone();
        }
        let neu = match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                AlphaNeu::Bounds(Box::new(self.pos(*lower)), Box::new(self.neg(*upper)))
            }
            Neu::Con(path, args) => AlphaNeu::Con(path.clone(), self.neu_slice(args)),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => AlphaNeu::Fun {
                arg: Box::new(self.neu(*arg)),
                arg_eff: Box::new(self.neu(*arg_eff)),
                ret_eff: Box::new(self.neu(*ret_eff)),
                ret: Box::new(self.neu(*ret)),
            },
            Neu::Record(fields) => AlphaNeu::Record(self.neu_fields(fields)),
            Neu::PolyVariant(variants) => AlphaNeu::PolyVariant(
                variants
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads.iter().map(|payload| self.neu(*payload)).collect(),
                        )
                    })
                    .collect(),
            ),
            Neu::Tuple(items) => AlphaNeu::Tuple(self.neu_slice(items)),
        };
        self.neu_nodes.insert(id, neu.clone());
        neu
    }

    fn role_predicate(&mut self, predicate: &RolePredicate) -> AlphaRolePredicate {
        let inputs = predicate
            .inputs
            .iter()
            .map(|input| match input {
                RolePredicateArg::Covariant(id) => AlphaRolePredicateArg::Covariant(self.pos(*id)),
                RolePredicateArg::Contravariant(id) => {
                    AlphaRolePredicateArg::Contravariant(self.neg(*id))
                }
                RolePredicateArg::Invariant(id) => AlphaRolePredicateArg::Invariant(self.neu(*id)),
            })
            .collect();
        let mut associated = predicate.associated.iter().collect::<Vec<_>>();
        associated.sort_by(|left, right| left.name.cmp(&right.name));
        let associated = associated
            .into_iter()
            .map(|associated| AlphaAssociatedType {
                name: associated.name.clone(),
                value: self.neu(associated.value),
            })
            .collect();
        AlphaRolePredicate {
            role: predicate.role.clone(),
            inputs,
            associated,
        }
    }

    fn pos_fields(&mut self, fields: &[RecordField<PosId>]) -> Vec<AlphaField<AlphaPos>> {
        fields
            .iter()
            .map(|field| AlphaField {
                name: field.name.clone(),
                value: self.pos(field.value),
                optional: field.optional,
            })
            .collect()
    }

    fn neg_fields(&mut self, fields: &[RecordField<NegId>]) -> Vec<AlphaField<AlphaNeg>> {
        fields
            .iter()
            .map(|field| AlphaField {
                name: field.name.clone(),
                value: self.neg(field.value),
                optional: field.optional,
            })
            .collect()
    }

    fn neu_fields(&mut self, fields: &[RecordField<NeuId>]) -> Vec<AlphaField<AlphaNeu>> {
        fields
            .iter()
            .map(|field| AlphaField {
                name: field.name.clone(),
                value: self.neu(field.value),
                optional: field.optional,
            })
            .collect()
    }

    fn neu_slice(&mut self, ids: &[NeuId]) -> Vec<AlphaNeu> {
        ids.iter().map(|id| self.neu(*id)).collect()
    }

    fn weight(&mut self, weight: &StackWeight) -> AlphaStackWeight {
        AlphaStackWeight {
            filter: self.subtractability(weight.filter_set()),
            entries: weight
                .entries()
                .iter()
                .map(|entry| AlphaStackWeightEntry {
                    binder: self.stack_binder(entry.id),
                    pops: entry.pops,
                    floor: entry
                        .floor
                        .iter()
                        .map(|item| self.subtractability(item))
                        .collect(),
                    stack: entry
                        .stack
                        .iter()
                        .map(|item| self.subtractability(item))
                        .collect(),
                })
                .collect(),
        }
    }

    fn subtractability(&mut self, item: &Subtractability) -> AlphaSubtractability {
        match item {
            Subtractability::Empty => AlphaSubtractability::Empty,
            Subtractability::All => AlphaSubtractability::All,
            Subtractability::AllExcept(path, args) => {
                AlphaSubtractability::AllExcept(path.clone(), self.neu_slice(args))
            }
            Subtractability::AllExceptMany(families) => AlphaSubtractability::AllExceptMany(
                families
                    .iter()
                    .map(|(path, args)| (path.clone(), self.neu_slice(args)))
                    .collect(),
            ),
            Subtractability::Set(path, args) => {
                AlphaSubtractability::Set(path.clone(), self.neu_slice(args))
            }
            Subtractability::SetMany(families) => AlphaSubtractability::SetMany(
                families
                    .iter()
                    .map(|(path, args)| (path.clone(), self.neu_slice(args)))
                    .collect(),
            ),
        }
    }
}

fn per_use_binders(scheme: &Scheme) -> HashSet<TypeVar> {
    scheme
        .quantifiers
        .iter()
        .copied()
        .chain(scheme.recursive_bounds.iter().map(|bound| bound.var))
        .collect()
}

fn standalone_role_key(
    arena: &TypeArena,
    predicate: &RolePredicate,
    per_use: &HashSet<TypeVar>,
    boundary: &HashSet<TypeVar>,
    stack: &HashSet<SubtractId>,
    unbound: &HashSet<TypeVar>,
    unbound_stack: &HashSet<SubtractId>,
) -> String {
    let mut builder = AlphaBuilder::new(
        arena,
        per_use.clone(),
        boundary.clone(),
        stack.clone(),
        unbound.clone(),
        unbound_stack.clone(),
    );
    format!("{:?}", builder.role_predicate(predicate))
}

fn standalone_recursive_key(
    arena: &TypeArena,
    var: TypeVar,
    bounds: NeuId,
    per_use: &HashSet<TypeVar>,
    boundary: &HashSet<TypeVar>,
    stack: &HashSet<SubtractId>,
    unbound: &HashSet<TypeVar>,
    unbound_stack: &HashSet<SubtractId>,
) -> String {
    let mut builder = AlphaBuilder::new(
        arena,
        per_use.clone(),
        boundary.clone(),
        stack.clone(),
        unbound.clone(),
        unbound_stack.clone(),
    );
    format!("{:?}:{:?}", builder.binder(var), builder.neu(bounds))
}

fn standalone_boundary_key(
    arena: &TypeArena,
    bound: &BoundaryBound,
    per_use: &HashSet<TypeVar>,
    boundary: &HashSet<TypeVar>,
    stack: &HashSet<SubtractId>,
    unbound: &HashSet<TypeVar>,
    unbound_stack: &HashSet<SubtractId>,
) -> String {
    let mut builder = AlphaBuilder::new(
        arena,
        per_use.clone(),
        boundary.clone(),
        stack.clone(),
        unbound.clone(),
        unbound_stack.clone(),
    );
    format!(
        "{:?}:{:?}:{:?}",
        builder.binder(bound.var),
        builder.pos(bound.lower),
        builder.neg(bound.upper)
    )
}

fn alpha_difference(
    path: impl Into<String>,
    left: &impl std::fmt::Debug,
    right: &impl std::fmt::Debug,
) -> SchemeAlphaDifference {
    SchemeAlphaDifference {
        path: path.into(),
        left: debug_excerpt(left),
        right: debug_excerpt(right),
    }
}

fn count_difference(path: &str, left: usize, right: usize) -> SchemeAlphaDifference {
    SchemeAlphaDifference {
        path: path.into(),
        left: left.to_string(),
        right: right.to_string(),
    }
}

fn debug_excerpt(value: &impl std::fmt::Debug) -> String {
    const LIMIT: usize = 320;
    let text = format!("{value:?}");
    if text.len() <= LIMIT {
        return text;
    }
    let mut end = LIMIT;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…", &text[..end])
}
