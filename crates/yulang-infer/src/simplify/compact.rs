use std::collections::HashMap;

use rustc_hash::{FxHashMap, FxHashSet};
use std::mem;

use std::time::Duration;

use crate::profile::ProfileClock as Instant;

use smallvec::SmallVec;

use crate::ids::{NegId, PosId, TypeVar};
use crate::scheme::OwnedSchemeInstance;
use crate::symbols::{Name, Path};
use crate::types::RecordField;
use crate::types::{Neg, Pos};

use crate::solve::{Infer, IntoNegId, IntoPosId};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CompactBounds {
    pub self_var: Option<TypeVar>,
    pub lower: CompactType,
    pub upper: CompactType,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CompactTypeScheme {
    pub cty: CompactBounds,
    pub rec_vars: std::collections::HashMap<TypeVar, CompactBounds>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CompactType {
    pub vars: std::collections::HashSet<TypeVar>,
    pub prims: std::collections::HashSet<Path>,
    pub cons: Vec<CompactCon>,
    pub funs: Vec<CompactFun>,
    pub records: Vec<CompactRecord>,
    pub record_spreads: Vec<CompactRecordSpread>,
    pub variants: Vec<CompactVariant>,
    pub tuples: Vec<Vec<CompactType>>,
    pub rows: Vec<CompactRow>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CompactProfile {
    pub compact_var_side: Duration,
    pub compact_pos_ref: Duration,
    pub compact_neg_ref: Duration,
    pub compact_reachable_rec_vars: Duration,
}

impl CompactProfile {
    pub fn merge(&mut self, other: &Self) {
        self.compact_var_side += other.compact_var_side;
        self.compact_pos_ref += other.compact_pos_ref;
        self.compact_neg_ref += other.compact_neg_ref;
        self.compact_reachable_rec_vars += other.compact_reachable_rec_vars;
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactCon {
    pub path: Path,
    pub args: Vec<CompactBounds>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactFun {
    pub arg: CompactType,
    pub arg_eff: CompactType,
    pub ret_eff: CompactType,
    pub ret: CompactType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactRecord {
    pub fields: Vec<RecordField<CompactType>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactRecordSpread {
    pub fields: Vec<RecordField<CompactType>>,
    pub tail: Box<CompactType>,
    pub tail_wins: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactVariant {
    pub items: Vec<(Name, Vec<CompactType>)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactRow {
    pub items: Vec<CompactType>,
    pub tail: Box<CompactType>,
}

pub fn compact_type_var(infer: &Infer, tv: TypeVar) -> CompactTypeScheme {
    compact_type_var_profiled(infer, tv).0
}

pub fn compact_type_var_profiled(
    infer: &Infer,
    tv: TypeVar,
) -> (CompactTypeScheme, CompactProfile) {
    let mut ctx = CompactContext::new(infer);
    let scheme = ctx.compact_scheme(tv);
    (scheme, ctx.profile)
}

pub fn compact_type_vars_in_order(infer: &Infer, roots: &[TypeVar]) -> Vec<CompactTypeScheme> {
    compact_type_vars_in_order_profiled(infer, roots).0
}

pub fn compact_type_vars_in_order_profiled(
    infer: &Infer,
    roots: &[TypeVar],
) -> (Vec<CompactTypeScheme>, CompactProfile) {
    let mut ctx = CompactContext::new(infer);
    let schemes = roots
        .iter()
        .copied()
        .map(|tv| ctx.compact_scheme(tv))
        .collect();
    (schemes, ctx.profile)
}

pub(crate) fn compact_pos_expr<P: IntoPosId>(infer: &Infer, pos: P) -> CompactType {
    CompactContext::new(infer).compact_pos_id(pos.into_pos_id(infer), &ParentStack::new())
}

pub(crate) fn compact_neg_expr<N: IntoNegId>(infer: &Infer, neg: N) -> CompactType {
    CompactContext::new(infer).compact_neg_id(neg.into_neg_id(infer), &ParentStack::new())
}

pub(crate) fn merge_compact_bounds(
    positive: bool,
    lhs: CompactBounds,
    rhs: CompactBounds,
) -> CompactBounds {
    CompactBounds {
        self_var: lhs.self_var.or(rhs.self_var),
        lower: merge_compact_types(positive, lhs.lower, rhs.lower),
        upper: merge_compact_types(!positive, lhs.upper, rhs.upper),
    }
}

pub(crate) fn merge_compact_types(
    positive: bool,
    lhs: CompactType,
    rhs: CompactType,
) -> CompactType {
    if is_empty_compact_type(&lhs) {
        return rhs;
    }
    if is_empty_compact_type(&rhs) {
        return lhs;
    }
    if lhs == rhs {
        return lhs;
    }

    let CompactType {
        vars: rhs_vars,
        prims: rhs_prims,
        cons: rhs_cons,
        funs: rhs_funs,
        records: rhs_records,
        record_spreads: rhs_record_spreads,
        variants: rhs_variants,
        tuples: rhs_tuples,
        rows: rhs_rows,
    } = rhs;
    let mut lhs = lhs;
    lhs.vars.extend(rhs_vars);
    lhs.prims.extend(rhs_prims);
    lhs.cons = merge_cons(positive, lhs.cons, rhs_cons);
    lhs.funs = merge_funs(positive, lhs.funs, rhs_funs);
    lhs.records = merge_records(positive, lhs.records, rhs_records);
    lhs.record_spreads = merge_unique_owned(lhs.record_spreads, rhs_record_spreads);
    lhs.variants = merge_unique_owned(lhs.variants, rhs_variants);
    lhs.tuples = merge_tuples(positive, lhs.tuples, rhs_tuples);
    lhs.rows = merge_rows(positive, lhs.rows, rhs_rows);
    lhs
}

struct CompactContext<'a> {
    infer: &'a Infer,
    lower_bounds: std::cell::Ref<'a, FxHashMap<TypeVar, SmallVec<[PosId; 2]>>>,
    upper_bounds: std::cell::Ref<'a, FxHashMap<TypeVar, SmallVec<[NegId; 2]>>>,
    compact_lower_instances:
        std::cell::Ref<'a, FxHashMap<TypeVar, SmallVec<[OwnedSchemeInstance; 2]>>>,
    in_progress: FxHashSet<(TypeVar, bool)>,
    recursive: FxHashSet<(TypeVar, bool)>,
    rec_vars: FxHashMap<TypeVar, CompactBounds>,
    cache: FxHashMap<(TypeVar, bool), CompactType>,
    profile: CompactProfile,
}

type ParentStack = SmallVec<[TypeVar; 8]>;

impl<'a> CompactContext<'a> {
    fn new(infer: &'a Infer) -> Self {
        Self {
            infer,
            lower_bounds: infer.lower.borrow(),
            upper_bounds: infer.upper.borrow(),
            compact_lower_instances: infer.compact_lower_instances.borrow(),
            in_progress: FxHashSet::default(),
            recursive: FxHashSet::default(),
            rec_vars: FxHashMap::default(),
            cache: FxHashMap::default(),
            profile: CompactProfile::default(),
        }
    }

    fn compact_var(&mut self, tv: TypeVar) -> CompactBounds {
        CompactBounds {
            self_var: Some(tv),
            lower: self.compact_var_side(tv, true, &ParentStack::new()),
            upper: self.compact_var_side(tv, false, &ParentStack::new()),
        }
    }

    fn compact_scheme(&mut self, tv: TypeVar) -> CompactTypeScheme {
        let cty = self.compact_var(tv);
        let reachable_start = Instant::now();
        let rec_vars = self.reachable_rec_vars(&cty);
        self.profile.compact_reachable_rec_vars += reachable_start.elapsed();
        CompactTypeScheme { rec_vars, cty }
    }

    fn reachable_rec_vars(
        &self,
        cty: &CompactBounds,
    ) -> std::collections::HashMap<TypeVar, CompactBounds> {
        let mut out = std::collections::HashMap::new();
        let mut stack = Vec::new();
        let mut seen = FxHashSet::default();

        if let Some(tv) = cty.self_var {
            stack.push(tv);
        }
        self.collect_referenced_rec_vars_in_bounds(cty, &mut stack);

        while let Some(tv) = stack.pop() {
            if !seen.insert(tv) {
                continue;
            }
            let Some(bounds) = self.rec_vars.get(&tv) else {
                continue;
            };
            self.collect_referenced_rec_vars_in_bounds(bounds, &mut stack);
            out.insert(tv, bounds.clone());
        }

        out
    }

    fn collect_referenced_rec_vars_in_bounds(
        &self,
        bounds: &CompactBounds,
        stack: &mut Vec<TypeVar>,
    ) {
        if let Some(tv) = bounds.self_var {
            if self.rec_vars.contains_key(&tv) {
                stack.push(tv);
            }
        }
        self.collect_referenced_rec_vars_in_type(&bounds.lower, stack);
        self.collect_referenced_rec_vars_in_type(&bounds.upper, stack);
    }

    fn collect_referenced_rec_vars_in_type(&self, ty: &CompactType, stack: &mut Vec<TypeVar>) {
        stack.extend(
            ty.vars
                .iter()
                .copied()
                .filter(|tv| self.rec_vars.contains_key(tv)),
        );
        for con in &ty.cons {
            for arg in &con.args {
                self.collect_referenced_rec_vars_in_bounds(arg, stack);
            }
        }
        for fun in &ty.funs {
            self.collect_referenced_rec_vars_in_type(&fun.arg, stack);
            self.collect_referenced_rec_vars_in_type(&fun.arg_eff, stack);
            self.collect_referenced_rec_vars_in_type(&fun.ret_eff, stack);
            self.collect_referenced_rec_vars_in_type(&fun.ret, stack);
        }
        for record in &ty.records {
            for field in &record.fields {
                self.collect_referenced_rec_vars_in_type(&field.value, stack);
            }
        }
        for spread in &ty.record_spreads {
            for field in &spread.fields {
                self.collect_referenced_rec_vars_in_type(&field.value, stack);
            }
            self.collect_referenced_rec_vars_in_type(&spread.tail, stack);
        }
        for variant in &ty.variants {
            for (_, payloads) in &variant.items {
                for payload in payloads {
                    self.collect_referenced_rec_vars_in_type(payload, stack);
                }
            }
        }
        for tuple in &ty.tuples {
            for item in tuple {
                self.collect_referenced_rec_vars_in_type(item, stack);
            }
        }
        for row in &ty.rows {
            for item in &row.items {
                self.collect_referenced_rec_vars_in_type(item, stack);
            }
            self.collect_referenced_rec_vars_in_type(&row.tail, stack);
        }
    }

    fn compact_var_side(
        &mut self,
        tv: TypeVar,
        positive: bool,
        parents: &ParentStack,
    ) -> CompactType {
        let start = Instant::now();
        let key = (tv, positive);
        if let Some(cached) = self.cache.get(&key) {
            let out = cached.clone();
            self.profile.compact_var_side += start.elapsed();
            return out;
        }
        if self.in_progress.contains(&key) {
            if parents.contains(&tv) {
                self.profile.compact_var_side += start.elapsed();
                return CompactType::default();
            }
            self.recursive.insert(key);
            self.profile.compact_var_side += start.elapsed();
            return CompactType::from_var(tv);
        }

        self.in_progress.insert(key);
        let mut next_parents = parents.clone();
        next_parents.push(tv);
        let bounds = self.compact_var_bounds(tv, positive, &next_parents);
        let mut bound = if positive {
            merge_compact_types(true, CompactType::from_var(tv), bounds)
        } else {
            merge_compact_types(false, CompactType::from_var(tv), bounds)
        };
        if let Some(alias_tv) = single_alias_var(&bound) {
            if alias_tv != tv && !next_parents.contains(&alias_tv) {
                bound = self.compact_var_side(alias_tv, positive, &next_parents);
            }
        }
        self.in_progress.remove(&key);

        if self.recursive.remove(&key) {
            let entry = self.rec_vars.entry(tv).or_insert_with(|| CompactBounds {
                self_var: Some(tv),
                lower: CompactType::default(),
                upper: CompactType::default(),
            });
            if positive {
                entry.lower = bound.clone();
            } else {
                entry.upper = bound.clone();
            }
            bound = CompactType::from_var(tv);
        }

        self.cache.insert(key, bound.clone());
        self.profile.compact_var_side += start.elapsed();
        bound
    }

    fn compact_var_bounds(
        &mut self,
        tv: TypeVar,
        positive: bool,
        parents: &ParentStack,
    ) -> CompactType {
        if positive {
            let regular = match self
                .lower_bounds
                .get(&tv)
                .map(|bounds| bounds.iter().copied().collect::<SmallVec<[PosId; 4]>>())
            {
                Some(bounds) => self.compact_pos_bounds_ref(bounds.as_slice(), parents),
                None => CompactType::default(),
            };
            let instantiated = match self.compact_lower_instances.get(&tv).map(|instances| {
                instances
                    .iter()
                    .cloned()
                    .collect::<SmallVec<[OwnedSchemeInstance; 2]>>()
            }) {
                Some(instances) => self.compact_instance_bounds_ref(instances.as_slice(), parents),
                None => CompactType::default(),
            };
            merge_compact_types(true, regular, instantiated)
        } else {
            match self
                .upper_bounds
                .get(&tv)
                .map(|bounds| bounds.iter().copied().collect::<SmallVec<[NegId; 4]>>())
            {
                Some(bounds) => self.compact_neg_bounds_ref(bounds.as_slice(), parents),
                None => CompactType::default(),
            }
        }
    }

    fn compact_pos_bounds_ref(&mut self, bounds: &[PosId], parents: &ParentStack) -> CompactType {
        let Some((first, rest)) = bounds.split_first() else {
            return CompactType::default();
        };

        let mut compact = self.compact_pos_id(*first, parents);
        for bound in rest {
            compact = merge_compact_types(true, compact, self.compact_pos_id(*bound, parents));
        }
        compact
    }

    fn compact_instance_bounds_ref(
        &mut self,
        instances: &[OwnedSchemeInstance],
        parents: &ParentStack,
    ) -> CompactType {
        let Some((first, rest)) = instances.split_first() else {
            return CompactType::default();
        };

        let mut compact = self.compact_pos_id(
            self.infer.materialize_compact_lower_instance(first),
            parents,
        );
        for instance in rest {
            compact = merge_compact_types(
                true,
                compact,
                self.compact_pos_id(
                    self.infer.materialize_compact_lower_instance(instance),
                    parents,
                ),
            );
        }
        compact
    }

    fn compact_neg_bounds_ref(&mut self, bounds: &[NegId], parents: &ParentStack) -> CompactType {
        let Some((first, rest)) = bounds.split_first() else {
            return CompactType::default();
        };

        let mut compact = self.compact_neg_id(*first, parents);
        for bound in rest {
            compact = merge_compact_types(false, compact, self.compact_neg_id(*bound, parents));
        }
        compact
    }

    fn compact_pos_id(&mut self, id: PosId, parents: &ParentStack) -> CompactType {
        let start = Instant::now();
        let out = match self.infer.arena.get_pos(id) {
            Pos::Bot => CompactType::default(),
            Pos::Var(tv) | Pos::Raw(tv) => self.compact_var_side(tv, true, parents),
            Pos::Atom(atom) => self.compact_effect_atom_ref(&atom),
            Pos::Forall(_, body) => self.compact_pos_id(body, &ParentStack::new()),
            Pos::Con(path, args) => CompactType::from_con(
                path,
                args.iter()
                    .map(|(p, n)| CompactBounds {
                        self_var: None,
                        lower: self.compact_pos_id(*p, &ParentStack::new()),
                        upper: self.compact_neg_id(*n, &ParentStack::new()),
                    })
                    .collect(),
            ),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactType::from_fun(CompactFun {
                arg: self.compact_neg_id(arg, &ParentStack::new()),
                arg_eff: self.compact_neg_id(arg_eff, &ParentStack::new()),
                ret_eff: self.compact_pos_id(ret_eff, &ParentStack::new()),
                ret: self.compact_pos_id(ret, &ParentStack::new()),
            }),
            Pos::Record(fields) => CompactType::from_record(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.compact_pos_id(field.value, &ParentStack::new()),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Pos::RecordTailSpread { fields, tail } => CompactType::from_record_spread(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.compact_pos_id(field.value, &ParentStack::new()),
                        optional: field.optional,
                    })
                    .collect(),
                self.compact_pos_id(tail, &ParentStack::new()),
                true,
            ),
            Pos::RecordHeadSpread { tail, fields } => CompactType::from_record_spread(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.compact_pos_id(field.value, &ParentStack::new()),
                        optional: field.optional,
                    })
                    .collect(),
                self.compact_pos_id(tail, &ParentStack::new()),
                false,
            ),
            Pos::PolyVariant(items) => CompactType::from_variant(
                items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.compact_pos_id(*payload, &ParentStack::new()))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Pos::Tuple(items) => CompactType::from_tuple(
                items
                    .iter()
                    .map(|item| self.compact_pos_id(*item, &ParentStack::new()))
                    .collect(),
            ),
            Pos::Row(items, tail) => CompactType::from_row_with_polarity(
                true,
                items
                    .iter()
                    .map(|item| self.compact_pos_id(*item, &ParentStack::new()))
                    .collect(),
                self.compact_pos_id(tail, &ParentStack::new()),
            ),
            Pos::Union(lhs, rhs) => merge_compact_types(
                true,
                self.compact_pos_id(lhs, parents),
                self.compact_pos_id(rhs, parents),
            ),
        };
        self.profile.compact_pos_ref += start.elapsed();
        out
    }

    fn compact_neg_id(&mut self, id: NegId, parents: &ParentStack) -> CompactType {
        let start = Instant::now();
        let out = match self.infer.arena.get_neg(id) {
            Neg::Top => CompactType::default(),
            Neg::Var(tv) => self.compact_var_side(tv, false, parents),
            Neg::Atom(atom) => self.compact_effect_atom_ref(&atom),
            Neg::Forall(_, body) => self.compact_neg_id(body, &ParentStack::new()),
            Neg::Con(path, args) => CompactType::from_con(
                path,
                args.iter()
                    .map(|(p, n)| CompactBounds {
                        self_var: None,
                        lower: self.compact_pos_id(*p, &ParentStack::new()),
                        upper: self.compact_neg_id(*n, &ParentStack::new()),
                    })
                    .collect(),
            ),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactType::from_fun(CompactFun {
                arg: self.compact_pos_id(arg, &ParentStack::new()),
                arg_eff: self.compact_pos_id(arg_eff, &ParentStack::new()),
                ret_eff: self.compact_neg_id(ret_eff, &ParentStack::new()),
                ret: self.compact_neg_id(ret, &ParentStack::new()),
            }),
            Neg::Record(fields) => CompactType::from_record(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.compact_neg_id(field.value, &ParentStack::new()),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Neg::PolyVariant(items) => CompactType::from_variant(
                items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.compact_neg_id(*payload, &ParentStack::new()))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Neg::Tuple(items) => CompactType::from_tuple(
                items
                    .iter()
                    .map(|item| self.compact_neg_id(*item, &ParentStack::new()))
                    .collect(),
            ),
            Neg::Row(items, tail) => CompactType::from_row_with_polarity(
                false,
                items
                    .iter()
                    .map(|item| self.compact_neg_id(*item, &ParentStack::new()))
                    .collect(),
                self.compact_neg_id(tail, &ParentStack::new()),
            ),
            Neg::Intersection(lhs, rhs) => merge_compact_types(
                false,
                self.compact_neg_id(lhs, parents),
                self.compact_neg_id(rhs, parents),
            ),
        };
        self.profile.compact_neg_ref += start.elapsed();
        out
    }

    fn compact_effect_atom_ref(&mut self, atom: &crate::types::EffectAtom) -> CompactType {
        if atom.args.is_empty() {
            CompactType::from_prim(atom.path.clone())
        } else {
            CompactType::from_con(
                atom.path.clone(),
                atom.args
                    .iter()
                    .map(|(pos_tv, neg_tv)| CompactBounds {
                        self_var: None,
                        lower: CompactType::from_var(*pos_tv),
                        upper: CompactType::from_var(*neg_tv),
                    })
                    .collect(),
            )
        }
    }
}

pub(crate) fn subst_compact_type(ty: &CompactType, subst: &[(TypeVar, TypeVar)]) -> CompactType {
    CompactType {
        vars: ty
            .vars
            .iter()
            .copied()
            .map(|tv| subst_lookup_small(subst, tv))
            .collect(),
        prims: ty.prims.clone(),
        cons: ty
            .cons
            .iter()
            .map(|item| subst_compact_con(item, subst))
            .collect(),
        funs: ty
            .funs
            .iter()
            .map(|item| subst_compact_fun(item, subst))
            .collect(),
        records: ty
            .records
            .iter()
            .map(|item| subst_compact_record(item, subst))
            .collect(),
        record_spreads: ty
            .record_spreads
            .iter()
            .map(|item| subst_compact_record_spread(item, subst))
            .collect(),
        variants: ty
            .variants
            .iter()
            .map(|item| subst_compact_variant(item, subst))
            .collect(),
        tuples: ty
            .tuples
            .iter()
            .map(|tuple| {
                tuple
                    .iter()
                    .map(|item| subst_compact_type(item, subst))
                    .collect()
            })
            .collect(),
        rows: ty
            .rows
            .iter()
            .map(|item| subst_compact_row(item, subst))
            .collect(),
    }
}

pub(crate) fn subst_compact_bounds(
    bounds: &CompactBounds,
    subst: &[(TypeVar, TypeVar)],
) -> CompactBounds {
    CompactBounds {
        self_var: bounds.self_var.map(|tv| subst_lookup_small(subst, tv)),
        lower: subst_compact_type(&bounds.lower, subst),
        upper: subst_compact_type(&bounds.upper, subst),
    }
}

pub(crate) fn subst_compact_con(con: &CompactCon, subst: &[(TypeVar, TypeVar)]) -> CompactCon {
    CompactCon {
        path: con.path.clone(),
        args: con
            .args
            .iter()
            .map(|bounds| subst_compact_bounds(bounds, subst))
            .collect(),
    }
}

pub(crate) fn subst_compact_fun(fun: &CompactFun, subst: &[(TypeVar, TypeVar)]) -> CompactFun {
    CompactFun {
        arg: subst_compact_type(&fun.arg, subst),
        arg_eff: subst_compact_type(&fun.arg_eff, subst),
        ret_eff: subst_compact_type(&fun.ret_eff, subst),
        ret: subst_compact_type(&fun.ret, subst),
    }
}

pub(crate) fn subst_compact_record(
    record: &CompactRecord,
    subst: &[(TypeVar, TypeVar)],
) -> CompactRecord {
    CompactRecord {
        fields: record
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: subst_compact_type(&field.value, subst),
                optional: field.optional,
            })
            .collect(),
    }
}

pub(crate) fn subst_compact_record_spread(
    spread: &CompactRecordSpread,
    subst: &[(TypeVar, TypeVar)],
) -> CompactRecordSpread {
    CompactRecordSpread {
        fields: spread
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: subst_compact_type(&field.value, subst),
                optional: field.optional,
            })
            .collect(),
        tail: Box::new(subst_compact_type(&spread.tail, subst)),
        tail_wins: spread.tail_wins,
    }
}

pub(crate) fn subst_compact_variant(
    variant: &CompactVariant,
    subst: &[(TypeVar, TypeVar)],
) -> CompactVariant {
    CompactVariant {
        items: variant
            .items
            .iter()
            .map(|(name, payloads)| {
                (
                    name.clone(),
                    payloads
                        .iter()
                        .map(|payload| subst_compact_type(payload, subst))
                        .collect(),
                )
            })
            .collect(),
    }
}

pub(crate) fn subst_compact_row(row: &CompactRow, subst: &[(TypeVar, TypeVar)]) -> CompactRow {
    CompactRow {
        items: row
            .items
            .iter()
            .map(|item| subst_compact_type(item, subst))
            .collect(),
        tail: Box::new(subst_compact_type(&row.tail, subst)),
    }
}

pub(crate) fn subst_lookup_small(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> TypeVar {
    subst
        .iter()
        .find_map(|(from, to)| (*from == tv).then_some(*to))
        .unwrap_or(tv)
}

pub(crate) fn single_substituted_compact_var(
    ty: &CompactType,
    subst: &[(TypeVar, TypeVar)],
) -> Option<TypeVar> {
    if ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
        && ty.vars.len() == 1
    {
        ty.vars
            .iter()
            .copied()
            .next()
            .map(|tv| subst_lookup_small(subst, tv))
    } else {
        None
    }
}

fn single_alias_var(ty: &CompactType) -> Option<TypeVar> {
    (ty.vars.len() == 1
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty())
    .then(|| ty.vars.iter().copied().next())
    .flatten()
}

impl CompactType {
    fn from_var(tv: TypeVar) -> Self {
        let mut vars = std::collections::HashSet::new();
        vars.insert(tv);
        Self {
            vars,
            ..Self::default()
        }
    }

    fn from_prim(path: Path) -> Self {
        let mut prims = std::collections::HashSet::new();
        prims.insert(path);
        Self {
            prims,
            ..Self::default()
        }
    }

    fn from_con(path: Path, args: Vec<CompactBounds>) -> Self {
        Self {
            cons: vec![CompactCon { path, args }],
            ..Self::default()
        }
    }

    fn from_fun(fun: CompactFun) -> Self {
        Self {
            funs: vec![fun],
            ..Self::default()
        }
    }

    fn from_record(fields: Vec<RecordField<CompactType>>) -> Self {
        Self {
            records: vec![CompactRecord { fields }],
            ..Self::default()
        }
    }

    fn from_record_spread(
        fields: Vec<RecordField<CompactType>>,
        tail: CompactType,
        tail_wins: bool,
    ) -> Self {
        Self {
            record_spreads: vec![CompactRecordSpread {
                fields,
                tail: Box::new(tail),
                tail_wins,
            }],
            ..Self::default()
        }
    }

    fn from_variant(items: Vec<(Name, Vec<CompactType>)>) -> Self {
        Self {
            variants: vec![CompactVariant { items }],
            ..Self::default()
        }
    }

    fn from_tuple(items: Vec<CompactType>) -> Self {
        Self {
            tuples: vec![items],
            ..Self::default()
        }
    }

    fn from_row_with_polarity(positive: bool, items: Vec<CompactType>, tail: CompactType) -> Self {
        Self {
            rows: vec![CompactRow {
                items: merge_same_effect_items(positive, items),
                tail: Box::new(tail),
            }],
            ..Self::default()
        }
    }
}

fn merge_cons(positive: bool, lhs: Vec<CompactCon>, rhs: Vec<CompactCon>) -> Vec<CompactCon> {
    let mut out = lhs;
    for other in rhs {
        if let Some(existing) = out
            .iter_mut()
            .find(|con| con.path == other.path && con.args.len() == other.args.len())
        {
            existing.args = mem::take(&mut existing.args)
                .into_iter()
                .zip(other.args.into_iter())
                .map(|(lhs, rhs)| merge_compact_bounds(positive, lhs, rhs))
                .collect();
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

fn merge_funs(positive: bool, lhs: Vec<CompactFun>, rhs: Vec<CompactFun>) -> Vec<CompactFun> {
    let mut iter = lhs.into_iter().chain(rhs);
    let Some(mut acc) = iter.next() else {
        return vec![];
    };
    for other in iter {
        acc = CompactFun {
            arg: merge_compact_types(!positive, acc.arg, other.arg),
            arg_eff: merge_compact_types(!positive, acc.arg_eff, other.arg_eff),
            ret_eff: merge_compact_types(positive, acc.ret_eff, other.ret_eff),
            ret: merge_compact_types(positive, acc.ret, other.ret),
        };
    }
    vec![acc]
}

fn merge_records(
    positive: bool,
    lhs: Vec<CompactRecord>,
    rhs: Vec<CompactRecord>,
) -> Vec<CompactRecord> {
    let mut iter = lhs.into_iter().chain(rhs);
    let Some(mut acc) = iter.next() else {
        return vec![];
    };
    for other in iter {
        let mut rhs_map = other
            .fields
            .into_iter()
            .map(|field| (field.name.clone(), field))
            .collect::<HashMap<_, _>>();
        let mut fields = Vec::new();

        for lhs_field in acc.fields {
            match rhs_map.remove(&lhs_field.name) {
                Some(rhs_field) => fields.push(RecordField {
                    name: lhs_field.name,
                    value: merge_compact_types(positive, lhs_field.value, rhs_field.value),
                    optional: lhs_field.optional && rhs_field.optional,
                }),
                None if !positive => fields.push(lhs_field),
                None => {}
            }
        }

        if !positive {
            for rhs_field in rhs_map.into_values() {
                if !fields
                    .iter()
                    .any(|lhs_field| lhs_field.name == rhs_field.name)
                {
                    fields.push(rhs_field);
                }
            }
        }

        acc = CompactRecord { fields };
    }
    vec![acc]
}

fn merge_tuples(
    positive: bool,
    lhs: Vec<Vec<CompactType>>,
    rhs: Vec<Vec<CompactType>>,
) -> Vec<Vec<CompactType>> {
    let mut out = lhs;
    for other in rhs {
        if let Some(existing) = out.iter_mut().find(|tuple| tuple.len() == other.len()) {
            *existing = mem::take(existing)
                .into_iter()
                .zip(other.into_iter())
                .map(|(lhs, rhs)| merge_compact_types(positive, lhs, rhs))
                .collect();
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

fn merge_rows(positive: bool, lhs: Vec<CompactRow>, rhs: Vec<CompactRow>) -> Vec<CompactRow> {
    let mut out = lhs
        .into_iter()
        .map(|row| CompactRow {
            items: merge_same_effect_items(positive, row.items),
            tail: row.tail,
        })
        .collect::<Vec<_>>();
    for other in rhs {
        let other = CompactRow {
            items: merge_same_effect_items(positive, other.items),
            tail: other.tail,
        };
        if let Some(existing) = out.iter_mut().find(|row| row.tail == other.tail) {
            let items = mem::take(&mut existing.items)
                .into_iter()
                .chain(other.items.into_iter())
                .collect();
            existing.items = merge_same_effect_items(positive, items);
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

fn merge_same_effect_items(positive: bool, items: Vec<CompactType>) -> Vec<CompactType> {
    let mut out = Vec::new();
    let mut keyed = FxHashMap::default();
    for item in items {
        if let Some(key) = single_effect_item_key(&item) {
            if let Some(&index) = keyed.get(&key) {
                let existing = mem::take(&mut out[index]);
                out[index] = merge_compact_types(positive, existing, item);
                continue;
            }
            keyed.insert(key, out.len());
        }
        if !out.contains(&item) {
            out.push(item);
        }
    }
    out
}

fn single_effect_item_key(item: &CompactType) -> Option<(Path, usize)> {
    if !item.vars.is_empty()
        || !item.funs.is_empty()
        || !item.records.is_empty()
        || !item.record_spreads.is_empty()
        || !item.variants.is_empty()
        || !item.tuples.is_empty()
        || !item.rows.is_empty()
    {
        return None;
    }
    if item.prims.len() == 1 && item.cons.is_empty() {
        return item.prims.iter().next().cloned().map(|path| (path, 0));
    }
    if item.cons.len() == 1 && item.prims.is_empty() {
        let con = &item.cons[0];
        return Some((con.path.clone(), con.args.len()));
    }
    None
}

fn merge_unique_owned<T: PartialEq>(mut lhs: Vec<T>, rhs: Vec<T>) -> Vec<T> {
    for other in rhs {
        if !lhs.contains(&other) {
            lhs.push(other);
        }
    }
    lhs
}

fn is_empty_compact_type(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

#[cfg(test)]
mod tests {

    use super::compact_type_var;
    use crate::fresh_type_var;
    use crate::solve::Infer;
    use crate::symbols::{Name, Path};
    use crate::types::{EffectAtom, Neg, Pos};

    #[test]
    fn compact_type_var_collects_function_and_prim_bounds() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        let arg_tv = fresh_type_var();
        let ret_tv = fresh_type_var();

        for current in [tv, arg_tv, ret_tv] {
            infer.register_level(current, 0);
        }

        infer.add_lower(
            tv,
            Pos::Fun {
                arg: infer.alloc_neg(Neg::Var(arg_tv)),
                arg_eff: infer.arena.top,
                ret_eff: infer.arena.bot,
                ret: infer.alloc_pos(Pos::Var(ret_tv)),
            },
        );
        infer.add_lower(
            tv,
            Pos::Con(
                Path {
                    segments: vec![Name("int".to_string())],
                },
                vec![],
            ),
        );

        let compact = compact_type_var(&infer, tv);
        assert_eq!(compact.cty.lower.cons.len(), 1);
        assert_eq!(compact.cty.lower.funs.len(), 1);
    }

    #[test]
    fn compact_type_var_merges_same_effect_items_in_row() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        let arg_a = fresh_type_var();
        let arg_b = fresh_type_var();
        for current in [tv, arg_a, arg_b] {
            infer.register_level(current, 0);
        }

        let path = Path {
            segments: vec![Name("var".to_string())],
        };
        infer.add_lower(
            tv,
            Pos::Row(
                vec![
                    infer.alloc_pos(Pos::Atom(EffectAtom {
                        path: path.clone(),
                        args: vec![(arg_a, arg_a)],
                    })),
                    infer.alloc_pos(Pos::Atom(EffectAtom {
                        path,
                        args: vec![(arg_b, arg_b)],
                    })),
                ],
                infer.arena.bot,
            ),
        );

        let compact = compact_type_var(&infer, tv);
        let row = &compact.cty.lower.rows[0];
        assert_eq!(row.items.len(), 1);
        assert_eq!(row.items[0].cons.len(), 1);
        assert_eq!(row.items[0].cons[0].args.len(), 1);
    }

    #[test]
    fn compact_type_var_ignores_spurious_self_cycle() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        infer.register_level(tv, 0);
        infer.add_lower(tv, Pos::Var(tv));

        let compact = compact_type_var(&infer, tv);
        assert!(!compact.rec_vars.contains_key(&tv));
    }
}
