//! Demand-driven monomorphization prototype.
//!
//! This module is wired as an early monomorphization pass and still falls back
//! to the older fixed-point path when a demand-specialized module does not pass
//! validation.  It is the new algorithmic core being built beside that older
//! path: concrete use sites create demands, demands are deduplicated by a
//! runtime signature, and `_` / `Any` becomes a monomorphization hole instead
//! of a VM type witness.

use std::collections::{HashMap, HashSet, VecDeque};

use yulang_core_ir as core_ir;

use crate::ir::Type as RuntimeType;

mod associated;
mod check;
mod collect;
mod emit;
mod engine;
mod solve;
mod specialize;

use associated::*;
pub use check::*;
pub use collect::*;
pub use emit::*;
pub use engine::*;
pub use solve::*;
pub use specialize::*;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct DemandQueue {
    queue: VecDeque<Demand>,
    seen: HashSet<DemandKey>,
}

impl DemandQueue {
    pub fn push(&mut self, target: core_ir::Path, expected: RuntimeType) -> bool {
        let demand = Demand::new(target, expected);
        self.push_demand(demand)
    }

    pub fn push_signature(
        &mut self,
        target: core_ir::Path,
        expected: RuntimeType,
        signature: DemandSignature,
    ) -> bool {
        let demand = Demand::with_signature(target, expected, signature);
        self.push_demand(demand)
    }

    fn push_demand(&mut self, demand: Demand) -> bool {
        if !self.seen.insert(demand.key.clone()) {
            return false;
        }
        self.queue.push_back(demand);
        true
    }

    pub fn pop_front(&mut self) -> Option<Demand> {
        self.queue.pop_front()
    }

    pub fn len(&self) -> usize {
        self.queue.len()
    }

    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Demand {
    pub target: core_ir::Path,
    pub expected: RuntimeType,
    pub key: DemandKey,
}

impl Demand {
    pub fn new(target: core_ir::Path, expected: RuntimeType) -> Self {
        let key = DemandKey::new(target.clone(), &expected);
        Self {
            target,
            expected,
            key,
        }
    }

    pub fn with_signature(
        target: core_ir::Path,
        expected: RuntimeType,
        signature: DemandSignature,
    ) -> Self {
        let signature = close_known_associated_type_signature(&target, signature);
        let key = DemandKey::from_signature(target.clone(), signature);
        Self {
            target,
            expected,
            key,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DemandKey {
    pub target: core_ir::Path,
    pub signature: DemandSignature,
}

impl DemandKey {
    pub fn new(target: core_ir::Path, expected: &RuntimeType) -> Self {
        Self {
            target,
            signature: DemandSignature::from_runtime_type(expected).canonicalize_holes(),
        }
    }

    pub fn from_signature(target: core_ir::Path, signature: DemandSignature) -> Self {
        Self {
            target,
            signature: signature.canonicalize_holes(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DemandSignature {
    Ignored,
    Hole(u32),
    Core(DemandCoreType),
    Fun {
        param: Box<DemandSignature>,
        ret: Box<DemandSignature>,
    },
    Thunk {
        effect: DemandEffect,
        value: Box<DemandSignature>,
    },
}

impl DemandSignature {
    pub fn from_runtime_type(ty: &RuntimeType) -> Self {
        let mut next_hole = 0;
        Self::from_runtime_type_with_holes(ty, &mut next_hole)
    }

    pub fn from_runtime_type_with_holes(ty: &RuntimeType, next_hole: &mut u32) -> Self {
        let mut builder = SignatureBuilder {
            next_hole: *next_hole,
        };
        let signature = builder.runtime_type(ty);
        *next_hole = builder.next_hole;
        signature
    }

    pub fn next_hole_after(&self) -> u32 {
        match self {
            DemandSignature::Ignored => 0,
            DemandSignature::Hole(id) => id + 1,
            DemandSignature::Core(ty) => ty.next_hole_after(),
            DemandSignature::Fun { param, ret } => {
                param.next_hole_after().max(ret.next_hole_after())
            }
            DemandSignature::Thunk { effect, value } => {
                effect.next_hole_after().max(value.next_hole_after())
            }
        }
    }

    pub fn canonicalize_holes(&self) -> Self {
        HoleCanonicalizer::default().signature(self)
    }

    pub fn is_closed(&self) -> bool {
        match self {
            DemandSignature::Ignored => true,
            DemandSignature::Hole(_) => false,
            DemandSignature::Core(ty) => ty.is_closed(),
            DemandSignature::Fun { param, ret } => param.is_closed() && ret.is_closed(),
            DemandSignature::Thunk { effect, value } => effect.is_closed() && value.is_closed(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DemandEffect {
    Empty,
    Hole(u32),
    Atom(DemandCoreType),
    Row(Vec<DemandEffect>),
}

impl DemandEffect {
    pub fn from_core_type(ty: &core_ir::Type) -> Self {
        let mut next_hole = 0;
        Self::from_core_type_with_holes(ty, &mut next_hole)
    }

    pub fn from_core_type_with_holes(ty: &core_ir::Type, next_hole: &mut u32) -> Self {
        let mut builder = SignatureBuilder {
            next_hole: *next_hole,
        };
        let effect = builder.effect_type(ty);
        *next_hole = builder.next_hole;
        effect
    }

    pub fn next_hole_after(&self) -> u32 {
        match self {
            DemandEffect::Empty => 0,
            DemandEffect::Hole(id) => id + 1,
            DemandEffect::Atom(ty) => ty.next_hole_after(),
            DemandEffect::Row(items) => items
                .iter()
                .map(DemandEffect::next_hole_after)
                .max()
                .unwrap_or(0),
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            DemandEffect::Empty => true,
            DemandEffect::Hole(_) => false,
            DemandEffect::Atom(ty) => ty.is_closed(),
            DemandEffect::Row(items) => items.iter().all(DemandEffect::is_closed),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DemandCoreType {
    Any,
    Never,
    Hole(u32),
    Named {
        path: core_ir::Path,
        args: Vec<DemandTypeArg>,
    },
    Fun {
        param: Box<DemandCoreType>,
        param_effect: Box<DemandEffect>,
        ret_effect: Box<DemandEffect>,
        ret: Box<DemandCoreType>,
    },
    Tuple(Vec<DemandCoreType>),
    Record(Vec<DemandRecordField>),
    Variant(Vec<DemandVariantCase>),
    RowAsValue(Vec<DemandEffect>),
    Union(Vec<DemandCoreType>),
    Inter(Vec<DemandCoreType>),
    Recursive {
        var: core_ir::TypeVar,
        body: Box<DemandCoreType>,
    },
}

impl DemandCoreType {
    pub fn next_hole_after(&self) -> u32 {
        match self {
            DemandCoreType::Any => 0,
            DemandCoreType::Never => 0,
            DemandCoreType::Hole(id) => id + 1,
            DemandCoreType::Named { args, .. } => args
                .iter()
                .map(DemandTypeArg::next_hole_after)
                .max()
                .unwrap_or(0),
            DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => param
                .next_hole_after()
                .max(param_effect.next_hole_after())
                .max(ret_effect.next_hole_after())
                .max(ret.next_hole_after()),
            DemandCoreType::Tuple(items)
            | DemandCoreType::Union(items)
            | DemandCoreType::Inter(items) => items
                .iter()
                .map(DemandCoreType::next_hole_after)
                .max()
                .unwrap_or(0),
            DemandCoreType::Record(fields) => fields
                .iter()
                .map(|field| field.value.next_hole_after())
                .max()
                .unwrap_or(0),
            DemandCoreType::Variant(cases) => cases
                .iter()
                .flat_map(|case| case.payloads.iter())
                .map(DemandCoreType::next_hole_after)
                .max()
                .unwrap_or(0),
            DemandCoreType::RowAsValue(items) => items
                .iter()
                .map(DemandEffect::next_hole_after)
                .max()
                .unwrap_or(0),
            DemandCoreType::Recursive { body, .. } => body.next_hole_after(),
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            DemandCoreType::Any => true,
            DemandCoreType::Never => true,
            DemandCoreType::Hole(_) => false,
            DemandCoreType::Named { args, .. } => args.iter().all(DemandTypeArg::is_closed),
            DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                param.is_closed()
                    && param_effect.is_closed()
                    && ret_effect.is_closed()
                    && ret.is_closed()
            }
            DemandCoreType::Tuple(items)
            | DemandCoreType::Union(items)
            | DemandCoreType::Inter(items) => items.iter().all(DemandCoreType::is_closed),
            DemandCoreType::Record(fields) => fields.iter().all(|field| field.value.is_closed()),
            DemandCoreType::Variant(cases) => cases
                .iter()
                .flat_map(|case| case.payloads.iter())
                .all(DemandCoreType::is_closed),
            DemandCoreType::RowAsValue(items) => items.iter().all(DemandEffect::is_closed),
            DemandCoreType::Recursive { body, .. } => body.is_closed(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DemandTypeArg {
    Type(DemandCoreType),
    Bounds {
        lower: Option<DemandCoreType>,
        upper: Option<DemandCoreType>,
    },
}

impl DemandTypeArg {
    pub fn next_hole_after(&self) -> u32 {
        match self {
            DemandTypeArg::Type(ty) => ty.next_hole_after(),
            DemandTypeArg::Bounds { lower, upper } => lower
                .iter()
                .chain(upper)
                .map(DemandCoreType::next_hole_after)
                .max()
                .unwrap_or(0),
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            DemandTypeArg::Type(ty) => ty.is_closed(),
            DemandTypeArg::Bounds { lower, upper } => {
                lower.iter().chain(upper).all(|ty| ty.is_closed())
            }
        }
    }
}

#[derive(Debug, Default)]
struct HoleCanonicalizer {
    values: HashMap<u32, u32>,
    cores: HashMap<u32, u32>,
    effects: HashMap<u32, u32>,
    next_value: u32,
    next_core: u32,
    next_effect: u32,
}

impl HoleCanonicalizer {
    fn signature(&mut self, signature: &DemandSignature) -> DemandSignature {
        match signature {
            DemandSignature::Ignored => DemandSignature::Ignored,
            DemandSignature::Hole(id) => DemandSignature::Hole(self.value_hole(*id)),
            DemandSignature::Core(ty) => DemandSignature::Core(self.core_type(ty)),
            DemandSignature::Fun { param, ret } => DemandSignature::Fun {
                param: Box::new(self.signature(param)),
                ret: Box::new(self.signature(ret)),
            },
            DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
                effect: self.effect(effect),
                value: Box::new(self.signature(value)),
            },
        }
    }

    fn core_type(&mut self, ty: &DemandCoreType) -> DemandCoreType {
        match ty {
            DemandCoreType::Any => DemandCoreType::Any,
            DemandCoreType::Never => DemandCoreType::Never,
            DemandCoreType::Hole(id) => DemandCoreType::Hole(self.core_hole(*id)),
            DemandCoreType::Named { path, args } => DemandCoreType::Named {
                path: path.clone(),
                args: args.iter().map(|arg| self.type_arg(arg)).collect(),
            },
            DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => DemandCoreType::Fun {
                param: Box::new(self.core_type(param)),
                param_effect: Box::new(self.effect(param_effect)),
                ret_effect: Box::new(self.effect(ret_effect)),
                ret: Box::new(self.core_type(ret)),
            },
            DemandCoreType::Tuple(items) => {
                DemandCoreType::Tuple(items.iter().map(|item| self.core_type(item)).collect())
            }
            DemandCoreType::Record(fields) => DemandCoreType::Record(
                fields
                    .iter()
                    .map(|field| DemandRecordField {
                        name: field.name.clone(),
                        value: self.core_type(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            DemandCoreType::Variant(cases) => DemandCoreType::Variant(
                cases
                    .iter()
                    .map(|case| DemandVariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .map(|payload| self.core_type(payload))
                            .collect(),
                    })
                    .collect(),
            ),
            DemandCoreType::RowAsValue(items) => {
                DemandCoreType::RowAsValue(items.iter().map(|item| self.effect(item)).collect())
            }
            DemandCoreType::Union(items) => {
                DemandCoreType::Union(items.iter().map(|item| self.core_type(item)).collect())
            }
            DemandCoreType::Inter(items) => {
                DemandCoreType::Inter(items.iter().map(|item| self.core_type(item)).collect())
            }
            DemandCoreType::Recursive { var, body } => DemandCoreType::Recursive {
                var: var.clone(),
                body: Box::new(self.core_type(body)),
            },
        }
    }

    fn effect(&mut self, effect: &DemandEffect) -> DemandEffect {
        match effect {
            DemandEffect::Empty => DemandEffect::Empty,
            DemandEffect::Hole(id) => DemandEffect::Hole(self.effect_hole(*id)),
            DemandEffect::Atom(ty) => DemandEffect::Atom(self.core_type(ty)),
            DemandEffect::Row(items) => {
                DemandEffect::Row(items.iter().map(|item| self.effect(item)).collect())
            }
        }
    }

    fn type_arg(&mut self, arg: &DemandTypeArg) -> DemandTypeArg {
        match arg {
            DemandTypeArg::Type(ty) => DemandTypeArg::Type(self.core_type(ty)),
            DemandTypeArg::Bounds { lower, upper } => DemandTypeArg::Bounds {
                lower: lower.as_ref().map(|ty| self.core_type(ty)),
                upper: upper.as_ref().map(|ty| self.core_type(ty)),
            },
        }
    }

    fn value_hole(&mut self, id: u32) -> u32 {
        canonical_hole(&mut self.values, &mut self.next_value, id)
    }

    fn core_hole(&mut self, id: u32) -> u32 {
        canonical_hole(&mut self.cores, &mut self.next_core, id)
    }

    fn effect_hole(&mut self, id: u32) -> u32 {
        canonical_hole(&mut self.effects, &mut self.next_effect, id)
    }
}

fn canonical_hole(map: &mut HashMap<u32, u32>, next: &mut u32, id: u32) -> u32 {
    *map.entry(id).or_insert_with(|| {
        let canonical = *next;
        *next += 1;
        canonical
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DemandRecordField {
    pub name: core_ir::Name,
    pub value: DemandCoreType,
    pub optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DemandVariantCase {
    pub name: core_ir::Name,
    pub payloads: Vec<DemandCoreType>,
}

#[derive(Debug, Default)]
struct SignatureBuilder {
    next_hole: u32,
}

impl SignatureBuilder {
    fn runtime_type(&mut self, ty: &RuntimeType) -> DemandSignature {
        match ty {
            RuntimeType::Core(ty) => match self.core_type(ty) {
                DemandCoreType::Hole(id) => DemandSignature::Hole(id),
                ty => DemandSignature::Core(ty),
            },
            RuntimeType::Fun { param, ret } => DemandSignature::Fun {
                param: Box::new(self.runtime_type(param)),
                ret: Box::new(self.runtime_type(ret)),
            },
            RuntimeType::Thunk { effect, value } => DemandSignature::Thunk {
                effect: self.effect_type(effect),
                value: Box::new(self.runtime_type(value)),
            },
        }
    }

    fn core_type(&mut self, ty: &core_ir::Type) -> DemandCoreType {
        match ty {
            core_ir::Type::Never => DemandCoreType::Never,
            core_ir::Type::Any | core_ir::Type::Var(_) => DemandCoreType::Hole(self.fresh_hole()),
            core_ir::Type::Named { path, args } => DemandCoreType::Named {
                path: path.clone(),
                args: args.iter().map(|arg| self.type_arg(arg)).collect(),
            },
            core_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => DemandCoreType::Fun {
                param: Box::new(self.core_type(param)),
                param_effect: Box::new(self.effect_type(param_effect)),
                ret_effect: Box::new(self.effect_type(ret_effect)),
                ret: Box::new(self.core_type(ret)),
            },
            core_ir::Type::Tuple(items) => {
                DemandCoreType::Tuple(items.iter().map(|item| self.core_type(item)).collect())
            }
            core_ir::Type::Record(record) => DemandCoreType::Record(
                record
                    .fields
                    .iter()
                    .map(|field| DemandRecordField {
                        name: field.name.clone(),
                        value: self.core_type(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            core_ir::Type::Variant(variant) => DemandCoreType::Variant(
                variant
                    .cases
                    .iter()
                    .map(|case| DemandVariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .map(|payload| self.core_type(payload))
                            .collect(),
                    })
                    .collect(),
            ),
            core_ir::Type::Row { items, tail } => {
                let mut row = items
                    .iter()
                    .map(|item| self.effect_type(item))
                    .collect::<Vec<_>>();
                row.push(self.effect_type(tail));
                DemandCoreType::RowAsValue(row)
            }
            core_ir::Type::Union(items) => {
                DemandCoreType::Union(items.iter().map(|item| self.core_type(item)).collect())
            }
            core_ir::Type::Inter(items) => {
                DemandCoreType::Inter(items.iter().map(|item| self.core_type(item)).collect())
            }
            core_ir::Type::Recursive { var, body } => DemandCoreType::Recursive {
                var: var.clone(),
                body: Box::new(self.core_type(body)),
            },
        }
    }

    fn effect_type(&mut self, ty: &core_ir::Type) -> DemandEffect {
        match ty {
            core_ir::Type::Never => DemandEffect::Empty,
            core_ir::Type::Any | core_ir::Type::Var(_) => DemandEffect::Hole(self.fresh_hole()),
            core_ir::Type::Row { items, tail } => {
                let mut row = items
                    .iter()
                    .map(|item| self.effect_type(item))
                    .filter(|item| !matches!(item, DemandEffect::Empty))
                    .collect::<Vec<_>>();
                let tail = self.effect_type(tail);
                if !matches!(tail, DemandEffect::Empty) {
                    row.push(tail);
                }
                if row.is_empty() {
                    DemandEffect::Empty
                } else {
                    DemandEffect::Row(row)
                }
            }
            other => DemandEffect::Atom(self.core_type(other)),
        }
    }

    fn type_arg(&mut self, arg: &core_ir::TypeArg) -> DemandTypeArg {
        match arg {
            core_ir::TypeArg::Type(ty) => DemandTypeArg::Type(self.core_type(ty)),
            core_ir::TypeArg::Bounds(bounds) => DemandTypeArg::Bounds {
                lower: bounds.lower.as_deref().map(|ty| self.core_type(ty)),
                upper: bounds.upper.as_deref().map(|ty| self.core_type(ty)),
            },
        }
    }

    fn fresh_hole(&mut self) -> u32 {
        let id = self.next_hole;
        self.next_hole += 1;
        id
    }
}

pub(super) fn curried_signatures(
    args: &[DemandSignature],
    ret: DemandSignature,
) -> DemandSignature {
    args.iter()
        .rev()
        .fold(ret, |ret, arg| DemandSignature::Fun {
            param: Box::new(arg.clone()),
            ret: Box::new(ret),
        })
}

pub(super) fn signature_core_value(signature: &DemandSignature) -> DemandCoreType {
    match signature {
        DemandSignature::Ignored => DemandCoreType::Any,
        DemandSignature::Hole(id) => DemandCoreType::Hole(*id),
        DemandSignature::Core(ty) => ty.clone(),
        DemandSignature::Fun { param, ret } => {
            let (param, param_effect) = signature_effected_core_value(param);
            let (ret, ret_effect) = signature_effected_core_value(ret);
            DemandCoreType::Fun {
                param: Box::new(param),
                param_effect: Box::new(param_effect),
                ret_effect: Box::new(ret_effect),
                ret: Box::new(ret),
            }
        }
        DemandSignature::Thunk { value, .. } => signature_core_value(value),
    }
}

pub(super) fn signature_value(signature: &DemandSignature) -> DemandSignature {
    match signature {
        DemandSignature::Thunk { value, .. } => signature_value(value),
        other => other.clone(),
    }
}

pub(super) fn signature_effected_core_value(
    signature: &DemandSignature,
) -> (DemandCoreType, DemandEffect) {
    match signature {
        DemandSignature::Thunk { effect, value } => (signature_core_value(value), effect.clone()),
        other => (signature_core_value(other), DemandEffect::Empty),
    }
}

pub(super) fn effected_core_signature(ty: DemandCoreType, effect: DemandEffect) -> DemandSignature {
    if matches!(effect, DemandEffect::Empty) {
        DemandSignature::Core(ty)
    } else {
        DemandSignature::Thunk {
            effect,
            value: Box::new(DemandSignature::Core(ty)),
        }
    }
}

pub(super) fn apply_evidence_merged_signature(
    evidence: &core_ir::ApplyEvidence,
    fallback: DemandSignature,
) -> DemandSignature {
    let Some(evidence) = apply_evidence_signature(evidence) else {
        return fallback;
    };
    merge_signature_hint(fallback, evidence)
}

fn apply_evidence_signature(evidence: &core_ir::ApplyEvidence) -> Option<DemandSignature> {
    if let Some(core_ir::Type::Fun {
        ret_effect, ret, ..
    }) = evidence_bounds_type(&evidence.callee)
    {
        let mut next_hole = 0;
        let ret = DemandSignature::from_runtime_type_with_holes(
            &RuntimeType::core(ret.as_ref().clone()),
            &mut next_hole,
        );
        let ret_effect = DemandEffect::from_core_type_with_holes(ret_effect, &mut next_hole);
        return Some(effected_core_signature(
            signature_core_value(&ret),
            ret_effect,
        ));
    }
    evidence_bounds_type(&evidence.result)
        .map(|ty| DemandSignature::from_runtime_type(&RuntimeType::core(ty.clone())))
}

fn evidence_bounds_type(bounds: &core_ir::TypeBounds) -> Option<&core_ir::Type> {
    bounds.lower.as_deref().or(bounds.upper.as_deref())
}

pub(super) fn merge_signature_hint(
    fallback: DemandSignature,
    hint: DemandSignature,
) -> DemandSignature {
    let Ok(substitutions) = DemandUnifier::new().unify_signature(&fallback, &hint) else {
        return fallback;
    };
    substitutions.apply_signature(&fallback)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn demand_signature_turns_any_value_into_hole() {
        let ty = RuntimeType::fun(
            RuntimeType::core(core_ir::Type::Any),
            RuntimeType::core(named("int")),
        );

        let signature = DemandSignature::from_runtime_type(&ty);

        assert_eq!(
            signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Hole(0)),
                ret: Box::new(DemandSignature::Core(DemandCoreType::Named {
                    path: path("int"),
                    args: Vec::new(),
                })),
            }
        );
    }

    #[test]
    fn demand_signature_keeps_effect_holes_separate_from_value_holes() {
        let ty = RuntimeType::thunk(core_ir::Type::Any, RuntimeType::core(core_ir::Type::Any));

        let signature = DemandSignature::from_runtime_type(&ty);

        assert_eq!(
            signature,
            DemandSignature::Thunk {
                effect: DemandEffect::Hole(0),
                value: Box::new(DemandSignature::Hole(1)),
            }
        );
    }

    #[test]
    fn demand_queue_deduplicates_equivalent_demands() {
        let mut queue = DemandQueue::default();
        let target = path("id");

        assert!(queue.push(target.clone(), RuntimeType::core(core_ir::Type::Any)));
        assert!(!queue.push(target, RuntimeType::core(core_ir::Type::Any)));
        assert_eq!(queue.len(), 1);
    }

    #[test]
    fn demand_queue_distinguishes_different_concrete_demands() {
        let mut queue = DemandQueue::default();
        let target = path("id");

        assert!(queue.push(target.clone(), RuntimeType::core(named("int"))));
        assert!(queue.push(target, RuntimeType::core(named("str"))));
        assert_eq!(queue.len(), 2);
    }

    #[test]
    fn demand_signature_can_continue_hole_numbering() {
        let first = RuntimeType::fun(
            RuntimeType::core(core_ir::Type::Any),
            RuntimeType::core(core_ir::Type::Any),
        );
        let mut next_hole = 0;
        let first = DemandSignature::from_runtime_type_with_holes(&first, &mut next_hole);
        let second = DemandSignature::from_runtime_type_with_holes(
            &RuntimeType::core(core_ir::Type::Any),
            &mut next_hole,
        );

        assert_eq!(
            first,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Hole(0)),
                ret: Box::new(DemandSignature::Hole(1)),
            }
        );
        assert_eq!(second, DemandSignature::Hole(2));
        assert_eq!(next_hole, 3);
    }

    #[test]
    fn demand_keys_canonicalize_hole_numbers() {
        let target = path("id");
        let left = DemandKey::from_signature(
            target.clone(),
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Hole(20)),
                ret: Box::new(DemandSignature::Hole(30)),
            },
        );
        let right = DemandKey::from_signature(
            target,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Hole(0)),
                ret: Box::new(DemandSignature::Hole(1)),
            },
        );

        assert_eq!(left, right);
    }

    #[test]
    fn demand_key_hole_canonicalization_keeps_namespaces_separate() {
        let key = DemandKey::from_signature(
            path("f"),
            DemandSignature::Thunk {
                effect: DemandEffect::Hole(8),
                value: Box::new(DemandSignature::Core(DemandCoreType::Hole(8))),
            },
        );

        assert_eq!(
            key.signature,
            DemandSignature::Thunk {
                effect: DemandEffect::Hole(0),
                value: Box::new(DemandSignature::Core(DemandCoreType::Hole(0))),
            }
        );
    }

    #[test]
    fn demand_signature_reports_whether_it_is_closed() {
        assert!(
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(DemandCoreType::Named {
                    path: path("int"),
                    args: Vec::new(),
                })),
                ret: Box::new(DemandSignature::Core(DemandCoreType::Never)),
            }
            .is_closed()
        );
        assert!(
            !DemandSignature::Thunk {
                effect: DemandEffect::Hole(0),
                value: Box::new(DemandSignature::Core(DemandCoreType::Never)),
            }
            .is_closed()
        );
    }

    #[test]
    fn fold_demand_closes_list_item_and_accumulator_callback_types() {
        let demand = Demand::with_signature(
            path_segments(&["std", "list", "&impl#187", "fold"]),
            RuntimeType::core(core_ir::Type::Any),
            fold_signature(DemandSignature::Fun {
                param: Box::new(DemandSignature::Hole(0)),
                ret: Box::new(DemandSignature::Fun {
                    param: Box::new(DemandSignature::Hole(0)),
                    ret: Box::new(unit_thunk()),
                }),
            }),
        );

        let DemandSignature::Fun { ret, .. } = demand.key.signature else {
            panic!("expected fold function");
        };
        let DemandSignature::Fun { ret, .. } = *ret else {
            panic!("expected z function");
        };
        let DemandSignature::Fun { param, .. } = *ret else {
            panic!("expected callback function");
        };

        assert_eq!(
            *param,
            DemandSignature::Fun {
                param: Box::new(unit_signature()),
                ret: Box::new(DemandSignature::Thunk {
                    effect: undet_effect(),
                    value: Box::new(DemandSignature::Fun {
                        param: Box::new(int_signature()),
                        ret: Box::new(unit_thunk()),
                    }),
                }),
            }
        );
    }

    #[test]
    fn fold_impl_demand_wraps_callback_in_empty_thunk() {
        let demand = Demand::with_signature(
            path_segments(&["std", "list", "fold_impl"]),
            RuntimeType::core(core_ir::Type::Any),
            fold_signature(DemandSignature::Fun {
                param: Box::new(DemandSignature::Hole(0)),
                ret: Box::new(DemandSignature::Fun {
                    param: Box::new(DemandSignature::Hole(0)),
                    ret: Box::new(unit_thunk()),
                }),
            }),
        );

        let DemandSignature::Fun { ret, .. } = demand.key.signature else {
            panic!("expected fold_impl function");
        };
        let DemandSignature::Thunk { value: ret, .. } = *ret else {
            panic!("expected fold_impl rest thunk");
        };
        let DemandSignature::Fun { ret, .. } = *ret else {
            panic!("expected z function");
        };
        let DemandSignature::Thunk { value: ret, .. } = *ret else {
            panic!("expected callback rest thunk");
        };
        let DemandSignature::Fun { param, .. } = *ret else {
            panic!("expected callback function");
        };

        assert_eq!(
            *param,
            DemandSignature::Thunk {
                effect: DemandEffect::Empty,
                value: Box::new(DemandSignature::Fun {
                    param: Box::new(unit_signature()),
                    ret: Box::new(DemandSignature::Thunk {
                        effect: undet_effect(),
                        value: Box::new(DemandSignature::Fun {
                            param: Box::new(int_signature()),
                            ret: Box::new(unit_thunk()),
                        }),
                    }),
                }),
            }
        );
    }

    #[test]
    fn fold_demand_closes_range_item_as_int() {
        let demand = Demand::with_signature(
            path_segments(&["std", "range", "&impl#120", "fold"]),
            RuntimeType::core(core_ir::Type::Any),
            curried_signatures(
                &[
                    DemandSignature::Core(DemandCoreType::Named {
                        path: path_segments(&["std", "range", "range"]),
                        args: Vec::new(),
                    }),
                    unit_signature(),
                    DemandSignature::Fun {
                        param: Box::new(DemandSignature::Hole(0)),
                        ret: Box::new(DemandSignature::Fun {
                            param: Box::new(DemandSignature::Hole(0)),
                            ret: Box::new(unit_thunk()),
                        }),
                    },
                ],
                unit_thunk(),
            ),
        );

        let DemandSignature::Fun { ret, .. } = demand.key.signature else {
            panic!("expected fold function");
        };
        let DemandSignature::Fun { ret, .. } = *ret else {
            panic!("expected z function");
        };
        let DemandSignature::Fun { param, .. } = *ret else {
            panic!("expected callback function");
        };

        assert_eq!(
            *param,
            DemandSignature::Fun {
                param: Box::new(unit_signature()),
                ret: Box::new(DemandSignature::Thunk {
                    effect: undet_effect(),
                    value: Box::new(DemandSignature::Fun {
                        param: Box::new(int_signature()),
                        ret: Box::new(unit_thunk()),
                    }),
                }),
            }
        );
    }

    #[test]
    fn for_in_demand_marks_callback_result_as_ignored() {
        let demand = Demand::with_signature(
            path_segments(&["std", "flow", "loop", "for_in"]),
            RuntimeType::core(core_ir::Type::Any),
            curried_signatures(
                &[
                    DemandSignature::Core(DemandCoreType::Named {
                        path: path_segments(&["std", "range", "range"]),
                        args: Vec::new(),
                    }),
                    DemandSignature::Fun {
                        param: Box::new(DemandSignature::Hole(0)),
                        ret: Box::new(DemandSignature::Thunk {
                            effect: DemandEffect::Atom(DemandCoreType::Named {
                                path: path_segments(&["std", "flow", "loop"]),
                                args: Vec::new(),
                            }),
                            value: Box::new(DemandSignature::Hole(1)),
                        }),
                    },
                ],
                DemandSignature::Thunk {
                    effect: DemandEffect::Empty,
                    value: Box::new(unit_signature()),
                },
            ),
        );

        let DemandSignature::Fun { ret, .. } = demand.key.signature else {
            panic!("expected for_in function");
        };
        let DemandSignature::Fun { param, .. } = *ret else {
            panic!("expected callback argument");
        };

        assert_eq!(
            *param,
            DemandSignature::Fun {
                param: Box::new(int_signature()),
                ret: Box::new(DemandSignature::Thunk {
                    effect: DemandEffect::Atom(DemandCoreType::Named {
                        path: path_segments(&["std", "flow", "loop"]),
                        args: Vec::new(),
                    }),
                    value: Box::new(DemandSignature::Ignored),
                }),
            }
        );
    }

    fn fold_signature(callback: DemandSignature) -> DemandSignature {
        curried_signatures(
            &[
                DemandSignature::Core(DemandCoreType::Named {
                    path: path_segments(&["std", "list", "list"]),
                    args: vec![DemandTypeArg::Type(DemandCoreType::Named {
                        path: path("int"),
                        args: Vec::new(),
                    })],
                }),
                unit_signature(),
                callback,
            ],
            unit_thunk(),
        )
    }

    fn unit_thunk() -> DemandSignature {
        DemandSignature::Thunk {
            effect: undet_effect(),
            value: Box::new(unit_signature()),
        }
    }

    fn undet_effect() -> DemandEffect {
        DemandEffect::Atom(DemandCoreType::Named {
            path: path_segments(&["std", "undet", "undet"]),
            args: Vec::new(),
        })
    }

    fn unit_signature() -> DemandSignature {
        DemandSignature::Core(DemandCoreType::Named {
            path: path("unit"),
            args: Vec::new(),
        })
    }

    fn int_signature() -> DemandSignature {
        DemandSignature::Core(DemandCoreType::Named {
            path: path("int"),
            args: Vec::new(),
        })
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }

    fn path_segments(segments: &[&str]) -> core_ir::Path {
        core_ir::Path {
            segments: segments
                .iter()
                .map(|segment| core_ir::Name((*segment).to_string()))
                .collect(),
        }
    }
}
