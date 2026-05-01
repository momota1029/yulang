//! Demand-driven monomorphization prototype.
//!
//! This module is intentionally not wired into the compiler path yet.  It is
//! the new algorithmic core being built beside the fixed-point monomorphizer:
//! concrete use sites create demands, demands are deduplicated by a runtime
//! signature, and `_` / `Any` becomes a monomorphization hole instead of a VM
//! type witness.

use std::collections::{HashMap, HashSet, VecDeque};

use yulang_core_ir as core_ir;

use crate::ir::Type as RuntimeType;

mod check;
mod collect;
mod emit;
mod engine;
mod solve;
mod specialize;

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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DemandCoreType {
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

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }
}
