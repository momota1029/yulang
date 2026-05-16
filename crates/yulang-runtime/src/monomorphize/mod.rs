//! Monomorphization and specialization.
//!
//! The default path is principal-elaboration based: it inlines polymorphic
//! wrappers, elaborates principal types, refreshes closed schemes, and prunes
//! unreachable bindings.
//!
//! The legacy demand-driven fixpoint path is retained for comparison and debug,
//! enabled by setting `YULANG_LEGACY_MONO_FIXPOINT`.  In that path, concrete
//! use sites create demands, demands are deduplicated by runtime signature, and
//! `_` / `Any` becomes a monomorphization hole instead of a VM type witness.

use std::collections::{BTreeMap, HashMap};

use yulang_typed_ir as typed_ir;

use crate::ir::{Expr, ExprKind, RecordSpreadExpr, Stmt, Type as RuntimeType};
use crate::types::substitute_type;

mod associated;
mod check;
mod collect;
mod demand_profile;
mod demand_queue;
mod emit;
mod engine;
mod pipeline;
mod semantics;
mod solve;
mod specialize;

use associated::*;
pub use check::*;
pub use collect::*;
use demand_profile::DEMAND_EVIDENCE_PROFILE;
pub use demand_profile::DemandEvidenceProfile;
pub(crate) use demand_profile::{reset_demand_evidence_profile, snapshot_demand_evidence_profile};
pub use demand_queue::{DemandQueue, DemandQueueProfile};
pub use emit::*;
pub use engine::*;
pub use pipeline::{
    MonomorphizeMode, MonomorphizePassProfile, MonomorphizeProfile, MonomorphizeProgress,
    SubstitutionSpecializeInferenceCount, SubstitutionSpecializeMissingVarCount,
    SubstitutionSpecializeProfile, SubstitutionSpecializeRewriteContextCount,
    SubstitutionSpecializeRewriteExprKindTiming, SubstitutionSpecializeRewritePhaseTiming,
    SubstitutionSpecializeSkipCount, SubstitutionSpecializeTargetInferences,
    SubstitutionSpecializeTargetRewrites, SubstitutionSpecializeTargetSkips, monomorphize_module,
    monomorphize_module_profiled,
};
use semantics::*;
pub use solve::*;
pub use specialize::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Demand {
    pub target: typed_ir::Path,
    pub expected: RuntimeType,
    pub key: DemandKey,
}

impl Demand {
    pub fn new(target: typed_ir::Path, expected: RuntimeType) -> Self {
        Self::new_with_semantics(&DemandSemantics::default(), target, expected)
    }

    pub(super) fn new_with_semantics(
        semantics: &DemandSemantics,
        target: typed_ir::Path,
        expected: RuntimeType,
    ) -> Self {
        let key = DemandKey::new(target.clone(), &expected);
        let key = DemandKey::from_signature(
            target.clone(),
            pass_through_associated_type_signature(semantics, &target, key.signature),
        );
        Self {
            target,
            expected,
            key,
        }
    }

    pub fn with_signature(
        target: typed_ir::Path,
        expected: RuntimeType,
        signature: DemandSignature,
    ) -> Self {
        Self::with_signature_and_semantics(&DemandSemantics::default(), target, expected, signature)
    }

    pub(super) fn with_signature_and_semantics(
        semantics: &DemandSemantics,
        target: typed_ir::Path,
        expected: RuntimeType,
        signature: DemandSignature,
    ) -> Self {
        let signature =
            pass_through_associated_type_signature(semantics, &target, signature);
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
    pub target: typed_ir::Path,
    pub signature: DemandSignature,
}

impl DemandKey {
    pub fn new(target: typed_ir::Path, expected: &RuntimeType) -> Self {
        Self {
            target,
            signature: DemandSignature::from_runtime_type(expected).canonicalize_holes(),
        }
    }

    pub fn from_signature(target: typed_ir::Path, signature: DemandSignature) -> Self {
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
    pub fn from_core_type(ty: &typed_ir::Type) -> Self {
        let mut next_hole = 0;
        Self::from_core_type_with_holes(ty, &mut next_hole)
    }

    pub fn from_core_type_with_holes(ty: &typed_ir::Type, next_hole: &mut u32) -> Self {
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
        path: typed_ir::Path,
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
        var: typed_ir::TypeVar,
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
                normalize_canonical_effect_row(items.iter().map(|item| self.effect(item)).collect())
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

fn normalize_canonical_effect_row(items: Vec<DemandEffect>) -> DemandEffect {
    let mut out = Vec::new();
    for item in items {
        push_canonical_effect_item(item, &mut out);
    }
    out.sort_by_key(canonical_effect_key);
    out.dedup();
    match out.as_slice() {
        [] => DemandEffect::Empty,
        [item] => item.clone(),
        _ => DemandEffect::Row(out),
    }
}

pub(super) fn merge_demand_effects(left: DemandEffect, right: DemandEffect) -> DemandEffect {
    normalize_canonical_effect_row(vec![left, right])
}

fn push_canonical_effect_item(item: DemandEffect, out: &mut Vec<DemandEffect>) {
    match item {
        DemandEffect::Empty => {}
        DemandEffect::Row(items) => {
            for item in items {
                push_canonical_effect_item(item, out);
            }
        }
        item if demand_effect_is_impossible(&item) => {}
        item => out.push(item),
    }
}

pub(super) fn demand_effect_is_impossible(effect: &DemandEffect) -> bool {
    match effect {
        DemandEffect::Atom(DemandCoreType::Named { args, .. }) => {
            args.iter().any(demand_type_arg_is_never)
        }
        DemandEffect::Row(items) => items.iter().all(demand_effect_is_impossible),
        DemandEffect::Empty => true,
        DemandEffect::Hole(_) | DemandEffect::Atom(_) => false,
    }
}

fn demand_type_arg_is_never(arg: &DemandTypeArg) -> bool {
    match arg {
        DemandTypeArg::Type(ty) => demand_core_is_never(ty),
        DemandTypeArg::Bounds { lower, upper } => lower
            .as_ref()
            .or(upper.as_ref())
            .is_some_and(demand_core_is_never),
    }
}

fn demand_core_is_never(ty: &DemandCoreType) -> bool {
    matches!(ty, DemandCoreType::Never)
}

fn canonical_effect_key(effect: &DemandEffect) -> String {
    match effect {
        DemandEffect::Empty => "0:".to_string(),
        DemandEffect::Hole(id) => format!("1:{id}"),
        DemandEffect::Atom(ty) => format!("2:{}", canonical_core_key(ty)),
        DemandEffect::Row(items) => {
            let mut keys = items.iter().map(canonical_effect_key).collect::<Vec<_>>();
            keys.sort();
            format!("3:{}", keys.join(";"))
        }
    }
}

fn canonical_core_key(ty: &DemandCoreType) -> String {
    match ty {
        DemandCoreType::Any => "any".to_string(),
        DemandCoreType::Never => "never".to_string(),
        DemandCoreType::Hole(id) => format!("hole:{id}"),
        DemandCoreType::Named { path, args } => format!(
            "named:{}<{}>",
            canonical_path_key(path),
            args.iter()
                .map(canonical_type_arg_key)
                .collect::<Vec<_>>()
                .join(",")
        ),
        DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => format!(
            "fun({};{})->({};{})",
            canonical_core_key(param),
            canonical_effect_key(param_effect),
            canonical_effect_key(ret_effect),
            canonical_core_key(ret)
        ),
        DemandCoreType::Tuple(items) => format!(
            "tuple({})",
            items
                .iter()
                .map(canonical_core_key)
                .collect::<Vec<_>>()
                .join(",")
        ),
        DemandCoreType::Record(fields) => format!(
            "record({})",
            fields
                .iter()
                .map(|field| format!(
                    "{}:{}:{}",
                    field.name.0,
                    field.optional,
                    canonical_core_key(&field.value)
                ))
                .collect::<Vec<_>>()
                .join(",")
        ),
        DemandCoreType::Variant(cases) => format!(
            "variant({})",
            cases
                .iter()
                .map(|case| format!(
                    "{}({})",
                    case.name.0,
                    case.payloads
                        .iter()
                        .map(canonical_core_key)
                        .collect::<Vec<_>>()
                        .join(",")
                ))
                .collect::<Vec<_>>()
                .join("|")
        ),
        DemandCoreType::RowAsValue(items) => format!(
            "row-value({})",
            items
                .iter()
                .map(canonical_effect_key)
                .collect::<Vec<_>>()
                .join(";")
        ),
        DemandCoreType::Union(items) => format!(
            "union({})",
            items
                .iter()
                .map(canonical_core_key)
                .collect::<Vec<_>>()
                .join("|")
        ),
        DemandCoreType::Inter(items) => format!(
            "inter({})",
            items
                .iter()
                .map(canonical_core_key)
                .collect::<Vec<_>>()
                .join("&")
        ),
        DemandCoreType::Recursive { var, body } => {
            format!("rec({}.{})", var.0, canonical_core_key(body))
        }
    }
}

fn canonical_type_arg_key(arg: &DemandTypeArg) -> String {
    match arg {
        DemandTypeArg::Type(ty) => canonical_core_key(ty),
        DemandTypeArg::Bounds { lower, upper } => format!(
            "bounds({};{})",
            lower
                .as_ref()
                .map(canonical_core_key)
                .unwrap_or_else(|| "_".to_string()),
            upper
                .as_ref()
                .map(canonical_core_key)
                .unwrap_or_else(|| "_".to_string())
        ),
    }
}

fn canonical_path_key(path: &typed_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DemandRecordField {
    pub name: typed_ir::Name,
    pub value: DemandCoreType,
    pub optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DemandVariantCase {
    pub name: typed_ir::Name,
    pub payloads: Vec<DemandCoreType>,
}

#[derive(Debug, Default)]
struct SignatureBuilder {
    next_hole: u32,
}

impl SignatureBuilder {
    fn runtime_type(&mut self, ty: &RuntimeType) -> DemandSignature {
        match ty {
            RuntimeType::Unknown => DemandSignature::Hole(self.fresh_hole()),
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

    fn core_type(&mut self, ty: &typed_ir::Type) -> DemandCoreType {
        match ty {
            typed_ir::Type::Never => DemandCoreType::Never,
            typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => {
                DemandCoreType::Hole(self.fresh_hole())
            }
            typed_ir::Type::Named { path, args } => DemandCoreType::Named {
                path: path.clone(),
                args: args.iter().map(|arg| self.type_arg(arg)).collect(),
            },
            typed_ir::Type::Fun {
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
            typed_ir::Type::Tuple(items) => {
                DemandCoreType::Tuple(items.iter().map(|item| self.core_type(item)).collect())
            }
            typed_ir::Type::Record(record) => DemandCoreType::Record(
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
            typed_ir::Type::Variant(variant) => DemandCoreType::Variant(
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
            typed_ir::Type::Row { items, tail } => {
                let mut row = items
                    .iter()
                    .map(|item| self.effect_type(item))
                    .collect::<Vec<_>>();
                row.push(self.effect_type(tail));
                DemandCoreType::RowAsValue(row)
            }
            typed_ir::Type::Union(items) => {
                DemandCoreType::Union(items.iter().map(|item| self.core_type(item)).collect())
            }
            typed_ir::Type::Inter(items) => {
                DemandCoreType::Inter(items.iter().map(|item| self.core_type(item)).collect())
            }
            typed_ir::Type::Recursive { var, body } => DemandCoreType::Recursive {
                var: var.clone(),
                body: Box::new(self.core_type(body)),
            },
        }
    }

    fn effect_type(&mut self, ty: &typed_ir::Type) -> DemandEffect {
        match ty {
            typed_ir::Type::Never => DemandEffect::Empty,
            typed_ir::Type::Any | typed_ir::Type::Var(_) => DemandEffect::Hole(self.fresh_hole()),
            typed_ir::Type::Row { items, tail } => {
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

    fn type_arg(&mut self, arg: &typed_ir::TypeArg) -> DemandTypeArg {
        match arg {
            typed_ir::TypeArg::Type(ty) => DemandTypeArg::Type(self.core_type(ty)),
            typed_ir::TypeArg::Bounds(bounds) => DemandTypeArg::Bounds {
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

/// DFS reachability walk from module roots.
///
/// Returns every binding path reachable from the module's root expressions and
/// `Root::Binding` entries.  Suitable for both pruning and filtering passes.
pub(super) fn reachable_binding_paths(
    module: &crate::ir::Module,
) -> std::collections::HashSet<typed_ir::Path> {
    let bodies: std::collections::HashMap<typed_ir::Path, &Expr> = module
        .bindings
        .iter()
        .map(|b| (b.name.clone(), &b.body))
        .collect();
    let mut reachable = std::collections::HashSet::new();
    let mut stack = Vec::new();
    for root in &module.roots {
        if let crate::ir::Root::Binding(path) = root {
            stack.push(path.clone());
        }
    }
    for expr in &module.root_exprs {
        collect_expr_refs(expr, &mut stack);
    }
    while let Some(path) = stack.pop() {
        if !reachable.insert(path.clone()) {
            continue;
        }
        if let Some(body) = bodies.get(&path) {
            collect_expr_refs(body, &mut stack);
        }
    }
    reachable
}

pub(super) fn collect_expr_refs(expr: &Expr, out: &mut Vec<typed_ir::Path>) {
    match &expr.kind {
        ExprKind::Var(path) => out.push(path.clone()),
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => collect_expr_refs(body, out),
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_refs(callee, out);
            collect_expr_refs(arg, out);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_refs(cond, out);
            collect_expr_refs(then_branch, out);
            collect_expr_refs(else_branch, out);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_refs(item, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_refs(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_expr_refs(expr, out);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_refs(value, out);
            }
        }
        ExprKind::Select { base, .. } => collect_expr_refs(base, out),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_refs(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_refs(stmt, out);
            }
            if let Some(tail) = tail {
                collect_expr_refs(tail, out);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_refs(body, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

pub(super) fn collect_stmt_refs(stmt: &Stmt, out: &mut Vec<typed_ir::Path>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_refs(value, out);
        }
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

pub(super) fn return_effect_from_args(
    ret: DemandSignature,
    args: &[DemandSignature],
) -> DemandSignature {
    args.iter()
        .rev()
        .find_map(|arg| effectful_return_matching_value(arg, &ret))
        .unwrap_or(ret)
}

fn effectful_return_matching_value(
    signature: &DemandSignature,
    value: &DemandSignature,
) -> Option<DemandSignature> {
    match signature {
        DemandSignature::Fun { ret, .. } => effectful_return_matching_value(ret, value),
        DemandSignature::Thunk {
            effect,
            value: thunk_value,
        } if DemandUnifier::new()
            .unify_signature(value, thunk_value)
            .is_ok() =>
        {
            Some(DemandSignature::Thunk {
                effect: effect.clone(),
                value: thunk_value.clone(),
            })
        }
        DemandSignature::Core(DemandCoreType::Fun {
            ret_effect, ret, ..
        }) if !matches!(ret_effect.as_ref(), DemandEffect::Empty)
            && DemandUnifier::new()
                .unify_signature(value, &DemandSignature::Core(ret.as_ref().clone()))
                .is_ok() =>
        {
            Some(DemandSignature::Thunk {
                effect: ret_effect.as_ref().clone(),
                value: Box::new(DemandSignature::Core(ret.as_ref().clone())),
            })
        }
        _ => None,
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
    evidence: &typed_ir::ApplyEvidence,
    fallback: DemandSignature,
) -> DemandSignature {
    let Some(evidence) = apply_evidence_signature(evidence) else {
        return fallback;
    };
    merge_signature_hint(fallback, evidence)
}

pub(super) fn apply_evidence_callee_signature(
    evidence: &typed_ir::ApplyEvidence,
) -> Option<DemandSignature> {
    apply_evidence_callee_type(evidence)
        .map(|ty| DemandSignature::from_runtime_type(&RuntimeType::core(ty)))
}

pub(super) fn apply_evidence_substituted_callee_signature(
    evidence: &typed_ir::ApplyEvidence,
) -> Option<DemandSignature> {
    apply_evidence_substituted_callee_type(evidence)
        .map(|ty| DemandSignature::from_runtime_type(&RuntimeType::core(ty)))
}

pub(super) fn apply_evidence_arg_signature(
    evidence: &typed_ir::ApplyEvidence,
) -> Option<DemandSignature> {
    apply_evidence_arg_signature_with_expected_arg(
        evidence,
        std::env::var_os("YULANG_USE_EXPECTED_ARG_EVIDENCE").is_some(),
    )
}

pub(super) fn apply_evidence_arg_signature_with_expected_arg(
    evidence: &typed_ir::ApplyEvidence,
    use_expected_arg: bool,
) -> Option<DemandSignature> {
    DEMAND_EVIDENCE_PROFILE.fetch_add_apply_arg_signature_calls();
    if !use_expected_arg {
        DEMAND_EVIDENCE_PROFILE.fetch_add_expected_arg_hint_disabled();
    } else if let Some(bounds) = evidence.expected_arg.as_ref() {
        DEMAND_EVIDENCE_PROFILE.fetch_add_expected_arg_hint_present();
        if let Some(ty) = evidence_bounds_type(bounds) {
            DEMAND_EVIDENCE_PROFILE.fetch_add_expected_arg_hint_converted();
            let signature = DemandSignature::from_runtime_type(&RuntimeType::core(ty.clone()));
            if signature.is_closed() {
                DEMAND_EVIDENCE_PROFILE.fetch_add_expected_arg_hint_used();
                let fallback = evidence_bounds_type(&evidence.arg)
                    .map(|ty| DemandSignature::from_runtime_type(&RuntimeType::core(ty.clone())));
                if fallback.as_ref() == Some(&signature) {
                    DEMAND_EVIDENCE_PROFILE.fetch_add_expected_arg_hint_same_signature();
                } else {
                    DEMAND_EVIDENCE_PROFILE.fetch_add_expected_arg_hint_changed_signature();
                }
                return Some(signature);
            }
            DEMAND_EVIDENCE_PROFILE.fetch_add_expected_arg_hint_rejected_open();
        }
    }
    evidence_bounds_type(&evidence.arg)
        .map(|ty| DemandSignature::from_runtime_type(&RuntimeType::core(ty.clone())))
}

pub(super) fn apply_evidence_param_signature(
    evidence: &typed_ir::ApplyEvidence,
) -> Option<DemandSignature> {
    let arg = apply_evidence_arg_signature(evidence);
    let callee = apply_evidence_expected_callee_param_signature(
        evidence,
        std::env::var_os("YULANG_USE_EXPECTED_CALLEE_EVIDENCE").is_some(),
    );
    match (arg, callee) {
        (Some(arg), Some(callee)) => Some(merge_signature_hint(arg, callee)),
        (Some(arg), None) => Some(arg),
        (None, Some(callee)) => Some(callee),
        (None, None) => None,
    }
}

pub(super) fn apply_evidence_expected_callee_param_signature(
    evidence: &typed_ir::ApplyEvidence,
    use_expected_callee: bool,
) -> Option<DemandSignature> {
    DEMAND_EVIDENCE_PROFILE.fetch_add_apply_callee_signature_calls();
    if !use_expected_callee {
        DEMAND_EVIDENCE_PROFILE.fetch_add_expected_callee_hint_disabled();
        return None;
    }
    let Some(bounds) = evidence.expected_callee.as_ref() else {
        return None;
    };
    DEMAND_EVIDENCE_PROFILE.fetch_add_expected_callee_hint_present();
    let Some(ty) = evidence_bounds_type(bounds) else {
        return None;
    };
    DEMAND_EVIDENCE_PROFILE.fetch_add_expected_callee_hint_converted();
    let typed_ir::Type::Fun { param, .. } = ty else {
        DEMAND_EVIDENCE_PROFILE.fetch_add_expected_callee_hint_rejected_non_function();
        return None;
    };
    let signature = DemandSignature::from_runtime_type(&RuntimeType::core(param.as_ref().clone()));
    if !signature.is_closed() {
        DEMAND_EVIDENCE_PROFILE.fetch_add_expected_callee_hint_rejected_open();
        return None;
    }
    DEMAND_EVIDENCE_PROFILE.fetch_add_expected_callee_hint_used();
    let fallback = evidence_bounds_type(&evidence.arg)
        .map(|ty| DemandSignature::from_runtime_type(&RuntimeType::core(ty.clone())));
    if fallback.as_ref() == Some(&signature) {
        DEMAND_EVIDENCE_PROFILE.fetch_add_expected_callee_hint_same_param_signature();
    } else {
        DEMAND_EVIDENCE_PROFILE.fetch_add_expected_callee_hint_changed_param_signature();
    }
    Some(signature)
}

fn apply_evidence_signature(evidence: &typed_ir::ApplyEvidence) -> Option<DemandSignature> {
    if let Some(typed_ir::Type::Fun {
        ret_effect, ret, ..
    }) = apply_evidence_callee_type(evidence)
    {
        let mut next_hole = 0;
        let ret = DemandSignature::from_runtime_type_with_holes(
            &RuntimeType::core(ret.as_ref().clone()),
            &mut next_hole,
        );
        let ret_effect = DemandEffect::from_core_type_with_holes(&ret_effect, &mut next_hole);
        return Some(effected_core_signature(
            signature_core_value(&ret),
            ret_effect,
        ));
    }
    evidence_bounds_type(&evidence.result)
        .map(|ty| DemandSignature::from_runtime_type(&RuntimeType::core(ty.clone())))
}

fn evidence_bounds_type(bounds: &typed_ir::TypeBounds) -> Option<&typed_ir::Type> {
    bounds.lower.as_deref().or(bounds.upper.as_deref())
}

fn apply_evidence_callee_type(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    if let Some(callee) = apply_evidence_substituted_callee_type(evidence) {
        return Some(callee);
    }
    evidence_bounds_type(&evidence.callee).cloned()
}

fn apply_evidence_substituted_callee_type(
    evidence: &typed_ir::ApplyEvidence,
) -> Option<typed_ir::Type> {
    if std::env::var_os("YULANG_USE_APPLY_SUBSTITUTIONS").is_none() {
        return None;
    }
    let principal_callee = evidence.principal_callee.as_ref()?;
    if evidence.substitutions.is_empty() {
        return None;
    }
    let substitutions = evidence
        .substitutions
        .iter()
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect::<BTreeMap<_, _>>();
    Some(substitute_type(principal_callee, &substitutions))
}

pub(super) fn merge_signature_hint(
    fallback: DemandSignature,
    hint: DemandSignature,
) -> DemandSignature {
    let Ok(substitutions) = DemandUnifier::new().unify_signature(&fallback, &hint) else {
        return merge_actual_effects_into_hint(fallback, &hint);
    };
    substitutions.apply_signature(&fallback)
}

fn merge_actual_effects_into_hint(
    hint: DemandSignature,
    actual: &DemandSignature,
) -> DemandSignature {
    match (hint, actual) {
        (
            DemandSignature::Fun { param, ret },
            DemandSignature::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => DemandSignature::Fun {
            param: Box::new(merge_actual_effects_into_hint(*param, actual_param)),
            ret: Box::new(merge_actual_effects_into_hint(*ret, actual_ret)),
        },
        (
            DemandSignature::Thunk { effect, value },
            DemandSignature::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) => DemandSignature::Thunk {
            effect: merge_empty_effect_hint(effect, actual_effect),
            value: Box::new(merge_actual_effects_into_hint(*value, actual_value)),
        },
        (DemandSignature::Thunk { effect, value }, actual) if effect_is_empty_hint(&effect) => {
            DemandSignature::Thunk {
                effect,
                value: Box::new(merge_actual_effects_into_hint(*value, actual)),
            }
        }
        (DemandSignature::Core(hint), actual) => DemandSignature::Core(
            merge_actual_core_effects_into_hint(hint, &signature_core_value(actual)),
        ),
        (hint, DemandSignature::Thunk { value, .. }) => merge_actual_effects_into_hint(hint, value),
        (hint, _) => hint,
    }
}

fn merge_actual_core_effects_into_hint(
    hint: DemandCoreType,
    actual: &DemandCoreType,
) -> DemandCoreType {
    match (hint, actual) {
        (
            DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            DemandCoreType::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => DemandCoreType::Fun {
            param: Box::new(merge_actual_core_effects_into_hint(*param, actual_param)),
            param_effect: Box::new(merge_empty_effect_hint(*param_effect, actual_param_effect)),
            ret_effect: Box::new(merge_empty_effect_hint(*ret_effect, actual_ret_effect)),
            ret: Box::new(merge_actual_core_effects_into_hint(*ret, actual_ret)),
        },
        (hint, _) => hint,
    }
}

fn merge_empty_effect_hint(hint: DemandEffect, actual: &DemandEffect) -> DemandEffect {
    match (&hint, actual) {
        (hint, actual) if effect_is_empty_hint(hint) && !effect_is_empty_hint(actual) => {
            actual.clone()
        }
        _ => hint,
    }
}

fn effect_is_empty_hint(effect: &DemandEffect) -> bool {
    match effect {
        DemandEffect::Empty => true,
        DemandEffect::Row(items) => items.iter().all(effect_is_empty_hint),
        DemandEffect::Hole(_) | DemandEffect::Atom(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn demand_signature_turns_any_value_into_hole() {
        let ty = RuntimeType::fun(
            RuntimeType::core(typed_ir::Type::Any),
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
        let ty = RuntimeType::thunk(typed_ir::Type::Any, RuntimeType::core(typed_ir::Type::Any));

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

        assert!(queue.push(target.clone(), RuntimeType::core(typed_ir::Type::Any)));
        assert!(!queue.push(target, RuntimeType::core(typed_ir::Type::Any)));
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
    fn demand_queue_drops_open_demand_after_closed_target_demand() {
        let mut queue = DemandQueue::default();
        let target = path("id");

        assert!(queue.push(target.clone(), RuntimeType::core(named("int"))));
        assert!(!queue.push(target, RuntimeType::core(typed_ir::Type::Any)));
        assert_eq!(queue.len(), 1);
    }

    #[test]
    fn demand_queue_keeps_open_demand_not_covered_by_closed_target_demand() {
        let mut queue = DemandQueue::default();
        let target = path("id");

        assert!(queue.push(target.clone(), RuntimeType::core(named("int"))));
        assert!(queue.push(
            target,
            RuntimeType::fun(
                RuntimeType::core(named("bool")),
                RuntimeType::core(typed_ir::Type::Any),
            )
        ));
        assert_eq!(queue.len(), 2);
    }

    #[test]
    fn demand_signature_can_continue_hole_numbering() {
        let first = RuntimeType::fun(
            RuntimeType::core(typed_ir::Type::Any),
            RuntimeType::core(typed_ir::Type::Any),
        );
        let mut next_hole = 0;
        let first = DemandSignature::from_runtime_type_with_holes(&first, &mut next_hole);
        let second = DemandSignature::from_runtime_type_with_holes(
            &RuntimeType::core(typed_ir::Type::Any),
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
    fn merge_signature_hint_preserves_actual_effects_inside_empty_thunks() {
        let unit = unit_signature();
        let int = int_signature();
        let effect = DemandEffect::Atom(DemandCoreType::Named {
            path: path_segments(&["std", "junction", "junction"]),
            args: Vec::new(),
        });
        let hint = DemandSignature::Thunk {
            effect: DemandEffect::Empty,
            value: Box::new(curried_signatures(
                &[unit.clone(), int.clone()],
                DemandSignature::Thunk {
                    effect: DemandEffect::Empty,
                    value: Box::new(unit.clone()),
                },
            )),
        };
        let actual = curried_signatures(
            &[unit.clone(), int],
            DemandSignature::Thunk {
                effect: effect.clone(),
                value: Box::new(unit.clone()),
            },
        );

        let merged = merge_signature_hint(hint, actual);

        assert_eq!(
            merged,
            DemandSignature::Thunk {
                effect: DemandEffect::Empty,
                value: Box::new(curried_signatures(
                    &[unit.clone(), int_signature()],
                    DemandSignature::Thunk {
                        effect,
                        value: Box::new(unit),
                    },
                )),
            }
        );
    }

    #[test]
    fn apply_evidence_arg_signature_can_use_closed_expected_arg_opt_in() {
        let evidence = typed_ir::ApplyEvidence {
            callee_source_edge: None,
            expected_callee: None,
            arg_source_edge: Some(1),
            callee: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
            arg: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
            expected_arg: Some(typed_ir::TypeBounds::exact(named("int"))),
            result: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        };

        assert_eq!(
            apply_evidence_arg_signature_with_expected_arg(&evidence, false),
            Some(DemandSignature::Hole(0)),
        );
        assert_eq!(
            apply_evidence_arg_signature_with_expected_arg(&evidence, true),
            Some(int_signature()),
        );
    }

    #[test]
    fn apply_evidence_arg_signature_ignores_open_expected_arg() {
        let evidence = typed_ir::ApplyEvidence {
            callee_source_edge: None,
            expected_callee: None,
            arg_source_edge: Some(1),
            callee: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
            arg: typed_ir::TypeBounds::exact(named("str")),
            expected_arg: Some(typed_ir::TypeBounds::exact(typed_ir::Type::Any)),
            result: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        };

        assert_eq!(
            apply_evidence_arg_signature_with_expected_arg(&evidence, true),
            Some(DemandSignature::Core(DemandCoreType::Named {
                path: path("str"),
                args: Vec::new(),
            })),
        );
    }

    #[test]
    fn apply_evidence_param_signature_can_use_closed_expected_callee_opt_in() {
        let evidence = typed_ir::ApplyEvidence {
            callee_source_edge: Some(2),
            expected_callee: Some(typed_ir::TypeBounds::exact(typed_ir::Type::Fun {
                param: Box::new(named("int")),
                param_effect: Box::new(typed_ir::Type::Never),
                ret_effect: Box::new(typed_ir::Type::Never),
                ret: Box::new(named("str")),
            })),
            arg_source_edge: None,
            callee: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
            arg: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
            expected_arg: None,
            result: typed_ir::TypeBounds::exact(typed_ir::Type::Any),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        };

        assert_eq!(
            apply_evidence_expected_callee_param_signature(&evidence, false),
            None,
        );
        assert_eq!(
            apply_evidence_expected_callee_param_signature(&evidence, true),
            Some(int_signature()),
        );
    }

    #[test]
    fn merge_demand_effects_drops_impossible_never_payload_effects() {
        let sub_never = DemandEffect::Atom(DemandCoreType::Named {
            path: path_segments(&["std", "flow", "sub"]),
            args: vec![DemandTypeArg::Type(DemandCoreType::Never)],
        });
        let sub_int = DemandEffect::Atom(DemandCoreType::Named {
            path: path_segments(&["std", "flow", "sub"]),
            args: vec![DemandTypeArg::Type(DemandCoreType::Named {
                path: path("int"),
                args: Vec::new(),
            })],
        });

        assert_eq!(merge_demand_effects(sub_never, sub_int.clone()), sub_int);
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
    fn demand_keys_canonicalize_effect_row_order() {
        let target = path("effectful");
        let io = DemandEffect::Atom(DemandCoreType::Named {
            path: path("io"),
            args: Vec::new(),
        });
        let undet = DemandEffect::Atom(DemandCoreType::Named {
            path: path("undet"),
            args: Vec::new(),
        });
        let left = DemandKey::from_signature(
            target.clone(),
            DemandSignature::Thunk {
                effect: DemandEffect::Row(vec![io.clone(), undet.clone()]),
                value: Box::new(DemandSignature::Core(DemandCoreType::Never)),
            },
        );
        let right = DemandKey::from_signature(
            target,
            DemandSignature::Thunk {
                effect: DemandEffect::Row(vec![undet, io]),
                value: Box::new(DemandSignature::Core(DemandCoreType::Never)),
            },
        );

        assert_eq!(left, right);
    }

    #[test]
    fn demand_keys_canonicalize_singleton_effect_rows() {
        let target = path("effectful");
        let io = DemandEffect::Atom(DemandCoreType::Named {
            path: path("io"),
            args: Vec::new(),
        });
        let left = DemandKey::from_signature(
            target.clone(),
            DemandSignature::Thunk {
                effect: DemandEffect::Row(vec![io.clone()]),
                value: Box::new(DemandSignature::Core(DemandCoreType::Never)),
            },
        );
        let right = DemandKey::from_signature(
            target,
            DemandSignature::Thunk {
                effect: io,
                value: Box::new(DemandSignature::Core(DemandCoreType::Never)),
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
    fn add_named_user_binding_does_not_receive_list_merge_signature_closure() {
        let list_int = DemandSignature::Core(DemandCoreType::Named {
            path: path_segments(&["std", "list", "list"]),
            args: vec![DemandTypeArg::Type(DemandCoreType::Named {
                path: path("int"),
                args: Vec::new(),
            })],
        });
        let original = curried_signatures(
            &[list_int, DemandSignature::Hole(0)],
            DemandSignature::Hole(1),
        );

        let demand = Demand::with_signature(
            path_segments(&["user", "math", "add"]),
            RuntimeType::core(typed_ir::Type::Any),
            original.clone(),
        );

        assert_eq!(demand.key.signature, original);
    }

    #[test]
    fn fold_named_user_binding_does_not_receive_fold_signature_closure() {
        let original = fold_signature(DemandSignature::Fun {
            param: Box::new(DemandSignature::Hole(0)),
            ret: Box::new(DemandSignature::Fun {
                param: Box::new(DemandSignature::Hole(1)),
                ret: Box::new(unit_thunk()),
            }),
        });

        let demand = Demand::with_signature(
            path_segments(&["user", "container", "fold"]),
            RuntimeType::core(typed_ir::Type::Any),
            original.clone(),
        );

        assert_eq!(demand.key.signature, original);
    }

    #[test]
    fn fold_impl_named_user_binding_does_not_receive_fold_signature_closure() {
        let original = fold_signature(DemandSignature::Fun {
            param: Box::new(DemandSignature::Hole(0)),
            ret: Box::new(DemandSignature::Fun {
                param: Box::new(DemandSignature::Hole(1)),
                ret: Box::new(unit_thunk()),
            }),
        });

        let demand = Demand::with_signature(
            path_segments(&["user", "list", "fold_impl"]),
            RuntimeType::core(typed_ir::Type::Any),
            original.clone(),
        );

        assert_eq!(demand.key.signature, original);
    }

    #[test]
    fn find_named_user_binding_does_not_receive_fold_find_signature_closure() {
        let list_int = DemandSignature::Core(DemandCoreType::Named {
            path: path_segments(&["std", "list", "list"]),
            args: vec![DemandTypeArg::Type(DemandCoreType::Named {
                path: path("int"),
                args: Vec::new(),
            })],
        });
        let opt_int = DemandSignature::Core(DemandCoreType::Named {
            path: path_segments(&["std", "opt", "opt"]),
            args: vec![DemandTypeArg::Type(DemandCoreType::Named {
                path: path("int"),
                args: Vec::new(),
            })],
        });
        let original = curried_signatures(
            &[
                list_int,
                DemandSignature::Fun {
                    param: Box::new(DemandSignature::Hole(0)),
                    ret: Box::new(DemandSignature::Hole(1)),
                },
            ],
            opt_int,
        );

        let demand = Demand::with_signature(
            path_segments(&["user", "container", "find"]),
            RuntimeType::core(typed_ir::Type::Any),
            original.clone(),
        );

        assert_eq!(demand.key.signature, original);
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

    fn named(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> typed_ir::Path {
        typed_ir::Path::from_name(typed_ir::Name(name.to_string()))
    }

    fn path_segments(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path {
            segments: segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).to_string()))
                .collect(),
        }
    }
}
