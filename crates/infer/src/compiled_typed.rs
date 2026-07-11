use poly::expr::{Arena as PolyArena, Def, DefId, Vis};
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RoleAssociatedType, RolePredicate,
    RolePredicateArg, Scheme, SchemeRecursiveBound, StackWeight, SubtractId, Subtractability,
    TypeArena, TypeIds, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use sources::{Name, Path};

use crate::Arena as InferArena;
use crate::lowering::BodyLowering;
use crate::{
    CompiledNamespaceMergeOutput, CompiledNamespaceSurface, CompiledNamespaceValueVisibility,
    CompiledNamespaceVisibility,
};

#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledTypedSurface {
    pub types: CompiledTypeArena,
    pub boundary: CompiledBoundaryInterface,
    pub values: Vec<CompiledTypedValueScheme>,
}

/// Unit-scoped type binders retained across compiled-surface imports.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledBoundaryInterface {
    pub bounds: Vec<CompiledBoundaryBound>,
}

/// One unit-owned boundary variable and its frozen neutral interval.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledBoundaryBound {
    pub var: TypeVar,
    pub bounds: NeuId,
}

/// Alpha-invariant identity of the boundary table accepted by this format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledBoundaryFingerprint(u64);

impl CompiledBoundaryInterface {
    pub fn empty() -> Self {
        Self::default()
    }

    /// Stage 1 deliberately accepts only the empty canonical table.
    ///
    /// A non-empty table needs the recursive alpha-canonical graph encoding
    /// specified for later stages. Hashing raw arena IDs here would make the
    /// typed/runtime agreement check unsound after an arena remap.
    pub fn semantic_fingerprint(&self) -> Option<CompiledBoundaryFingerprint> {
        if !self.bounds.is_empty() {
            return None;
        }

        let mut state = 0xcbf29ce484222325_u64;
        for byte in b"yulang/compiled-boundary-interface/v1"
            .iter()
            .chain(0_u64.to_le_bytes().iter())
        {
            state ^= u64::from(*byte);
            state = state.wrapping_mul(0x100000001b3);
        }
        Some(CompiledBoundaryFingerprint(state))
    }

    /// Fingerprint a structurally canonical non-empty boundary table in its owning arena.
    ///
    /// Entry roots first receive a local first-occurrence namespace used only for ordering. The
    /// order is accepted when those exact structural keys are unique; ambiguous symmetric roots
    /// remain non-canonical until the recursive-graph algorithm is specified. A second encoding
    /// then uses ordinals from that structural order, so raw `TypeVar` and arena node IDs never
    /// enter the fingerprint.
    #[allow(
        dead_code,
        reason = "Stage 5 production artifact connection consumes this in slice 2d"
    )]
    pub(crate) fn semantic_fingerprint_with_types(
        &self,
        types: &TypeArena,
    ) -> Option<CompiledBoundaryFingerprint> {
        let key = self.canonical_structural_key(types)?;
        Some(fingerprint_boundary_structural_key(&key))
    }

    pub(crate) fn canonical_structural_key(&self, types: &TypeArena) -> Option<Vec<u8>> {
        if self.bounds.is_empty() {
            let mut key = b"yulang/compiled-boundary-interface/v1".to_vec();
            push_u64(&mut key, 0);
            return Some(key);
        }

        let mut boundary = FxHashSet::default();
        for bound in &self.bounds {
            if !boundary.insert(bound.var) {
                return None;
            }
        }

        let mut ordered = self
            .bounds
            .iter()
            .map(|bound| {
                let mut encoder = BoundaryStructuralEncoder::local(types, &boundary, bound.var);
                let key = encoder.neu(bound.bounds)?;
                Some((key, bound))
            })
            .collect::<Option<Vec<_>>>()?;
        ordered.sort_by(|left, right| left.0.cmp(&right.0));
        if ordered.windows(2).any(|pair| pair[0].0 == pair[1].0) {
            return None;
        }

        let binders = ordered
            .iter()
            .enumerate()
            .map(|(index, (_, bound))| {
                let index = u32::try_from(index).ok()?;
                Some((bound.var, index))
            })
            .collect::<Option<FxHashMap<_, _>>>()?;
        let mut key = b"yulang/compiled-boundary-interface/v2".to_vec();
        push_len(&mut key, ordered.len())?;
        for (index, (_, bound)) in ordered.into_iter().enumerate() {
            push_u32(&mut key, u32::try_from(index).ok()?);
            let mut encoder = BoundaryStructuralEncoder::canonical(types, &boundary, &binders);
            let bounds = encoder.neu(bound.bounds)?;
            push_bytes(&mut key, &bounds)?;
        }
        Some(key)
    }
}

fn fingerprint_boundary_structural_key(key: &[u8]) -> CompiledBoundaryFingerprint {
    let mut state = 0xcbf29ce484222325_u64;
    for byte in key {
        state ^= u64::from(*byte);
        state = state.wrapping_mul(0x100000001b3);
    }
    CompiledBoundaryFingerprint(state)
}

use boundary_structural_fingerprint::{
    BoundaryStructuralEncoder, push_bytes, push_len, push_u32, push_u64,
};

mod boundary_structural_fingerprint {
    use super::*;

    pub(super) struct BoundaryStructuralEncoder<'a> {
        types: &'a TypeArena,
        boundary: &'a FxHashSet<TypeVar>,
        binders: FxHashMap<TypeVar, u32>,
        assign_first_occurrence: bool,
        pos: FxHashMap<PosId, Vec<u8>>,
        neg: FxHashMap<NegId, Vec<u8>>,
        neu: FxHashMap<NeuId, Vec<u8>>,
    }

    impl<'a> BoundaryStructuralEncoder<'a> {
        pub(super) fn local(
            types: &'a TypeArena,
            boundary: &'a FxHashSet<TypeVar>,
            root: TypeVar,
        ) -> Self {
            Self {
                types,
                boundary,
                binders: FxHashMap::from_iter([(root, 0)]),
                assign_first_occurrence: true,
                pos: FxHashMap::default(),
                neg: FxHashMap::default(),
                neu: FxHashMap::default(),
            }
        }

        pub(super) fn canonical(
            types: &'a TypeArena,
            boundary: &'a FxHashSet<TypeVar>,
            binders: &FxHashMap<TypeVar, u32>,
        ) -> Self {
            Self {
                types,
                boundary,
                binders: binders.clone(),
                assign_first_occurrence: false,
                pos: FxHashMap::default(),
                neg: FxHashMap::default(),
                neu: FxHashMap::default(),
            }
        }

        fn binder(&mut self, var: TypeVar) -> Option<u32> {
            if !self.boundary.contains(&var) {
                return None;
            }
            if let Some(index) = self.binders.get(&var) {
                return Some(*index);
            }
            if !self.assign_first_occurrence {
                return None;
            }
            let index = u32::try_from(self.binders.len()).ok()?;
            self.binders.insert(var, index);
            Some(index)
        }

        fn pos(&mut self, id: PosId) -> Option<Vec<u8>> {
            if let Some(encoded) = self.pos.get(&id) {
                return Some(encoded.clone());
            }
            let node = self.types.pos_nodes().get(id.0 as usize)?.clone();
            let mut out = Vec::new();
            match node {
                Pos::Bot => push_tag(&mut out, 0),
                Pos::Var(var) => {
                    push_tag(&mut out, 1);
                    push_u32(&mut out, self.binder(var)?);
                }
                Pos::Con(path, args) => {
                    push_tag(&mut out, 2);
                    push_path(&mut out, &path)?;
                    self.neu_ids(&mut out, &args)?;
                }
                Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                } => {
                    push_tag(&mut out, 3);
                    push_bytes(&mut out, &self.neg(arg)?)?;
                    push_bytes(&mut out, &self.neg(arg_eff)?)?;
                    push_bytes(&mut out, &self.pos(ret_eff)?)?;
                    push_bytes(&mut out, &self.pos(ret)?)?;
                }
                Pos::Record(fields) => {
                    push_tag(&mut out, 4);
                    self.pos_fields(&mut out, &fields)?;
                }
                Pos::RecordTailSpread { fields, tail } => {
                    push_tag(&mut out, 5);
                    self.pos_fields(&mut out, &fields)?;
                    push_bytes(&mut out, &self.pos(tail)?)?;
                }
                Pos::RecordHeadSpread { tail, fields } => {
                    push_tag(&mut out, 6);
                    push_bytes(&mut out, &self.pos(tail)?)?;
                    self.pos_fields(&mut out, &fields)?;
                }
                Pos::PolyVariant(items) => {
                    push_tag(&mut out, 7);
                    self.pos_variants(&mut out, &items)?;
                }
                Pos::Tuple(items) => {
                    push_tag(&mut out, 8);
                    self.pos_ids(&mut out, &items)?;
                }
                Pos::Row(items) => {
                    push_tag(&mut out, 9);
                    self.pos_ids(&mut out, &items)?;
                }
                Pos::Stack { inner, weight } => {
                    if !weight.is_empty() {
                        return None;
                    }
                    push_tag(&mut out, 10);
                    push_bytes(&mut out, &self.pos(inner)?)?;
                }
                Pos::NonSubtract(inner, weight) => {
                    if !weight.is_empty() {
                        return None;
                    }
                    push_tag(&mut out, 11);
                    push_bytes(&mut out, &self.pos(inner)?)?;
                }
                Pos::Union(left, right) => {
                    push_tag(&mut out, 12);
                    push_bytes(&mut out, &self.pos(left)?)?;
                    push_bytes(&mut out, &self.pos(right)?)?;
                }
            }
            self.pos.insert(id, out.clone());
            Some(out)
        }

        fn neg(&mut self, id: NegId) -> Option<Vec<u8>> {
            if let Some(encoded) = self.neg.get(&id) {
                return Some(encoded.clone());
            }
            let node = self.types.neg_nodes().get(id.0 as usize)?.clone();
            let mut out = Vec::new();
            match node {
                Neg::Top => push_tag(&mut out, 0),
                Neg::Bot => push_tag(&mut out, 1),
                Neg::Var(var) => {
                    push_tag(&mut out, 2);
                    push_u32(&mut out, self.binder(var)?);
                }
                Neg::Con(path, args) => {
                    push_tag(&mut out, 3);
                    push_path(&mut out, &path)?;
                    self.neu_ids(&mut out, &args)?;
                }
                Neg::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                } => {
                    push_tag(&mut out, 4);
                    push_bytes(&mut out, &self.pos(arg)?)?;
                    push_bytes(&mut out, &self.pos(arg_eff)?)?;
                    push_bytes(&mut out, &self.neg(ret_eff)?)?;
                    push_bytes(&mut out, &self.neg(ret)?)?;
                }
                Neg::Record(fields) => {
                    push_tag(&mut out, 5);
                    self.neg_fields(&mut out, &fields)?;
                }
                Neg::PolyVariant(items) => {
                    push_tag(&mut out, 6);
                    self.neg_variants(&mut out, &items)?;
                }
                Neg::Tuple(items) => {
                    push_tag(&mut out, 7);
                    self.neg_ids(&mut out, &items)?;
                }
                Neg::Row(items, tail) => {
                    push_tag(&mut out, 8);
                    self.neg_ids(&mut out, &items)?;
                    push_bytes(&mut out, &self.neg(tail)?)?;
                }
                Neg::Stack { inner, weight } => {
                    if !weight.is_empty() {
                        return None;
                    }
                    push_tag(&mut out, 9);
                    push_bytes(&mut out, &self.neg(inner)?)?;
                }
                Neg::Intersection(left, right) => {
                    push_tag(&mut out, 10);
                    push_bytes(&mut out, &self.neg(left)?)?;
                    push_bytes(&mut out, &self.neg(right)?)?;
                }
            }
            self.neg.insert(id, out.clone());
            Some(out)
        }

        pub(super) fn neu(&mut self, id: NeuId) -> Option<Vec<u8>> {
            if let Some(encoded) = self.neu.get(&id) {
                return Some(encoded.clone());
            }
            let node = self.types.neu_nodes().get(id.0 as usize)?.clone();
            let mut out = Vec::new();
            match node {
                Neu::Bounds(lower, upper) => {
                    push_tag(&mut out, 0);
                    push_bytes(&mut out, &self.pos(lower)?)?;
                    push_bytes(&mut out, &self.neg(upper)?)?;
                }
                Neu::Con(path, args) => {
                    push_tag(&mut out, 1);
                    push_path(&mut out, &path)?;
                    self.neu_ids(&mut out, &args)?;
                }
                Neu::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                } => {
                    push_tag(&mut out, 2);
                    push_bytes(&mut out, &self.neu(arg)?)?;
                    push_bytes(&mut out, &self.neu(arg_eff)?)?;
                    push_bytes(&mut out, &self.neu(ret_eff)?)?;
                    push_bytes(&mut out, &self.neu(ret)?)?;
                }
                Neu::Record(fields) => {
                    push_tag(&mut out, 3);
                    self.neu_fields(&mut out, &fields)?;
                }
                Neu::PolyVariant(items) => {
                    push_tag(&mut out, 4);
                    self.neu_variants(&mut out, &items)?;
                }
                Neu::Tuple(items) => {
                    push_tag(&mut out, 5);
                    self.neu_ids(&mut out, &items)?;
                }
            }
            self.neu.insert(id, out.clone());
            Some(out)
        }

        fn pos_ids(&mut self, out: &mut Vec<u8>, ids: &[PosId]) -> Option<()> {
            push_len(out, ids.len())?;
            for id in ids {
                push_bytes(out, &self.pos(*id)?)?;
            }
            Some(())
        }

        fn neg_ids(&mut self, out: &mut Vec<u8>, ids: &[NegId]) -> Option<()> {
            push_len(out, ids.len())?;
            for id in ids {
                push_bytes(out, &self.neg(*id)?)?;
            }
            Some(())
        }

        fn neu_ids(&mut self, out: &mut Vec<u8>, ids: &[NeuId]) -> Option<()> {
            push_len(out, ids.len())?;
            for id in ids {
                push_bytes(out, &self.neu(*id)?)?;
            }
            Some(())
        }

        fn pos_fields(&mut self, out: &mut Vec<u8>, fields: &[RecordField<PosId>]) -> Option<()> {
            push_len(out, fields.len())?;
            for field in fields {
                push_string(out, &field.name)?;
                push_bool(out, field.optional);
                push_bytes(out, &self.pos(field.value)?)?;
            }
            Some(())
        }

        fn neg_fields(&mut self, out: &mut Vec<u8>, fields: &[RecordField<NegId>]) -> Option<()> {
            push_len(out, fields.len())?;
            for field in fields {
                push_string(out, &field.name)?;
                push_bool(out, field.optional);
                push_bytes(out, &self.neg(field.value)?)?;
            }
            Some(())
        }

        fn neu_fields(&mut self, out: &mut Vec<u8>, fields: &[RecordField<NeuId>]) -> Option<()> {
            push_len(out, fields.len())?;
            for field in fields {
                push_string(out, &field.name)?;
                push_bool(out, field.optional);
                push_bytes(out, &self.neu(field.value)?)?;
            }
            Some(())
        }

        fn pos_variants(
            &mut self,
            out: &mut Vec<u8>,
            items: &[(String, Vec<PosId>)],
        ) -> Option<()> {
            push_len(out, items.len())?;
            for (name, payloads) in items {
                push_string(out, name)?;
                self.pos_ids(out, payloads)?;
            }
            Some(())
        }

        fn neg_variants(
            &mut self,
            out: &mut Vec<u8>,
            items: &[(String, Vec<NegId>)],
        ) -> Option<()> {
            push_len(out, items.len())?;
            for (name, payloads) in items {
                push_string(out, name)?;
                self.neg_ids(out, payloads)?;
            }
            Some(())
        }

        fn neu_variants(
            &mut self,
            out: &mut Vec<u8>,
            items: &[(String, Vec<NeuId>)],
        ) -> Option<()> {
            push_len(out, items.len())?;
            for (name, payloads) in items {
                push_string(out, name)?;
                self.neu_ids(out, payloads)?;
            }
            Some(())
        }
    }

    fn push_tag(out: &mut Vec<u8>, tag: u8) {
        out.push(tag);
    }

    fn push_bool(out: &mut Vec<u8>, value: bool) {
        out.push(u8::from(value));
    }

    pub(super) fn push_u32(out: &mut Vec<u8>, value: u32) {
        out.extend(value.to_le_bytes());
    }

    pub(super) fn push_u64(out: &mut Vec<u8>, value: u64) {
        out.extend(value.to_le_bytes());
    }

    pub(super) fn push_len(out: &mut Vec<u8>, value: usize) -> Option<()> {
        push_u64(out, u64::try_from(value).ok()?);
        Some(())
    }

    pub(super) fn push_bytes(out: &mut Vec<u8>, value: &[u8]) -> Option<()> {
        push_len(out, value.len())?;
        out.extend(value);
        Some(())
    }

    fn push_string(out: &mut Vec<u8>, value: &str) -> Option<()> {
        push_bytes(out, value.as_bytes())
    }

    fn push_path(out: &mut Vec<u8>, path: &[String]) -> Option<()> {
        push_len(out, path.len())?;
        for segment in path {
            push_string(out, segment)?;
        }
        Some(())
    }
}

impl CompiledBoundaryFingerprint {
    pub fn get(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledTypeArena {
    pub pos: Vec<Pos>,
    pub neg: Vec<Neg>,
    pub neu: Vec<Neu>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledTypedValueScheme {
    pub symbol: u32,
    pub scheme: Scheme,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledTypedMergeError {
    MissingValueSymbol { prefix: usize, symbol: u32 },
    DuplicateValueSymbol { symbol: u32 },
}

/// One-shot canonical cache-interface handoff to both compiled surfaces.
///
/// Artifact construction does not use this entry until the later integration stage. Keeping the
/// pair together here ensures that enabling it cannot independently freeze schemes, candidates,
/// or boundary graphs for typed and runtime consumers.
#[allow(
    dead_code,
    reason = "the Stage 5 non-empty artifact slice enables this common handoff"
)]
pub(crate) struct CompiledCacheInterfaceSurfaces {
    pub(crate) typed: CompiledTypedSurface,
    pub(crate) runtime: crate::CompiledRuntimeSurface,
}

#[derive(Clone, Copy)]
struct CompiledTypedValueSource {
    symbol: u32,
    def: DefId,
}

#[allow(
    dead_code,
    reason = "the Stage 5 non-empty artifact slice enables this common handoff"
)]
impl CompiledCacheInterfaceSurfaces {
    pub(crate) fn from_lowering(
        lowering: &BodyLowering,
        namespace: &CompiledNamespaceSurface,
    ) -> Result<Self, crate::analysis::BoundaryCaptureError> {
        let value_sources = compiled_typed_value_sources(lowering, namespace);
        let (draft, candidates) = lowering
            .session
            .prepare_cache_interface_handoff(value_sources.iter().map(|value| value.def))?;
        let mut arena = lowering.session.poly.clone();
        let candidates = lowering
            .session
            .freeze_cache_candidate_interface(candidates, &mut arena)?;
        let boundary = draft
            .with_frozen_candidates(candidates)
            .freeze_into_poly(lowering.session.infer.constraints(), &mut arena)?;
        let typed = CompiledTypedSurface::from_poly_arena(&arena, &value_sources, boundary.clone());
        let runtime = crate::CompiledRuntimeSurface::from_canonical_cache_interface_handoff(
            lowering, namespace, arena, boundary,
        );
        Ok(Self { typed, runtime })
    }
}

pub struct CompiledValueImport {
    pub boundary: CompiledBoundaryInterface,
    pub values: Vec<CompiledImportedValue>,
}

pub struct CompiledImportedValue {
    pub symbol: u32,
    pub def: DefId,
}

pub struct CompiledUnitImport {
    pub values: CompiledValueImport,
    exported_values: FxHashMap<Vec<String>, FxHashMap<String, DefId>>,
}

impl CompiledUnitImport {
    pub fn exported_value_def(&self, module_path: &[String], name: &str) -> Option<DefId> {
        self.exported_values
            .get(module_path)
            .and_then(|values| values.get(name))
            .copied()
    }
}

pub struct CompiledTypedIndex<'a> {
    surface: &'a CompiledTypedSurface,
    values_by_symbol: FxHashMap<u32, usize>,
}

impl<'a> CompiledTypedIndex<'a> {
    pub fn new(surface: &'a CompiledTypedSurface) -> Self {
        Self {
            surface,
            values_by_symbol: surface
                .values
                .iter()
                .enumerate()
                .map(|(index, value)| (value.symbol, index))
                .collect(),
        }
    }

    pub fn value_scheme(&self, symbol: u32) -> Option<&'a Scheme> {
        let index = *self.values_by_symbol.get(&symbol)?;
        Some(&self.surface.values.get(index)?.scheme)
    }
}

impl CompiledTypedSurface {
    /// Return the boundary fingerprint only after exact typed/runtime structural agreement.
    ///
    /// The compiled surfaces serialize their type arenas independently even when both originated
    /// from one canonical handoff. Decode and merge validation can therefore compare the complete
    /// alpha-canonical byte keys before reducing their shared identity to a `u64` fingerprint.
    pub fn boundary_fingerprint_agreeing_with_runtime(
        &self,
        runtime: &crate::CompiledRuntimeSurface,
    ) -> Option<CompiledBoundaryFingerprint> {
        let typed_types = self.types.to_type_arena();
        let typed_key = self.boundary.canonical_structural_key(&typed_types)?;
        let runtime_key = runtime
            .boundary
            .canonical_structural_key(&runtime.arena.typ)?;
        if typed_key != runtime_key {
            return None;
        }
        Some(fingerprint_boundary_structural_key(&typed_key))
    }

    pub fn from_lowering(lowering: &BodyLowering, namespace: &CompiledNamespaceSurface) -> Self {
        Self::from_lowering_with_boundary(lowering, namespace, CompiledBoundaryInterface::empty())
    }

    pub fn from_lowering_with_boundary(
        lowering: &BodyLowering,
        namespace: &CompiledNamespaceSurface,
        boundary: CompiledBoundaryInterface,
    ) -> Self {
        let value_sources = compiled_typed_value_sources(lowering, namespace);
        Self::from_poly_arena(&lowering.session.poly, &value_sources, boundary)
    }

    fn from_poly_arena(
        arena: &PolyArena,
        value_sources: &[CompiledTypedValueSource],
        boundary: CompiledBoundaryInterface,
    ) -> Self {
        let mut values = value_sources
            .iter()
            .filter_map(|value| {
                let Some(Def::Let {
                    scheme: Some(scheme),
                    ..
                }) = arena.defs.get(value.def)
                else {
                    return None;
                };
                Some(CompiledTypedValueScheme {
                    symbol: value.symbol,
                    scheme: scheme.clone(),
                })
            })
            .collect::<Vec<_>>();
        values.sort_by_key(|value| value.symbol);
        Self {
            types: CompiledTypeArena::from_type_arena(&arena.typ),
            boundary,
            values,
        }
    }

    pub fn import_value_defs(
        &self,
        namespace: &CompiledNamespaceSurface,
        poly: &mut PolyArena,
        infer: &mut InferArena,
    ) -> CompiledValueImport {
        let mut type_importer = CompiledTypeImporter::new(&self.types, infer);
        let boundary = type_importer.import_boundary_interface(&self.boundary);
        let values = self
            .values
            .iter()
            .filter_map(|value| {
                let visibility = namespace.value_visibility(value.symbol)?;
                let def = poly.defs.fresh();
                poly.defs.set(
                    def,
                    Def::Let {
                        vis: compiled_value_visibility(visibility),
                        scheme: Some(type_importer.import_scheme(&value.scheme)),
                        body: None,
                        children: Vec::new(),
                    },
                );
                Some(CompiledImportedValue {
                    symbol: value.symbol,
                    def,
                })
            })
            .collect();
        CompiledValueImport { boundary, values }
    }

    pub fn import_unit(
        &self,
        namespace: &CompiledNamespaceSurface,
        poly: &mut PolyArena,
        infer: &mut InferArena,
    ) -> CompiledUnitImport {
        let values = self.import_value_defs(namespace, poly, infer);
        let value_defs = values
            .values
            .iter()
            .map(|value| (value.symbol, value.def))
            .collect::<FxHashMap<_, _>>();
        let mut exported_values = FxHashMap::default();
        for module in &namespace.modules {
            for value in module
                .values
                .iter()
                .filter(|value| value.visibility != CompiledNamespaceVisibility::My)
            {
                let Some(def) = value_defs.get(&value.symbol).copied() else {
                    continue;
                };
                exported_values
                    .entry(module.path.clone())
                    .or_insert_with(FxHashMap::default)
                    .insert(value.name.clone(), def);
            }
            for value in module
                .imported_values
                .iter()
                .filter(|value| value.visibility != CompiledNamespaceVisibility::My)
            {
                let Some(def) = value_defs.get(&value.symbol).copied() else {
                    continue;
                };
                exported_values
                    .entry(module.path.clone())
                    .or_insert_with(FxHashMap::default)
                    .insert(value.name.clone(), def);
            }
        }
        CompiledUnitImport {
            values,
            exported_values,
        }
    }

    pub fn merge_prefixes<'a>(
        prefixes: impl IntoIterator<Item = &'a CompiledTypedSurface>,
        namespace: &CompiledNamespaceMergeOutput,
    ) -> Result<Self, CompiledTypedMergeError> {
        let mut type_target = CompiledTypeArenaBuilder::new();
        let mut boundary = CompiledBoundaryInterface::empty();
        let mut values = Vec::new();
        let mut seen_values = FxHashSet::default();
        for (prefix, surface) in prefixes.into_iter().enumerate() {
            let mut type_importer = CompiledTypeImporter::new(&surface.types, &mut type_target);
            boundary.bounds.extend(
                type_importer
                    .import_boundary_interface(&surface.boundary)
                    .bounds,
            );
            for value in &surface.values {
                let Some(symbol) = namespace.map_value(prefix, value.symbol) else {
                    return Err(CompiledTypedMergeError::MissingValueSymbol {
                        prefix,
                        symbol: value.symbol,
                    });
                };
                if !seen_values.insert(symbol) {
                    return Err(CompiledTypedMergeError::DuplicateValueSymbol { symbol });
                }
                values.push(CompiledTypedValueScheme {
                    symbol,
                    scheme: type_importer.import_scheme(&value.scheme),
                });
            }
        }
        values.sort_by_key(|value| value.symbol);
        Ok(Self {
            types: type_target.finish(),
            boundary,
            values,
        })
    }
}

fn compiled_typed_value_sources(
    lowering: &BodyLowering,
    namespace: &CompiledNamespaceSurface,
) -> Vec<CompiledTypedValueSource> {
    let mut values = Vec::new();
    for module in &namespace.modules {
        let Some(live_module) = lowering
            .modules
            .module_by_path(&path_from_strings(&module.path))
        else {
            continue;
        };
        for value in module
            .values
            .iter()
            .filter(|value| value.visibility != CompiledNamespaceVisibility::My)
        {
            let name = Name(value.name.clone());
            let Some(def) = lowering
                .modules
                .value_decls(live_module, &name)
                .into_iter()
                .find(|decl| decl.order.index() == value.order)
                .map(|decl| decl.def)
            else {
                continue;
            };
            let Some(Def::Let {
                vis,
                scheme: Some(_),
                ..
            }) = lowering.session.poly.defs.get(def)
            else {
                continue;
            };
            if *vis == Vis::My {
                continue;
            }
            values.push(CompiledTypedValueSource {
                symbol: value.symbol,
                def,
            });
        }
    }
    values.sort_by_key(|value| value.symbol);
    values
}

fn compiled_value_visibility(visibility: CompiledNamespaceValueVisibility) -> Vis {
    match visibility {
        CompiledNamespaceValueVisibility::Pub => Vis::Pub,
        CompiledNamespaceValueVisibility::Our => Vis::Our,
    }
}

impl CompiledTypeArena {
    pub fn from_type_arena(types: &TypeArena) -> Self {
        Self {
            pos: types.pos_nodes().to_vec(),
            neg: types.neg_nodes().to_vec(),
            neu: types.neu_nodes().to_vec(),
        }
    }

    pub fn to_type_arena(&self) -> TypeArena {
        let mut types = TypeArena::new();
        for (index, node) in self.pos.iter().enumerate() {
            let id = types.alloc_pos(node.clone());
            debug_assert_eq!(id.0 as usize, index);
        }
        for (index, node) in self.neg.iter().enumerate() {
            let id = types.alloc_neg(node.clone());
            debug_assert_eq!(id.0 as usize, index);
        }
        for (index, node) in self.neu.iter().enumerate() {
            let id = types.alloc_neu(node.clone());
            debug_assert_eq!(id.0 as usize, index);
        }
        types
    }
}

struct CompiledTypeArenaBuilder {
    type_ids: TypeIds,
    types: TypeArena,
}

impl CompiledTypeArenaBuilder {
    fn new() -> Self {
        Self {
            type_ids: TypeIds::new(),
            types: TypeArena::new(),
        }
    }

    fn finish(self) -> CompiledTypeArena {
        CompiledTypeArena::from_type_arena(&self.types)
    }
}

pub trait CompiledTypeImportTarget {
    fn fresh_type_var(&mut self) -> TypeVar;
    fn fresh_subtract_id(&mut self) -> SubtractId;
    fn alloc_pos(&mut self, pos: Pos) -> PosId;
    fn alloc_neg(&mut self, neg: Neg) -> NegId;
    fn alloc_neu(&mut self, neu: Neu) -> NeuId;
}

impl CompiledTypeImportTarget for CompiledTypeArenaBuilder {
    fn fresh_type_var(&mut self) -> TypeVar {
        self.type_ids.fresh_type_var()
    }

    fn fresh_subtract_id(&mut self) -> SubtractId {
        self.type_ids.fresh_subtract_id()
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.types.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.types.alloc_neg(neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.types.alloc_neu(neu)
    }
}

impl CompiledTypeImportTarget for InferArena {
    fn fresh_type_var(&mut self) -> TypeVar {
        self.fresh_type_var()
    }

    fn fresh_subtract_id(&mut self) -> SubtractId {
        self.fresh_subtract_id()
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.alloc_neg(neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.alloc_neu(neu)
    }
}

impl CompiledTypeImportTarget for PolyArena {
    fn fresh_type_var(&mut self) -> TypeVar {
        self.fresh_type_var()
    }

    fn fresh_subtract_id(&mut self) -> SubtractId {
        self.fresh_subtract_id()
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.typ.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.typ.alloc_neg(neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.typ.alloc_neu(neu)
    }
}

pub struct CompiledTypeImporter<'a, 'b, T: CompiledTypeImportTarget> {
    source: &'a CompiledTypeArena,
    target: &'b mut T,
    pos: FxHashMap<PosId, PosId>,
    neg: FxHashMap<NegId, NegId>,
    neu: FxHashMap<NeuId, NeuId>,
    vars: FxHashMap<TypeVar, TypeVar>,
    subtracts: FxHashMap<SubtractId, SubtractId>,
}

impl<'a, 'b, T: CompiledTypeImportTarget> CompiledTypeImporter<'a, 'b, T> {
    pub fn new(source: &'a CompiledTypeArena, target: &'b mut T) -> Self {
        Self {
            source,
            target,
            pos: FxHashMap::default(),
            neg: FxHashMap::default(),
            neu: FxHashMap::default(),
            vars: FxHashMap::default(),
            subtracts: FxHashMap::default(),
        }
    }

    pub fn import_scheme(&mut self, scheme: &Scheme) -> Scheme {
        Scheme {
            quantifiers: scheme
                .quantifiers
                .iter()
                .map(|var| self.map_type_var(*var))
                .collect(),
            role_predicates: scheme
                .role_predicates
                .iter()
                .map(|predicate| self.import_role_predicate(predicate))
                .collect(),
            recursive_bounds: scheme
                .recursive_bounds
                .iter()
                .map(|bound| SchemeRecursiveBound {
                    var: self.map_type_var(bound.var),
                    bounds: self.import_neu_id(bound.bounds),
                })
                .collect(),
            stack_quantifiers: scheme
                .stack_quantifiers
                .iter()
                .map(|id| self.map_subtract_id(*id))
                .collect(),
            predicate: self.import_pos_id(scheme.predicate),
        }
    }

    pub fn import_boundary_interface(
        &mut self,
        boundary: &CompiledBoundaryInterface,
    ) -> CompiledBoundaryInterface {
        // Register every unit binder before cloning any bound graph so mutual
        // references and scheme references share this importer's one mapping.
        for bound in &boundary.bounds {
            self.map_type_var(bound.var);
        }
        CompiledBoundaryInterface {
            bounds: boundary
                .bounds
                .iter()
                .map(|bound| CompiledBoundaryBound {
                    var: self.map_type_var(bound.var),
                    bounds: self.import_neu_id(bound.bounds),
                })
                .collect(),
        }
    }

    pub fn import_pos_id(&mut self, id: PosId) -> PosId {
        if let Some(mapped) = self.pos.get(&id) {
            return *mapped;
        }
        let node = self
            .source
            .pos
            .get(id.0 as usize)
            .unwrap_or_else(|| panic!("compiled positive type id {} is missing", id.0))
            .clone();
        let mapped = self.import_pos(node);
        self.pos.insert(id, mapped);
        mapped
    }

    pub fn import_neg_id(&mut self, id: NegId) -> NegId {
        if let Some(mapped) = self.neg.get(&id) {
            return *mapped;
        }
        let node = self
            .source
            .neg
            .get(id.0 as usize)
            .unwrap_or_else(|| panic!("compiled negative type id {} is missing", id.0))
            .clone();
        let mapped = self.import_neg(node);
        self.neg.insert(id, mapped);
        mapped
    }

    pub fn import_neu_id(&mut self, id: NeuId) -> NeuId {
        if let Some(mapped) = self.neu.get(&id) {
            return *mapped;
        }
        let node = self
            .source
            .neu
            .get(id.0 as usize)
            .unwrap_or_else(|| panic!("compiled neutral type id {} is missing", id.0))
            .clone();
        let mapped = self.import_neu(node);
        self.neu.insert(id, mapped);
        mapped
    }

    fn import_pos(&mut self, pos: Pos) -> PosId {
        let mapped = match pos {
            Pos::Bot => Pos::Bot,
            Pos::Var(var) => Pos::Var(self.map_type_var(var)),
            Pos::Con(path, args) => Pos::Con(path, self.import_neu_ids(args)),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Pos::Fun {
                arg: self.import_neg_id(arg),
                arg_eff: self.import_neg_id(arg_eff),
                ret_eff: self.import_pos_id(ret_eff),
                ret: self.import_pos_id(ret),
            },
            Pos::Record(fields) => {
                Pos::Record(self.import_record_fields(fields, Self::import_pos_id))
            }
            Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
                fields: self.import_record_fields(fields, Self::import_pos_id),
                tail: self.import_pos_id(tail),
            },
            Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
                tail: self.import_pos_id(tail),
                fields: self.import_record_fields(fields, Self::import_pos_id),
            },
            Pos::PolyVariant(variants) => Pos::PolyVariant(
                variants
                    .into_iter()
                    .map(|(name, payloads)| (name, self.import_pos_ids(payloads)))
                    .collect(),
            ),
            Pos::Tuple(items) => Pos::Tuple(self.import_pos_ids(items)),
            Pos::Row(items) => Pos::Row(self.import_pos_ids(items)),
            Pos::Stack { inner, weight } => Pos::Stack {
                inner: self.import_pos_id(inner),
                weight: self.import_stack_weight(&weight),
            },
            Pos::NonSubtract(inner, weight) => {
                Pos::NonSubtract(self.import_pos_id(inner), self.import_stack_weight(&weight))
            }
            Pos::Union(left, right) => {
                Pos::Union(self.import_pos_id(left), self.import_pos_id(right))
            }
        };
        self.target.alloc_pos(mapped)
    }

    fn import_neg(&mut self, neg: Neg) -> NegId {
        let mapped = match neg {
            Neg::Top => Neg::Top,
            Neg::Bot => Neg::Bot,
            Neg::Var(var) => Neg::Var(self.map_type_var(var)),
            Neg::Con(path, args) => Neg::Con(path, self.import_neu_ids(args)),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neg::Fun {
                arg: self.import_pos_id(arg),
                arg_eff: self.import_pos_id(arg_eff),
                ret_eff: self.import_neg_id(ret_eff),
                ret: self.import_neg_id(ret),
            },
            Neg::Record(fields) => {
                Neg::Record(self.import_record_fields(fields, Self::import_neg_id))
            }
            Neg::PolyVariant(variants) => Neg::PolyVariant(
                variants
                    .into_iter()
                    .map(|(name, payloads)| (name, self.import_neg_ids(payloads)))
                    .collect(),
            ),
            Neg::Tuple(items) => Neg::Tuple(self.import_neg_ids(items)),
            Neg::Row(items, tail) => Neg::Row(self.import_neg_ids(items), self.import_neg_id(tail)),
            Neg::Stack { inner, weight } => Neg::Stack {
                inner: self.import_neg_id(inner),
                weight: self.import_stack_weight(&weight),
            },
            Neg::Intersection(left, right) => {
                Neg::Intersection(self.import_neg_id(left), self.import_neg_id(right))
            }
        };
        self.target.alloc_neg(mapped)
    }

    fn import_neu(&mut self, neu: Neu) -> NeuId {
        let mapped = match neu {
            Neu::Bounds(lower, upper) => {
                Neu::Bounds(self.import_pos_id(lower), self.import_neg_id(upper))
            }
            Neu::Con(path, args) => Neu::Con(path, self.import_neu_ids(args)),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neu::Fun {
                arg: self.import_neu_id(arg),
                arg_eff: self.import_neu_id(arg_eff),
                ret_eff: self.import_neu_id(ret_eff),
                ret: self.import_neu_id(ret),
            },
            Neu::Record(fields) => {
                Neu::Record(self.import_record_fields(fields, Self::import_neu_id))
            }
            Neu::PolyVariant(variants) => Neu::PolyVariant(
                variants
                    .into_iter()
                    .map(|(name, payloads)| (name, self.import_neu_ids(payloads)))
                    .collect(),
            ),
            Neu::Tuple(items) => Neu::Tuple(self.import_neu_ids(items)),
        };
        self.target.alloc_neu(mapped)
    }

    fn import_role_predicate(&mut self, predicate: &RolePredicate) -> RolePredicate {
        RolePredicate {
            role: predicate.role.clone(),
            inputs: predicate
                .inputs
                .iter()
                .map(|input| match input {
                    RolePredicateArg::Covariant(id) => {
                        RolePredicateArg::Covariant(self.import_pos_id(*id))
                    }
                    RolePredicateArg::Contravariant(id) => {
                        RolePredicateArg::Contravariant(self.import_neg_id(*id))
                    }
                    RolePredicateArg::Invariant(id) => {
                        RolePredicateArg::Invariant(self.import_neu_id(*id))
                    }
                })
                .collect(),
            associated: predicate
                .associated
                .iter()
                .map(|associated| RoleAssociatedType {
                    name: associated.name.clone(),
                    value: self.import_neu_id(associated.value),
                })
                .collect(),
        }
    }

    fn import_stack_weight(&mut self, weight: &StackWeight) -> StackWeight {
        let mut out = StackWeight::filter(self.import_subtractability(weight.filter_set()));
        for entry in weight.entries() {
            if entry.pops > 0 {
                out = out.compose(&StackWeight::pops(
                    self.map_subtract_id(entry.id),
                    entry.pops,
                ));
            }
            for floor in &entry.floor {
                out = out.compose(&StackWeight::floor(
                    self.map_subtract_id(entry.id),
                    self.import_subtractability(floor),
                ));
            }
            for stack in &entry.stack {
                out = out.compose(&StackWeight::push(
                    self.map_subtract_id(entry.id),
                    self.import_subtractability(stack),
                ));
            }
        }
        out
    }

    fn import_subtractability(&mut self, subtractability: &Subtractability) -> Subtractability {
        match subtractability {
            Subtractability::Empty => Subtractability::Empty,
            Subtractability::All => Subtractability::All,
            Subtractability::AllExcept(path, args) => {
                Subtractability::AllExcept(path.clone(), self.import_neu_ids(args.clone()))
            }
            Subtractability::AllExceptMany(families) => Subtractability::AllExceptMany(
                families
                    .iter()
                    .map(|(path, args)| (path.clone(), self.import_neu_ids(args.clone())))
                    .collect(),
            ),
            Subtractability::Set(path, args) => {
                Subtractability::Set(path.clone(), self.import_neu_ids(args.clone()))
            }
            Subtractability::SetMany(families) => Subtractability::SetMany(
                families
                    .iter()
                    .map(|(path, args)| (path.clone(), self.import_neu_ids(args.clone())))
                    .collect(),
            ),
        }
    }

    fn import_record_fields<SourceId: Copy, TargetId>(
        &mut self,
        fields: Vec<RecordField<SourceId>>,
        import: fn(&mut Self, SourceId) -> TargetId,
    ) -> Vec<RecordField<TargetId>> {
        fields
            .into_iter()
            .map(|field| RecordField {
                name: field.name,
                value: import(self, field.value),
                optional: field.optional,
            })
            .collect()
    }

    fn import_pos_ids(&mut self, ids: Vec<PosId>) -> Vec<PosId> {
        ids.into_iter().map(|id| self.import_pos_id(id)).collect()
    }

    fn import_neg_ids(&mut self, ids: Vec<NegId>) -> Vec<NegId> {
        ids.into_iter().map(|id| self.import_neg_id(id)).collect()
    }

    fn import_neu_ids(&mut self, ids: Vec<NeuId>) -> Vec<NeuId> {
        ids.into_iter().map(|id| self.import_neu_id(id)).collect()
    }

    fn map_type_var(&mut self, var: TypeVar) -> TypeVar {
        *self
            .vars
            .entry(var)
            .or_insert_with(|| self.target.fresh_type_var())
    }

    fn map_subtract_id(&mut self, id: SubtractId) -> SubtractId {
        *self
            .subtracts
            .entry(id)
            .or_insert_with(|| self.target.fresh_subtract_id())
    }
}

fn path_from_strings(path: &[String]) -> Path {
    Path {
        segments: path.iter().cloned().map(Name).collect(),
    }
}

#[cfg(test)]
mod tests {
    use sources::SourceFile;

    use crate::lowering::{
        lower_loaded_files, lower_loaded_files_prefix, lower_loaded_files_with_prefix,
    };

    use super::*;

    #[test]
    fn non_empty_boundary_fingerprint_ignores_raw_binder_node_and_entry_order() {
        let (left_types, left) =
            structural_boundary_fixture([TypeVar(7), TypeVar(8)], false, 0, "payload");
        let (right_types, right) =
            structural_boundary_fixture([TypeVar(800), TypeVar(300)], true, 3, "payload");

        let left_fingerprint = left
            .semantic_fingerprint_with_types(&left_types)
            .expect("unique structural roots are canonical");
        let right_fingerprint = right
            .semantic_fingerprint_with_types(&right_types)
            .expect("alpha-renamed structural roots are canonical");

        assert_eq!(left_fingerprint, right_fingerprint);
        assert_eq!(
            left.semantic_fingerprint_with_types(&left_types),
            left.semantic_fingerprint_with_types(&left_types),
            "repeated fingerprinting must be deterministic"
        );
        assert_eq!(
            CompiledBoundaryInterface::empty().semantic_fingerprint_with_types(&TypeArena::new()),
            CompiledBoundaryInterface::empty().semantic_fingerprint(),
            "the existing empty-boundary fingerprint must remain unchanged"
        );
    }

    #[test]
    fn typed_runtime_boundary_agreement_compares_exact_keys_before_hashing() {
        let (typed_types, typed_boundary) =
            structural_boundary_fixture([TypeVar(7), TypeVar(8)], false, 0, "payload");
        let (runtime_types, runtime_boundary) =
            structural_boundary_fixture([TypeVar(800), TypeVar(300)], true, 3, "payload");
        let typed_key = typed_boundary
            .canonical_structural_key(&typed_types)
            .expect("typed boundary key");
        let runtime_key = runtime_boundary
            .canonical_structural_key(&runtime_types)
            .expect("runtime boundary key");
        assert_eq!(
            typed_key, runtime_key,
            "alpha-equivalent boundaries in independent arenas must agree exactly"
        );
        let expected = typed_boundary
            .semantic_fingerprint_with_types(&typed_types)
            .expect("agreed boundary fingerprint");
        let typed = CompiledTypedSurface {
            types: CompiledTypeArena::from_type_arena(&typed_types),
            boundary: typed_boundary,
            values: Vec::new(),
        };
        let mut runtime_arena = PolyArena::new();
        runtime_arena.typ = runtime_types;
        let runtime = crate::CompiledRuntimeSurface {
            arena: runtime_arena,
            boundary: runtime_boundary,
            labels: poly::dump::DumpLabels::new(),
            modules: Vec::new(),
            values: Vec::new(),
        };
        assert_eq!(
            typed.boundary_fingerprint_agreeing_with_runtime(&runtime),
            Some(expected)
        );

        let (different_types, different_boundary) =
            structural_boundary_fixture([TypeVar(91), TypeVar(92)], false, 0, "different");
        let different_key = different_boundary
            .canonical_structural_key(&different_types)
            .expect("different runtime boundary key");
        assert_ne!(typed_key, different_key);
        let mut different_arena = PolyArena::new();
        different_arena.typ = different_types;
        let different_runtime = crate::CompiledRuntimeSurface {
            arena: different_arena,
            boundary: different_boundary,
            labels: poly::dump::DumpLabels::new(),
            modules: Vec::new(),
            values: Vec::new(),
        };
        assert_eq!(
            typed.boundary_fingerprint_agreeing_with_runtime(&different_runtime),
            None,
            "a structural mismatch must be rejected before either key is reduced to u64"
        );
    }

    #[test]
    fn non_empty_boundary_fingerprint_distinguishes_structure_and_rejects_ambiguous_roots() {
        let (left_types, left) =
            structural_boundary_fixture([TypeVar(11), TypeVar(12)], false, 0, "payload");
        let (different_types, different) =
            structural_boundary_fixture([TypeVar(91), TypeVar(92)], false, 0, "different");
        assert_ne!(
            left.semantic_fingerprint_with_types(&left_types),
            different.semantic_fingerprint_with_types(&different_types)
        );

        let mut ambiguous_types = TypeArena::new();
        let first = TypeVar(20);
        let second = TypeVar(21);
        let first_lower = ambiguous_types.alloc_pos(Pos::Var(first));
        let first_upper = ambiguous_types.alloc_neg(Neg::Var(first));
        let first_bounds = ambiguous_types.alloc_neu(Neu::Bounds(first_lower, first_upper));
        let second_lower = ambiguous_types.alloc_pos(Pos::Var(second));
        let second_upper = ambiguous_types.alloc_neg(Neg::Var(second));
        let second_bounds = ambiguous_types.alloc_neu(Neu::Bounds(second_lower, second_upper));
        let ambiguous = CompiledBoundaryInterface {
            bounds: vec![
                CompiledBoundaryBound {
                    var: first,
                    bounds: first_bounds,
                },
                CompiledBoundaryBound {
                    var: second,
                    bounds: second_bounds,
                },
            ],
        };

        assert_eq!(
            ambiguous.semantic_fingerprint_with_types(&ambiguous_types),
            None,
            "symmetric roots need the still-unconfirmed recursive graph canonicalizer"
        );
    }

    #[test]
    fn typed_surface_records_exported_value_schemes_by_namespace_symbol() {
        let loaded = sources::load(vec![
            source(&[], "mod ops;\npub use ops::*\n"),
            source(&["ops"], "pub id x = x\npub x = 42\nmy hidden = 0\n"),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let typed = CompiledTypedSurface::from_lowering(&lowering, &namespace);
        let ops_path = vec!["ops".to_string()];
        let ops = namespace
            .modules
            .iter()
            .find(|module| module.path == ops_path)
            .unwrap();
        let x = ops.values.iter().find(|value| value.name == "x").unwrap();
        let id = ops.values.iter().find(|value| value.name == "id").unwrap();
        let hidden = ops
            .values
            .iter()
            .find(|value| value.name == "hidden")
            .unwrap();

        assert!(typed.values.iter().any(|value| value.symbol == x.symbol));
        assert!(
            !typed
                .values
                .iter()
                .any(|value| value.symbol == hidden.symbol)
        );

        let index = CompiledTypedIndex::new(&typed);
        assert!(index.value_scheme(x.symbol).is_some());
        assert!(index.value_scheme(hidden.symbol).is_none());

        let imported = {
            let source_scheme = index.value_scheme(id.symbol).unwrap();
            let mut target = crate::Arena::new();
            let mut importer = CompiledTypeImporter::new(&typed.types, &mut target);
            let imported = importer.import_scheme(source_scheme);
            let fresh_after_import = target.fresh_type_var();

            assert!(!source_scheme.quantifiers.is_empty());
            assert_ne!(imported.quantifiers, source_scheme.quantifiers);
            assert!(!imported.quantifiers.contains(&fresh_after_import));
            imported
        };
        assert_eq!(
            imported.quantifiers.len(),
            index.value_scheme(id.symbol).unwrap().quantifiers.len()
        );
        let mut poly_type_target = PolyArena::new();
        let mut poly_type_importer = CompiledTypeImporter::new(&typed.types, &mut poly_type_target);
        let poly_imported =
            poly_type_importer.import_scheme(index.value_scheme(id.symbol).unwrap());
        assert_eq!(poly_imported.quantifiers.len(), imported.quantifiers.len());
        assert!(poly_type_target.typ.node_len() > 0);

        let mut poly = PolyArena::new();
        let mut infer = crate::Arena::new();
        let imported_unit = typed.import_unit(&namespace, &mut poly, &mut infer);
        let imported_id = imported_unit.exported_value_def(&ops_path, "id").unwrap();
        assert_eq!(
            imported_unit.exported_value_def(&[], "id"),
            Some(imported_id)
        );
        assert_eq!(imported_unit.exported_value_def(&ops_path, "hidden"), None);
        let Some(Def::Let {
            vis: Vis::Pub,
            scheme: Some(imported_scheme),
            body: None,
            ..
        }) = poly.defs.get(imported_id)
        else {
            panic!("expected imported public bodyless let with a scheme");
        };
        assert_eq!(
            imported_scheme.quantifiers.len(),
            index.value_scheme(id.symbol).unwrap().quantifiers.len()
        );

        let restored_types = typed.types.to_type_arena();
        assert_eq!(
            restored_types.node_len(),
            lowering.session.poly.typ.node_len()
        );
    }

    #[test]
    fn canonical_cache_interface_handoff_freezes_once_for_typed_and_runtime_surfaces() {
        let loaded = sources::load(vec![source(
            &[],
            concat!(
                "my id x = x\n",
                "pub computed = id (\\x -> x)\n",
                "struct Token;\n",
                "role Echo 'a:\n",
                "  our x.echo: 'a\n",
                "impl Token: Echo:\n",
                "  our x.echo = x\n",
            ),
        )]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        assert!(lowering.errors.is_empty(), "{:?}", lowering.errors);
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);

        let surfaces = CompiledCacheInterfaceSurfaces::from_lowering(&lowering, &namespace)
            .expect("canonical cache-interface surface handoff");

        assert_eq!(surfaces.typed.boundary, surfaces.runtime.boundary);
        assert!(
            !surfaces.typed.boundary.bounds.is_empty(),
            "the expansive function result must retain its unit-owned boundary binder"
        );
        assert_eq!(
            surfaces.typed.types.pos,
            surfaces.runtime.arena.typ.pos_nodes()
        );
        assert_eq!(
            surfaces.typed.types.neg,
            surfaces.runtime.arena.typ.neg_nodes()
        );
        assert_eq!(
            surfaces.typed.types.neu,
            surfaces.runtime.arena.typ.neu_nodes()
        );

        let root = Vec::<String>::new();
        let symbol = crate::CompiledNamespaceIndex::new(&namespace)
            .exported_value_symbol(&root, "computed")
            .expect("computed symbol");
        let typed_scheme = CompiledTypedIndex::new(&surfaces.typed)
            .value_scheme(symbol)
            .expect("typed computed scheme");
        let runtime_def = surfaces
            .runtime
            .values
            .iter()
            .find(|value| value.symbol == symbol)
            .map(|value| value.def)
            .expect("runtime computed def");
        let Some(Def::Let {
            scheme: Some(runtime_scheme),
            ..
        }) = surfaces.runtime.arena.defs.get(runtime_def)
        else {
            panic!("runtime computed scheme");
        };
        assert_eq!(typed_scheme.quantifiers, runtime_scheme.quantifiers);
        assert_eq!(typed_scheme.role_predicates, runtime_scheme.role_predicates);
        assert_eq!(
            typed_scheme.recursive_bounds,
            runtime_scheme.recursive_bounds
        );
        assert_eq!(
            typed_scheme.stack_quantifiers,
            runtime_scheme.stack_quantifiers
        );
        assert_eq!(typed_scheme.predicate, runtime_scheme.predicate);

        for bound in &surfaces.typed.boundary.bounds {
            assert!(matches!(
                surfaces.runtime.arena.typ.neu(bound.bounds),
                Neu::Bounds(_, _)
            ));
        }
        let [candidate] = surfaces
            .runtime
            .arena
            .role_impls
            .candidates(&["Echo".to_string()])
        else {
            panic!("canonical runtime handoff must retain the frozen candidate")
        };
        assert!(candidate.prerequisites.is_empty());
    }

    #[test]
    fn canonical_cache_interface_handoff_rejects_an_unclosed_candidate_batch() {
        let loaded = sources::load(vec![source(&[], "pub value = 1\n")]);
        let mut lowering = lower_loaded_files(&loaded).unwrap();
        assert!(lowering.errors.is_empty(), "{:?}", lowering.errors);
        let head = lowering.session.infer.fresh_type_var();
        let prerequisite_only = lowering.session.infer.fresh_type_var();
        let head_input = {
            let lower = lowering.session.infer.alloc_pos(Pos::Var(head));
            let upper = lowering.session.infer.alloc_neg(Neg::Var(head));
            poly::roles::RoleConstraintArg { lower, upper }
        };
        let prerequisite_input = {
            let lower = lowering
                .session
                .infer
                .alloc_pos(Pos::Var(prerequisite_only));
            let upper = lowering
                .session
                .infer
                .alloc_neg(Neg::Var(prerequisite_only));
            poly::roles::RoleConstraintArg { lower, upper }
        };
        lowering
            .session
            .role_impls
            .insert(poly::roles::RoleImplCandidate {
                impl_def: None,
                role: vec!["UnclosedArtifactCandidate".into()],
                inputs: vec![head_input],
                associated: Vec::new(),
                prerequisites: vec![poly::roles::RoleConstraint {
                    role: vec!["UnclosedArtifactPrerequisite".into()],
                    inputs: vec![prerequisite_input],
                    associated: Vec::new(),
                }],
                methods: Vec::new(),
            });
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);

        let error = match CompiledCacheInterfaceSurfaces::from_lowering(&lowering, &namespace) {
            Ok(_) => panic!("an unclosed candidate must reject the complete surface handoff"),
            Err(error) => error,
        };

        assert_eq!(
            error,
            crate::analysis::BoundaryCaptureError::UnboundCandidateVariable {
                impl_def: None,
                role: vec!["UnclosedArtifactCandidate".into()],
                var: prerequisite_only,
            }
        );
        assert!(
            lowering
                .session
                .poly
                .role_impls
                .candidates(&["UnclosedArtifactCandidate".to_string()])
                .is_empty(),
            "failed canonical construction must not mutate the source lowering arena"
        );
    }

    #[test]
    fn typed_surface_from_prefixed_lowering_formats_prefix_and_suffix_schemes() {
        let prefix_loaded = sources::load(vec![
            source(&[], "mod prefix;\npub use prefix::*\n"),
            source(&["prefix"], "pub id x = x\n"),
        ]);
        let prefix = lower_loaded_files_prefix(&prefix_loaded).unwrap();
        let suffix_loaded = sources::load(vec![source(&[], "pub y = id 1\n")]);

        let lowering = lower_loaded_files_with_prefix(&prefix, &suffix_loaded).unwrap();
        assert_eq!(lowering.errors, Vec::new());

        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let typed = CompiledTypedSurface::from_lowering(&lowering, &namespace);
        let index = CompiledTypedIndex::new(&typed);
        let namespace_index = crate::CompiledNamespaceIndex::new(&namespace);
        let root = Vec::<String>::new();
        let id_symbol = namespace_index.exported_value_symbol(&root, "id").unwrap();
        let y_symbol = namespace_index.exported_value_symbol(&root, "y").unwrap();
        let restored_types = typed.types.to_type_arena();

        let id_type = poly::dump::format_scheme(
            &restored_types,
            index.value_scheme(id_symbol).expect("prefix id scheme"),
        );
        let y_type = poly::dump::format_scheme(
            &restored_types,
            index.value_scheme(y_symbol).expect("suffix y scheme"),
        );

        assert!(!id_type.is_empty());
        assert_eq!(y_type, "int");
    }

    #[test]
    fn typed_surface_merge_remaps_value_symbols_and_type_arena() {
        let left = compiled_typed_surface(&["left"], "pub id x = x\n");
        let right = compiled_typed_surface(&["right"], "pub id x = x\n");
        let namespace = CompiledNamespaceSurface::merge_prefixes_with_remap([
            &left.namespace,
            &right.namespace,
        ])
        .unwrap();
        let typed =
            CompiledTypedSurface::merge_prefixes([&left.typed, &right.typed], &namespace).unwrap();
        let namespace_index = crate::CompiledNamespaceIndex::new(&namespace.surface);
        let left_id = namespace_index
            .exported_value_symbol(&["left".to_string()], "id")
            .unwrap();
        let right_id = namespace_index
            .exported_value_symbol(&["right".to_string()], "id")
            .unwrap();
        let typed_index = CompiledTypedIndex::new(&typed);

        assert_eq!(
            namespace.map_value(0, left.value_symbol("id")),
            Some(left_id)
        );
        assert_eq!(
            namespace.map_value(1, right.value_symbol("id")),
            Some(right_id)
        );
        let left_scheme = typed_index.value_scheme(left_id).unwrap();
        let right_scheme = typed_index.value_scheme(right_id).unwrap();
        assert!(!left_scheme.quantifiers.is_empty());
        assert!(!right_scheme.quantifiers.is_empty());
        assert_ne!(left_scheme.quantifiers[0], right_scheme.quantifiers[0]);
        assert!(typed.types.pos.len() > 0);
        assert!(typed.boundary.bounds.is_empty());
    }

    #[test]
    fn typed_surface_merge_alpha_renames_boundary_scopes_disjointly() {
        let mut left = compiled_typed_surface(&["left"], "pub id x = x\n");
        let mut right = compiled_typed_surface(&["right"], "pub id x = x\n");
        install_boundary(&mut left.typed, TypeVar(50_000));
        install_boundary(&mut right.typed, TypeVar(50_000));
        let namespace = CompiledNamespaceSurface::merge_prefixes_with_remap([
            &left.namespace,
            &right.namespace,
        ])
        .unwrap();

        let typed =
            CompiledTypedSurface::merge_prefixes([&left.typed, &right.typed], &namespace).unwrap();

        assert_eq!(typed.boundary.bounds.len(), 2);
        assert_ne!(typed.boundary.bounds[0].var, typed.boundary.bounds[1].var);
        let types = typed.types.to_type_arena();
        for bound in &typed.boundary.bounds {
            let Neu::Bounds(lower, upper) = types.neu(bound.bounds) else {
                panic!("boundary bound should remain a neutral interval");
            };
            assert_eq!(types.pos(*lower), &Pos::Var(bound.var));
            assert_eq!(types.neg(*upper), &Neg::Var(bound.var));
        }
    }

    #[test]
    fn typed_surface_merge_rejects_value_symbol_without_namespace_remap() {
        let mut unit = compiled_typed_surface(&["unit"], "pub id x = x\n");
        let scheme = unit.typed.values[0].scheme.clone();
        unit.typed.values.push(CompiledTypedValueScheme {
            symbol: u32::MAX,
            scheme,
        });
        let namespace =
            CompiledNamespaceSurface::merge_prefixes_with_remap([&unit.namespace]).unwrap();
        let error = match CompiledTypedSurface::merge_prefixes([&unit.typed], &namespace) {
            Ok(_) => panic!("typed merge should reject a value without a namespace remap"),
            Err(error) => error,
        };

        assert_eq!(
            error,
            CompiledTypedMergeError::MissingValueSymbol {
                prefix: 0,
                symbol: u32::MAX,
            }
        );
    }

    struct TypedSurfaceFixture {
        path: Vec<String>,
        namespace: CompiledNamespaceSurface,
        typed: CompiledTypedSurface,
    }

    impl TypedSurfaceFixture {
        fn value_symbol(&self, name: &str) -> u32 {
            crate::CompiledNamespaceIndex::new(&self.namespace)
                .exported_value_symbol(&self.path, name)
                .unwrap()
        }
    }

    fn compiled_typed_surface(module: &[&str], text: &str) -> TypedSurfaceFixture {
        assert_eq!(module.len(), 1);
        let root = format!("mod {};\n", module[0]);
        let loaded = sources::load(vec![source(&[], &root), source(module, text)]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let typed = CompiledTypedSurface::from_lowering(&lowering, &namespace);
        TypedSurfaceFixture {
            path: module
                .iter()
                .map(|segment| (*segment).to_string())
                .collect(),
            namespace,
            typed,
        }
    }

    fn install_boundary(surface: &mut CompiledTypedSurface, var: TypeVar) {
        let mut types = surface.types.to_type_arena();
        let lower = types.alloc_pos(Pos::Var(var));
        let upper = types.alloc_neg(Neg::Var(var));
        let bounds = types.alloc_neu(Neu::Bounds(lower, upper));
        surface.types = CompiledTypeArena::from_type_arena(&types);
        surface.boundary = CompiledBoundaryInterface {
            bounds: vec![CompiledBoundaryBound { var, bounds }],
        };
    }

    fn structural_boundary_fixture(
        vars: [TypeVar; 2],
        reverse_entries: bool,
        padding_nodes: usize,
        marker: &str,
    ) -> (TypeArena, CompiledBoundaryInterface) {
        let mut types = TypeArena::new();
        for index in 0..padding_nodes {
            types.alloc_pos(Pos::Con(vec![format!("padding-{index}")], Vec::new()));
        }

        let first_lower = types.alloc_pos(Pos::Var(vars[0]));
        let first_upper = types.alloc_neg(Neg::Var(vars[0]));
        let first_bounds = types.alloc_neu(Neu::Bounds(first_lower, first_upper));

        let second_inner_lower = types.alloc_pos(Pos::Var(vars[1]));
        let second_inner_upper = types.alloc_neg(Neg::Var(vars[1]));
        let second_inner = types.alloc_neu(Neu::Bounds(second_inner_lower, second_inner_upper));
        let second_lower = types.alloc_pos(Pos::Con(vec![marker.to_string()], vec![second_inner]));
        let second_upper = types.alloc_neg(Neg::Con(vec![marker.to_string()], vec![second_inner]));
        let second_bounds = types.alloc_neu(Neu::Bounds(second_lower, second_upper));

        let mut bounds = vec![
            CompiledBoundaryBound {
                var: vars[0],
                bounds: first_bounds,
            },
            CompiledBoundaryBound {
                var: vars[1],
                bounds: second_bounds,
            },
        ];
        if reverse_entries {
            bounds.reverse();
        }
        (types, CompiledBoundaryInterface { bounds })
    }

    fn source(module: &[&str], text: &str) -> SourceFile {
        SourceFile {
            module_path: Path {
                segments: module
                    .iter()
                    .map(|segment| Name((*segment).to_string()))
                    .collect(),
            },
            source: text.to_string(),
        }
    }
}
