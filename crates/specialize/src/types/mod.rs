use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};

use mono::{
    EffectFamilies, EffectFamily, Signature, StackWeightEntry, Type, TypeField, TypeVariant,
};
use poly::expr as poly_expr;
use poly::provenance::{
    ProvenanceAnchor, ProvenanceCompleteness, SubtypeProvenanceSidecar, TypeOccurrenceOwner,
    TypeOccurrenceRole, TypePositionPath,
};
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicateArg, Scheme, StackWeight,
    Subtractability, TypeArena, TypeVar,
};

use crate::{SpecializeError, std_types};

mod collect;
mod match_types;
mod materialize;
mod setup;
mod type_ops;

pub(crate) use type_ops::*;

pub(crate) fn signature_for_scheme(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    expected: Option<&Type>,
) -> Result<Signature, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_open_vars(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    if let Some(expected) = expected {
        materializer.match_pos(scheme.predicate, expected, TypeContext::Value)?;
    }
    materializer.default_unbound_quantifiers();
    Ok(Signature {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
    })
}

pub(crate) fn role_predicates_for_scheme_signature(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    expected: Option<&Type>,
) -> Result<Vec<InstantiatedRolePredicate>, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    if let Some(expected) = expected {
        materializer.match_pos(scheme.predicate, expected, TypeContext::Value)?;
    }
    materializer.default_unbound_quantifiers();
    materializer.materialize_role_predicates(scheme)
}

pub(crate) fn instantiate_scheme_with_fresh_and_roles(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedScheme, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_open_vars(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    for quantifier in &scheme.quantifiers {
        let kind = materializer
            .kind_for(*quantifier)
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    Ok(InstantiatedScheme {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
        role_predicates: materializer.materialize_role_predicates(scheme)?,
        recursive_bounds: materializer.materialize_recursive_bounds(scheme)?,
    })
}

#[allow(dead_code)] // SUBP-I-2 shadow output; real task roots begin consuming this in SUBP-I-3.
pub(crate) fn instantiate_scheme_with_fresh_and_roles_with_provenance(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
    def: poly_expr::DefId,
    scheme: &Scheme,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedSchemeWithProvenance, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_open_vars(&arena.typ, def, scheme);
    materializer.collect_scheme_kinds(scheme);
    for quantifier in &scheme.quantifiers {
        let kind = materializer
            .kind_for(*quantifier)
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    finish_instantiated_scheme_with_provenance(
        &materializer,
        sidecar,
        def,
        scheme,
        materializer.materialize_recursive_bounds(scheme)?,
    )
}

pub(crate) fn instantiate_principal_scheme_for_inference_with_fresh_and_roles(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedScheme, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_all_vars(&arena.typ, def, scheme);
    materializer.use_inference_functions();
    materializer.use_inline_bounds();
    materializer.collect_scheme_kinds(scheme);
    for quantifier in &scheme.quantifiers {
        let kind = materializer
            .kind_for(*quantifier)
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    materializer.substitute_empty_bounds(&mut fresh);
    materializer.substitute_inline_bounds(&mut fresh);
    let mut recursive_bounds = materializer.materialize_inline_bounds()?;
    recursive_bounds.extend(materializer.materialize_recursive_bounds(scheme)?);
    Ok(InstantiatedScheme {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
        role_predicates: materializer.materialize_role_predicates(scheme)?,
        recursive_bounds,
    })
}

#[allow(dead_code)] // SUBP-I-2 shadow output; real task roots begin consuming this in SUBP-I-3.
pub(crate) fn instantiate_principal_scheme_for_inference_with_fresh_and_roles_with_provenance(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
    def: poly_expr::DefId,
    scheme: &Scheme,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedSchemeWithProvenance, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_all_vars(&arena.typ, def, scheme);
    materializer.use_inference_functions();
    materializer.use_inline_bounds();
    materializer.collect_scheme_kinds(scheme);
    for quantifier in &scheme.quantifiers {
        let kind = materializer
            .kind_for(*quantifier)
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    materializer.substitute_empty_bounds(&mut fresh);
    materializer.substitute_inline_bounds(&mut fresh);
    let mut recursive_bounds = materializer.materialize_inline_bounds()?;
    recursive_bounds.extend(materializer.materialize_recursive_bounds(scheme)?);
    finish_instantiated_scheme_with_provenance(
        &materializer,
        sidecar,
        def,
        scheme,
        recursive_bounds,
    )
}

pub(crate) fn instantiate_scheme_with_expected_fresh_and_roles(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    expected: &Type,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedScheme, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_all_vars(&arena.typ, def, scheme);
    materializer.use_inline_bounds();
    materializer.collect_scheme_kinds(scheme);
    materializer.match_pos(scheme.predicate, expected, TypeContext::Value)?;
    for quantifier in &scheme.quantifiers {
        if materializer.substitution.contains_key(quantifier) {
            continue;
        }
        let kind = materializer
            .kind_for(*quantifier)
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    materializer.substitute_empty_bounds(&mut fresh);
    materializer.substitute_inline_bounds(&mut fresh);
    let mut recursive_bounds = materializer.materialize_inline_bounds()?;
    recursive_bounds.extend(materializer.materialize_recursive_bounds(scheme)?);
    Ok(InstantiatedScheme {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
        role_predicates: materializer.materialize_role_predicates(scheme)?,
        recursive_bounds,
    })
}

#[allow(dead_code)] // SUBP-I-2 shadow output; real task roots begin consuming this in SUBP-I-3.
pub(crate) fn instantiate_scheme_with_expected_fresh_and_roles_with_provenance(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
    def: poly_expr::DefId,
    scheme: &Scheme,
    expected: &Type,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedSchemeWithProvenance, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_all_vars(&arena.typ, def, scheme);
    materializer.use_inline_bounds();
    materializer.collect_scheme_kinds(scheme);
    materializer.match_pos(scheme.predicate, expected, TypeContext::Value)?;
    for quantifier in &scheme.quantifiers {
        if materializer.substitution.contains_key(quantifier) {
            continue;
        }
        let kind = materializer
            .kind_for(*quantifier)
            .unwrap_or(QuantifierKind::Value);
        materializer
            .substitution
            .insert(*quantifier, fresh(kind.into()));
    }
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    materializer.substitute_empty_bounds(&mut fresh);
    materializer.substitute_inline_bounds(&mut fresh);
    let mut recursive_bounds = materializer.materialize_inline_bounds()?;
    recursive_bounds.extend(materializer.materialize_recursive_bounds(scheme)?);
    finish_instantiated_scheme_with_provenance(
        &materializer,
        sidecar,
        def,
        scheme,
        recursive_bounds,
    )
}

pub(crate) fn instantiate_monomorphic_scheme_with_fresh_and_roles(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    scheme: &Scheme,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedScheme, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_all_vars(&arena.typ, def, scheme);
    materializer.use_inline_bounds();
    materializer.collect_scheme_kinds(scheme);
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    materializer.substitute_empty_bounds(&mut fresh);
    materializer.substitute_inline_bounds(&mut fresh);
    let mut recursive_bounds = materializer.materialize_inline_bounds()?;
    recursive_bounds.extend(materializer.materialize_recursive_bounds(scheme)?);
    Ok(InstantiatedScheme {
        ty: materializer.materialize_pos(scheme.predicate, TypeContext::Value)?,
        role_predicates: materializer.materialize_role_predicates(scheme)?,
        recursive_bounds,
    })
}

#[allow(dead_code)] // SUBP-I-2 shadow output; real task roots begin consuming this in SUBP-I-3.
pub(crate) fn instantiate_monomorphic_scheme_with_fresh_and_roles_with_provenance(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
    def: poly_expr::DefId,
    scheme: &Scheme,
    mut fresh: impl FnMut(SchemeQuantifierKind) -> Type,
) -> Result<InstantiatedSchemeWithProvenance, SpecializeError> {
    reject_unsupported_scheme_features(def, scheme)?;
    let mut materializer = SchemeMaterializer::new_tracking_all_vars(&arena.typ, def, scheme);
    materializer.use_inline_bounds();
    materializer.collect_scheme_kinds(scheme);
    materializer.substitute_unbound_tracked_vars(&mut fresh);
    materializer.substitute_empty_bounds(&mut fresh);
    materializer.substitute_inline_bounds(&mut fresh);
    let mut recursive_bounds = materializer.materialize_inline_bounds()?;
    recursive_bounds.extend(materializer.materialize_recursive_bounds(scheme)?);
    finish_instantiated_scheme_with_provenance(
        &materializer,
        sidecar,
        def,
        scheme,
        recursive_bounds,
    )
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedScheme {
    pub(crate) ty: Type,
    pub(crate) role_predicates: Vec<InstantiatedRolePredicate>,
    pub(crate) recursive_bounds: Vec<InstantiatedRecursiveBound>,
}

/// Semantic scheme instantiation plus adjacent, non-semantic occurrence ownership.
///
/// This wrapper deliberately does not implement `Hash` and is never an instance key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstantiatedSchemeWithProvenance {
    pub(crate) scheme: InstantiatedScheme,
    pub(crate) provenance: MaterializedTypeProvenance,
}

fn finish_instantiated_scheme_with_provenance(
    materializer: &SchemeMaterializer<'_>,
    sidecar: &SubtypeProvenanceSidecar,
    def: poly_expr::DefId,
    scheme: &Scheme,
    recursive_bounds: Vec<InstantiatedRecursiveBound>,
) -> Result<InstantiatedSchemeWithProvenance, SpecializeError> {
    let materialized = materializer.materialize_pos_with_provenance(
        scheme.predicate,
        TypeContext::Value,
        sidecar,
        TypeOccurrenceOwner::Definition(def),
        TypeOccurrenceRole::DefinitionPredicate,
    )?;
    Ok(InstantiatedSchemeWithProvenance {
        scheme: InstantiatedScheme {
            ty: materialized.ty,
            role_predicates: materializer.materialize_role_predicates(scheme)?,
            recursive_bounds,
        },
        provenance: materialized.provenance,
    })
}

/// Semantic materialization plus adjacent, non-semantic occurrence ownership.
///
/// This wrapper deliberately does not implement `Hash` and is never an instance key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MaterializedTypeWithProvenance {
    pub(crate) ty: Type,
    pub(crate) provenance: MaterializedTypeProvenance,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MaterializedTypeProvenance {
    pub(crate) positions: Vec<MaterializedPositionProvenance>,
    pub(crate) completeness: ProvenanceCompleteness,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MaterializedPositionProvenance {
    pub(crate) path: TypePositionPath,
    pub(crate) anchors: Vec<ProvenanceAnchor>,
    pub(crate) completeness: ProvenanceCompleteness,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedRecursiveBound {
    pub(crate) value: Type,
    pub(crate) lower: Type,
    pub(crate) upper: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedRolePredicate {
    pub(crate) role: Vec<String>,
    pub(crate) inputs: Vec<InstantiatedRoleArg>,
    pub(crate) associated: Vec<InstantiatedRoleAssociatedType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedRoleArg {
    pub(crate) lower: Type,
    pub(crate) upper: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiatedRoleAssociatedType {
    pub(crate) name: String,
    pub(crate) lower: Type,
    pub(crate) upper: Type,
}

pub(crate) fn pure_function_type(arg: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(arg),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(Type::pure_effect()),
        ret: Box::new(ret),
    }
}

fn runtime_function_type(arg: Type, arg_effect: Type, ret_effect: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(runtime_shape(arg_effect, arg)),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(Type::pure_effect()),
        ret: Box::new(runtime_shape(ret_effect, ret)),
    }
}

fn inference_function_type(arg: Type, arg_effect: Type, ret_effect: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(arg),
        arg_effect: Box::new(arg_effect),
        ret_effect: Box::new(ret_effect),
        ret: Box::new(ret),
    }
}

pub(crate) fn runtime_shape(effect: Type, value: Type) -> Type {
    if effect.is_pure_effect() {
        return value;
    }
    Type::Thunk {
        effect: Box::new(effect),
        value: Box::new(value),
    }
}

fn split_runtime_shape(shape: &Type, legacy_effect: &Type) -> (Type, Type) {
    match shape {
        Type::Thunk { effect, value } => (value.as_ref().clone(), effect.as_ref().clone()),
        _ => (shape.clone(), legacy_effect.clone()),
    }
}

fn reject_unsupported_scheme_features(
    def: poly_expr::DefId,
    scheme: &Scheme,
) -> Result<(), SpecializeError> {
    let _ = def;
    let _ = scheme;
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SchemeQuantifierKind {
    Value,
    Effect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeContext {
    Value,
    Effect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FunctionMaterialization {
    Runtime,
    Inference,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundMaterialization {
    Structural,
    Fresh,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QuantifierKind {
    Value,
    Effect,
}

impl From<QuantifierKind> for SchemeQuantifierKind {
    fn from(kind: QuantifierKind) -> Self {
        match kind {
            QuantifierKind::Value => Self::Value,
            QuantifierKind::Effect => Self::Effect,
        }
    }
}

impl From<QuantifierKind> for TypeContext {
    fn from(kind: QuantifierKind) -> Self {
        match kind {
            QuantifierKind::Value => Self::Value,
            QuantifierKind::Effect => Self::Effect,
        }
    }
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

fn con_arg_context(path: &[String], index: usize) -> TypeContext {
    if std_types::is_ref_effect_arg(path, index) {
        TypeContext::Effect
    } else {
        TypeContext::Value
    }
}

struct SchemeMaterializer<'a> {
    arena: &'a TypeArena,
    def: poly_expr::DefId,
    quantifiers: HashSet<TypeVar>,
    substitution: HashMap<TypeVar, Type>,
    kinds: HashMap<TypeVar, QuantifierKind>,
    default_kinds: HashMap<TypeVar, QuantifierKind>,
    track_unquantified: bool,
    track_empty_bounds: bool,
    empty_bound_kinds: Vec<TypeContext>,
    empty_bound_types: RefCell<VecDeque<Type>>,
    function_materialization: FunctionMaterialization,
    bound_materialization: BoundMaterialization,
    inline_bound_kinds: HashMap<NeuId, QuantifierKind>,
    inline_bound_order: Vec<NeuId>,
    inline_bound_substitution: HashMap<NeuId, Type>,
}

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    use mono::Type;
    use poly::expr as poly_expr;
    use poly::provenance::{
        OccurrenceProvenance, ProvenanceAnchor, ProvenanceCompleteness, SubtypeProvenanceSidecar,
        TypeOccurrenceKey, TypeOccurrenceOwner, TypeOccurrenceRole, TypePositionIndex,
        TypePositionPath, TypePositionStep,
    };
    use poly::types::{Neg, Neu, Pos, RecordField, Scheme, TypeArena, TypeVar};

    use super::{
        InstantiatedScheme, InstantiatedSchemeWithProvenance, SchemeMaterializer,
        SchemeQuantifierKind, TypeContext, instantiate_monomorphic_scheme_with_fresh_and_roles,
        instantiate_monomorphic_scheme_with_fresh_and_roles_with_provenance,
        instantiate_principal_scheme_for_inference_with_fresh_and_roles,
        instantiate_principal_scheme_for_inference_with_fresh_and_roles_with_provenance,
        instantiate_scheme_with_expected_fresh_and_roles,
        instantiate_scheme_with_expected_fresh_and_roles_with_provenance,
        instantiate_scheme_with_fresh_and_roles,
        instantiate_scheme_with_fresh_and_roles_with_provenance, simplify_type,
    };

    #[test]
    fn instantiated_scheme_provenance_is_adjacent_to_semantic_hash_eq() {
        let (arena, scheme, sidecar, def) = quantified_definition_scheme_with_provenance();
        let semantic =
            instantiate_scheme_with_fresh_and_roles(&arena, def, &scheme, fresh_for_kind).unwrap();
        let shadow = instantiate_scheme_with_fresh_and_roles_with_provenance(
            &arena,
            &sidecar,
            def,
            &scheme,
            fresh_for_kind,
        )
        .unwrap();

        assert_eq!(shadow.scheme, semantic);
        assert_eq!(semantic_hash(&shadow.scheme), semantic_hash(&semantic));
        assert_definition_predicate_provenance(&shadow);
    }

    #[test]
    fn all_instantiation_provenance_variants_preserve_semantic_types() {
        let (arena, scheme, sidecar, def) = quantified_definition_scheme_with_provenance();

        let ordinary =
            instantiate_scheme_with_fresh_and_roles(&arena, def, &scheme, fresh_for_kind).unwrap();
        let ordinary_shadow = instantiate_scheme_with_fresh_and_roles_with_provenance(
            &arena,
            &sidecar,
            def,
            &scheme,
            fresh_for_kind,
        )
        .unwrap();
        assert_eq!(ordinary_shadow.scheme, ordinary);
        assert_definition_predicate_provenance(&ordinary_shadow);

        let principal = instantiate_principal_scheme_for_inference_with_fresh_and_roles(
            &arena,
            def,
            &scheme,
            fresh_for_kind,
        )
        .unwrap();
        let principal_shadow =
            instantiate_principal_scheme_for_inference_with_fresh_and_roles_with_provenance(
                &arena,
                &sidecar,
                def,
                &scheme,
                fresh_for_kind,
            )
            .unwrap();
        assert_eq!(principal_shadow.scheme, principal);
        assert_definition_predicate_provenance(&principal_shadow);

        let expected = int_type();
        let expected_semantic = instantiate_scheme_with_expected_fresh_and_roles(
            &arena,
            def,
            &scheme,
            &expected,
            fresh_for_kind,
        )
        .unwrap();
        let expected_shadow = instantiate_scheme_with_expected_fresh_and_roles_with_provenance(
            &arena,
            &sidecar,
            def,
            &scheme,
            &expected,
            fresh_for_kind,
        )
        .unwrap();
        assert_eq!(expected_shadow.scheme, expected_semantic);
        assert_definition_predicate_provenance(&expected_shadow);

        let monomorphic = instantiate_monomorphic_scheme_with_fresh_and_roles(
            &arena,
            def,
            &scheme,
            fresh_for_kind,
        )
        .unwrap();
        let monomorphic_shadow =
            instantiate_monomorphic_scheme_with_fresh_and_roles_with_provenance(
                &arena,
                &sidecar,
                def,
                &scheme,
                fresh_for_kind,
            )
            .unwrap();
        assert_eq!(monomorphic_shadow.scheme, monomorphic);
        assert_definition_predicate_provenance(&monomorphic_shadow);
    }

    #[test]
    fn provenance_shadow_preserves_semantic_type_and_projects_structural_paths() {
        let mut arena = poly_expr::Arena::new();
        let int = arena.typ.alloc_pos(Pos::Con(path(&["int"]), Vec::new()));
        let boolean = arena.typ.alloc_pos(Pos::Con(path(&["bool"]), Vec::new()));
        let record = arena.typ.alloc_pos(Pos::Record(vec![RecordField {
            name: "value".into(),
            value: int,
            optional: false,
        }]));
        let variant = arena
            .typ
            .alloc_pos(Pos::PolyVariant(vec![("some".into(), vec![boolean])]));
        let predicate = arena.typ.alloc_pos(Pos::Tuple(vec![record, variant]));
        let scheme = scheme(predicate, TypeVar(99));
        let owner = TypeOccurrenceOwner::Definition(poly_expr::DefId(0));
        let role = TypeOccurrenceRole::DefinitionPredicate;
        let record_path = TypePositionPath(vec![
            TypePositionStep::TupleElement(TypePositionIndex::from_usize(0)),
            TypePositionStep::RecordField {
                alternative: TypePositionIndex::from_usize(0),
                field: TypePositionIndex::from_usize(0),
            },
        ]);
        let variant_path = TypePositionPath(vec![
            TypePositionStep::TupleElement(TypePositionIndex::from_usize(1)),
            TypePositionStep::VariantPayload {
                alternative: TypePositionIndex::from_usize(0),
                item: TypePositionIndex::from_usize(0),
                payload: TypePositionIndex::from_usize(0),
            },
        ]);
        let mut sidecar = SubtypeProvenanceSidecar::empty();
        insert_occurrence(&mut sidecar, owner, role, record_path.clone(), 3);
        insert_occurrence(&mut sidecar, owner, role, variant_path.clone(), 7);

        let materializer = SchemeMaterializer::new(&arena.typ, poly_expr::DefId(0), &scheme);
        let semantic = materializer
            .materialize_pos(predicate, TypeContext::Value)
            .unwrap();
        let shadow = materializer
            .materialize_pos_with_provenance(predicate, TypeContext::Value, &sidecar, owner, role)
            .unwrap();

        assert_eq!(shadow.ty, semantic);
        assert_eq!(
            shadow.provenance.completeness,
            ProvenanceCompleteness::Complete
        );
        assert_eq!(
            shadow
                .provenance
                .positions
                .iter()
                .map(|position| (position.path.clone(), position.anchors.clone()))
                .collect::<Vec<_>>(),
            vec![
                (record_path, vec![ProvenanceAnchor::from_index(3)]),
                (variant_path, vec![ProvenanceAnchor::from_index(7)]),
            ]
        );
    }

    #[test]
    fn provenance_shadow_keeps_shared_poly_nodes_occurrence_specific() {
        let mut arena = poly_expr::Arena::new();
        let shared = arena.typ.alloc_pos(Pos::Con(path(&["int"]), Vec::new()));
        let predicate = arena.typ.alloc_pos(Pos::Tuple(vec![shared, shared]));
        let scheme = scheme(predicate, TypeVar(99));
        let role = TypeOccurrenceRole::ExpressionActual;
        let owner = TypeOccurrenceOwner::Expression(poly_expr::ExprId(4));
        let first = TypePositionPath(vec![TypePositionStep::TupleElement(
            TypePositionIndex::from_usize(0),
        )]);
        let second = TypePositionPath(vec![TypePositionStep::TupleElement(
            TypePositionIndex::from_usize(1),
        )]);
        let mut sidecar = SubtypeProvenanceSidecar::empty();
        insert_occurrence(&mut sidecar, owner, role, first.clone(), 1);
        insert_occurrence(&mut sidecar, owner, role, second.clone(), 2);

        let shadow = SchemeMaterializer::new(&arena.typ, poly_expr::DefId(0), &scheme)
            .materialize_pos_with_provenance(predicate, TypeContext::Value, &sidecar, owner, role)
            .unwrap();

        assert_eq!(shadow.provenance.positions.len(), 2);
        assert_eq!(shadow.provenance.positions[0].path, first);
        assert_eq!(
            shadow.provenance.positions[0].anchors,
            vec![ProvenanceAnchor::from_index(1)]
        );
        assert_eq!(shadow.provenance.positions[1].path, second);
        assert_eq!(
            shadow.provenance.positions[1].anchors,
            vec![ProvenanceAnchor::from_index(2)]
        );
    }

    #[test]
    fn provenance_shadow_marks_coalescing_transformations_incomplete() {
        let mut arena = poly_expr::Arena::new();
        let int = arena.typ.alloc_pos(Pos::Con(path(&["int"]), Vec::new()));
        let boolean = arena.typ.alloc_pos(Pos::Con(path(&["bool"]), Vec::new()));
        let predicate = arena.typ.alloc_pos(Pos::Union(int, boolean));
        let scheme = scheme(predicate, TypeVar(99));
        let owner = TypeOccurrenceOwner::Expression(poly_expr::ExprId(5));
        let role = TypeOccurrenceRole::ExpressionActual;
        let mut sidecar = SubtypeProvenanceSidecar::empty();
        insert_occurrence(&mut sidecar, owner, role, TypePositionPath::default(), 8);

        let shadow = SchemeMaterializer::new(&arena.typ, poly_expr::DefId(0), &scheme)
            .materialize_pos_with_provenance(predicate, TypeContext::Value, &sidecar, owner, role)
            .unwrap();

        assert_eq!(
            shadow.provenance.completeness,
            ProvenanceCompleteness::Incomplete
        );
        assert_eq!(shadow.provenance.positions.len(), 1);
        assert_eq!(
            shadow.provenance.positions[0].anchors,
            vec![ProvenanceAnchor::from_index(8)]
        );
        assert_eq!(
            shadow.provenance.positions[0].completeness,
            ProvenanceCompleteness::Incomplete
        );
    }

    #[test]
    fn provenance_shadow_marks_substitution_spread_and_runtime_shape_incomplete() {
        let owner = TypeOccurrenceOwner::Expression(poly_expr::ExprId(7));
        let role = TypeOccurrenceRole::ExpressionActual;
        let mut sidecar = SubtypeProvenanceSidecar::empty();
        insert_occurrence(&mut sidecar, owner, role, TypePositionPath::default(), 9);

        let mut substitution_arena = poly_expr::Arena::new();
        let var = TypeVar(0);
        let predicate = substitution_arena.typ.alloc_pos(Pos::Var(var));
        let substitution_scheme = scheme(predicate, var);
        let mut materializer = SchemeMaterializer::new(
            &substitution_arena.typ,
            poly_expr::DefId(0),
            &substitution_scheme,
        );
        materializer.substitution.insert(var, int_type());
        let substitution = materializer
            .materialize_pos_with_provenance(predicate, TypeContext::Value, &sidecar, owner, role)
            .unwrap();
        assert_eq!(substitution.ty, int_type());
        assert_eq!(
            substitution.provenance.completeness,
            ProvenanceCompleteness::Incomplete
        );

        let mut spread_arena = poly_expr::Arena::new();
        let int = spread_arena
            .typ
            .alloc_pos(Pos::Con(path(&["int"]), Vec::new()));
        let tail = spread_arena.typ.alloc_pos(Pos::Record(vec![RecordField {
            name: "tail".into(),
            value: int,
            optional: false,
        }]));
        let predicate = spread_arena.typ.alloc_pos(Pos::RecordTailSpread {
            fields: Vec::new(),
            tail,
        });
        let spread_scheme = scheme(predicate, TypeVar(99));
        let spread =
            SchemeMaterializer::new(&spread_arena.typ, poly_expr::DefId(0), &spread_scheme)
                .materialize_pos_with_provenance(
                    predicate,
                    TypeContext::Value,
                    &sidecar,
                    owner,
                    role,
                )
                .unwrap();
        assert_eq!(
            spread.provenance.completeness,
            ProvenanceCompleteness::Incomplete
        );

        let mut function_arena = poly_expr::Arena::new();
        let arg = function_arena
            .typ
            .alloc_neg(Neg::Con(path(&["bool"]), Vec::new()));
        let arg_eff = function_arena.typ.alloc_neg(Neg::Top);
        let ret_eff = function_arena.typ.alloc_pos(Pos::Bot);
        let ret = function_arena
            .typ
            .alloc_pos(Pos::Con(path(&["int"]), Vec::new()));
        let predicate = function_arena.typ.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        let function_scheme = scheme(predicate, TypeVar(99));
        let function =
            SchemeMaterializer::new(&function_arena.typ, poly_expr::DefId(0), &function_scheme)
                .materialize_pos_with_provenance(
                    predicate,
                    TypeContext::Value,
                    &sidecar,
                    owner,
                    role,
                )
                .unwrap();
        assert_eq!(
            function.provenance.completeness,
            ProvenanceCompleteness::Incomplete
        );
    }

    #[test]
    fn provenance_shadow_enforces_materialized_path_budget() {
        let mut arena = poly_expr::Arena::new();
        let owner = TypeOccurrenceOwner::Expression(poly_expr::ExprId(6));
        let role = TypeOccurrenceRole::ExpressionActual;
        let mut sidecar = SubtypeProvenanceSidecar::empty();
        let mut items = Vec::new();
        for index in 0..300 {
            items.push(arena.typ.alloc_pos(Pos::Con(path(&["int"]), Vec::new())));
            insert_occurrence(
                &mut sidecar,
                owner,
                role,
                TypePositionPath(vec![TypePositionStep::TupleElement(
                    TypePositionIndex::from_usize(index),
                )]),
                index,
            );
        }
        let predicate = arena.typ.alloc_pos(Pos::Tuple(items));
        let scheme = scheme(predicate, TypeVar(99));

        let shadow = SchemeMaterializer::new(&arena.typ, poly_expr::DefId(0), &scheme)
            .materialize_pos_with_provenance(predicate, TypeContext::Value, &sidecar, owner, role)
            .unwrap();

        assert_eq!(shadow.provenance.positions.len(), 256);
        assert_eq!(
            shadow.provenance.completeness,
            ProvenanceCompleteness::Incomplete
        );
    }

    #[test]
    fn nominal_arg_default_value_kind_loses_to_structural_ref_effect_kind() {
        let mut arena = poly_expr::Arena::new();
        let effect_var = TypeVar(0);
        let effect = bounds_var(&mut arena.typ, effect_var);
        let str_ty = con_neu(&mut arena.typ, &["str"]);
        let lines = arena.typ.alloc_pos(Pos::Con(
            path(&["std", "text", "str", "ref_lines"]),
            vec![effect],
        ));
        let source = arena
            .typ
            .alloc_pos(Pos::Con(ref_path(), vec![effect, str_ty]));
        let predicate = arena.typ.alloc_pos(Pos::Tuple(vec![lines, source]));
        let scheme = scheme(predicate, effect_var);

        let instantiated = instantiate_principal_scheme_for_inference_with_fresh_and_roles(
            &arena,
            poly_expr::DefId(0),
            &scheme,
            fresh_for_kind,
        )
        .unwrap();

        assert_eq!(
            instantiated.ty,
            Type::Tuple(vec![
                Type::Con {
                    path: path(&["std", "text", "str", "ref_lines"]),
                    args: vec![Type::OpenVar(200)],
                },
                Type::Con {
                    path: ref_path(),
                    args: vec![Type::OpenVar(200), str_type()],
                },
            ])
        );
    }

    #[test]
    fn nominal_arg_default_kind_stays_value_without_structural_effect_use() {
        let mut arena = poly_expr::Arena::new();
        let value_var = TypeVar(0);
        let value = bounds_var(&mut arena.typ, value_var);
        let predicate = arena.typ.alloc_pos(Pos::Con(
            path(&["std", "text", "str", "ref_lines"]),
            vec![value],
        ));
        let scheme = scheme(predicate, value_var);

        let instantiated = instantiate_principal_scheme_for_inference_with_fresh_and_roles(
            &arena,
            poly_expr::DefId(0),
            &scheme,
            fresh_for_kind,
        )
        .unwrap();

        assert_eq!(
            instantiated.ty,
            Type::Con {
                path: path(&["std", "text", "str", "ref_lines"]),
                args: vec![Type::OpenVar(100)],
            }
        );
    }

    #[test]
    fn effect_row_intersection_deduplicates_repeated_family() {
        let nondet = effect("nondet");
        let ty = simplify_type(Type::Intersection(
            Box::new(Type::EffectRow(vec![nondet.clone()])),
            Box::new(Type::EffectRow(vec![nondet.clone(), nondet.clone()])),
        ));

        assert_eq!(ty, Type::EffectRow(vec![nondet]));
    }

    #[test]
    fn effect_row_flattens_simplified_tail() {
        let nondet = effect("nondet");
        let tail = Type::Intersection(
            Box::new(Type::EffectRow(vec![nondet.clone()])),
            Box::new(Type::EffectRow(vec![nondet.clone(), nondet.clone()])),
        );
        let ty = simplify_type(Type::EffectRow(vec![nondet.clone(), tail]));

        assert_eq!(ty, Type::EffectRow(vec![nondet]));
    }

    #[test]
    fn effect_row_union_deduplicates_repeated_family() {
        let nondet = effect("nondet");
        let ty = simplify_type(Type::Union(
            Box::new(Type::EffectRow(vec![nondet.clone()])),
            Box::new(Type::EffectRow(vec![nondet.clone(), nondet.clone()])),
        ));

        assert_eq!(ty, Type::EffectRow(vec![nondet]));
    }

    #[test]
    fn value_union_keeps_open_var_with_concrete_candidate() {
        let ty = simplify_type(Type::Union(
            Box::new(Type::OpenVar(0)),
            Box::new(int_type()),
        ));

        assert!(matches!(ty, Type::Union(_, _)), "{ty:?}");
    }

    #[test]
    fn value_intersection_keeps_open_var_with_concrete_candidate() {
        let ty = simplify_type(Type::Intersection(
            Box::new(Type::OpenVar(0)),
            Box::new(int_type()),
        ));

        assert!(matches!(ty, Type::Intersection(_, _)), "{ty:?}");
    }

    fn int_type() -> Type {
        Type::Con {
            path: vec!["int".to_string()],
            args: Vec::new(),
        }
    }

    fn effect(name: &str) -> Type {
        Type::Con {
            path: vec![name.to_string()],
            args: Vec::new(),
        }
    }

    fn fresh_for_kind(kind: SchemeQuantifierKind) -> Type {
        match kind {
            SchemeQuantifierKind::Value => Type::OpenVar(100),
            SchemeQuantifierKind::Effect => Type::OpenVar(200),
        }
    }

    fn quantified_definition_scheme_with_provenance() -> (
        poly_expr::Arena,
        Scheme,
        SubtypeProvenanceSidecar,
        poly_expr::DefId,
    ) {
        let mut arena = poly_expr::Arena::new();
        let quantifier = TypeVar(99);
        let predicate = arena.typ.alloc_pos(Pos::Var(quantifier));
        let scheme = scheme(predicate, quantifier);
        let def = poly_expr::DefId(0);
        let mut sidecar = SubtypeProvenanceSidecar::empty();
        insert_occurrence(
            &mut sidecar,
            TypeOccurrenceOwner::Definition(def),
            TypeOccurrenceRole::DefinitionPredicate,
            TypePositionPath::default(),
            11,
        );
        (arena, scheme, sidecar, def)
    }

    fn assert_definition_predicate_provenance(materialized: &InstantiatedSchemeWithProvenance) {
        assert_eq!(
            materialized.provenance.completeness,
            ProvenanceCompleteness::Incomplete
        );
        assert_eq!(materialized.provenance.positions.len(), 1);
        assert_eq!(
            materialized.provenance.positions[0].path,
            TypePositionPath::default()
        );
        assert_eq!(
            materialized.provenance.positions[0].anchors,
            vec![ProvenanceAnchor::from_index(11)]
        );
    }

    fn semantic_hash(scheme: &InstantiatedScheme) -> u64 {
        let mut hasher = DefaultHasher::new();
        scheme.hash(&mut hasher);
        hasher.finish()
    }

    fn scheme(predicate: poly::types::PosId, quantifier: TypeVar) -> Scheme {
        Scheme {
            quantifiers: vec![quantifier],
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        }
    }

    fn bounds_var(typ: &mut TypeArena, var: TypeVar) -> poly::types::NeuId {
        let lower = typ.alloc_pos(Pos::Var(var));
        let upper = typ.alloc_neg(Neg::Var(var));
        typ.alloc_neu(Neu::Bounds(lower, upper))
    }

    fn con_neu(typ: &mut TypeArena, names: &[&str]) -> poly::types::NeuId {
        typ.alloc_neu(Neu::Con(path(names), Vec::new()))
    }

    fn str_type() -> Type {
        Type::Con {
            path: path(&["str"]),
            args: Vec::new(),
        }
    }

    fn ref_path() -> Vec<String> {
        path(&["std", "control", "var", "ref"])
    }

    fn path(names: &[&str]) -> Vec<String> {
        names.iter().map(|name| (*name).to_string()).collect()
    }

    fn insert_occurrence(
        sidecar: &mut SubtypeProvenanceSidecar,
        owner: TypeOccurrenceOwner,
        role: TypeOccurrenceRole,
        path: TypePositionPath,
        anchor: usize,
    ) {
        sidecar.occurrences.insert(
            TypeOccurrenceKey { owner, role, path },
            OccurrenceProvenance {
                anchors: vec![ProvenanceAnchor::from_index(anchor)],
                completeness: ProvenanceCompleteness::Complete,
            },
        );
    }
}
