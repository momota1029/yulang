//! Detached scheme closure for nominal act templates.
//!
//! M1-2 captures finalized member schemes into an arena that is independent of the lowering run.
//! The capture/apply API is shadow-only: synthetic act copies still take the legacy CST path.

#![allow(dead_code, reason = "M1-2 is shadow-only until M1-3 consumes it")]

use super::nominal_act_identity::{
    NominalActInstanceSubstitution, NominalActTemplateIdentity, NominalActValueMemberKind,
};
use crate::{DefId, TypeDeclId, TypeMethodReceiver};
use poly::expr::{Arena as PolyArena, Def};
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RoleAssociatedType, RolePredicate,
    RolePredicateArg, Scheme, SchemeRecursiveBound, StackWeight, Subtractability, TypeArena,
};
#[cfg(test)]
use poly::types::{SubtractId, TypeVar};
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

/// Finalized schemes and their reachable type graph for one nominal act template.
///
/// `source` IDs only identify members inside the capture run. Paths which cross that boundary are
/// retained as [`StableExternalReferenceKey`] values rather than arena-local definition IDs.
pub(crate) struct TypedActTemplate {
    pub(crate) template_root_act: TypeDeclId,
    pub(crate) internal_nominal_paths: Vec<Vec<String>>,
    pub(crate) members: Vec<TypedActTemplateMember>,
    pub(crate) types: TypeArena,
    pub(crate) external_references: FxHashSet<StableExternalReferenceKey>,
}

pub(crate) struct TypedActTemplateMember {
    pub(crate) key: NominalActMemberKey,
    pub(crate) source: DefId,
    pub(crate) scheme: Scheme,
}

/// Arena-independent identity for a value inside the captured nominal namespace closure.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) struct NominalActMemberKey {
    pub(crate) owner_relative_path: Vec<String>,
    pub(crate) kind: NominalActMemberKeyKind,
    pub(crate) name: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum NominalActMemberKeyKind {
    Operation,
    Binding,
    Constructor,
    FieldMethodValue,
    FieldMethodRef,
}

/// Stable key for a reference which is outside a captured template closure.
///
/// M1-2 emits `NominalPath` keys from scheme/type graphs. The remaining variants fix the portable
/// key space which M1-3 body capture will use for value, operation, and field-method references.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum StableExternalReferenceKey {
    NominalPath(Vec<String>),
    ValuePath(Vec<String>),
    Operation {
        family: Vec<String>,
        name: String,
    },
    FieldMethod {
        owner: Vec<String>,
        name: String,
        receiver: StableReceiverKind,
    },
    Method {
        owner: Vec<String>,
        name: String,
        receiver: StableReceiverKind,
    },
    Constructor {
        owner: Vec<String>,
        name: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum StableReceiverKind {
    Value,
    Ref,
}

impl super::ModuleTable {
    /// Resolve an arena-local definition to the portable key M1-3 body capture will retain.
    pub(crate) fn stable_external_reference_key(
        &self,
        def: DefId,
    ) -> Option<StableExternalReferenceKey> {
        if let Some(operation) = self.act_operation_decl_by_def(def) {
            return Some(StableExternalReferenceKey::Operation {
                family: path_names(&self.type_decl_path(&operation.effect)),
                name: operation.name.0,
            });
        }
        if let Some(constructor) = self.constructor_by_def(def) {
            let owner = self.type_decl_by_id(constructor.owner)?;
            let name = self
                .module_value_decls(constructor.module)
                .into_iter()
                .find(|value| value.def == def)?
                .name;
            return Some(StableExternalReferenceKey::Constructor {
                owner: path_names(&self.type_decl_path(&owner)),
                name: name.0,
            });
        }
        if let Some(method) = self.all_type_methods().find(|method| method.def == def) {
            let owner = self.type_decl_by_id(method.owner)?;
            return Some(StableExternalReferenceKey::Method {
                owner: path_names(&self.type_decl_path(&owner)),
                name: method.name.0.clone(),
                receiver: match method.receiver_kind {
                    TypeMethodReceiver::Value => StableReceiverKind::Value,
                    TypeMethodReceiver::Ref => StableReceiverKind::Ref,
                },
            });
        }
        if let Some(method) = self
            .all_type_field_methods()
            .find(|method| method.def == def)
        {
            let owner = self.type_decl_by_id(method.owner)?;
            return Some(StableExternalReferenceKey::FieldMethod {
                owner: path_names(&self.type_decl_path(&owner)),
                name: method.name.0.clone(),
                receiver: match method.receiver_kind {
                    TypeMethodReceiver::Value => StableReceiverKind::Value,
                    TypeMethodReceiver::Ref => StableReceiverKind::Ref,
                },
            });
        }
        for index in 0..self.nodes.len() {
            let module = crate::ModuleId(index);
            if let Some(value) = self
                .module_value_decls(module)
                .into_iter()
                .find(|value| value.def == def)
            {
                let mut path = path_names(&self.module_path(module));
                path.push(value.name.0);
                return Some(StableExternalReferenceKey::ValuePath(path));
            }
        }
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TypedActTemplateError {
    MissingClosedScheme {
        member: DefId,
    },
    WrongTemplateRoot {
        expected: TypeDeclId,
        actual: TypeDeclId,
    },
    MissingDestinationTypePath {
        source: Vec<String>,
    },
    MissingDestinationMember {
        source: DefId,
    },
    MalformedTemplateIdentity,
}

/// One shadow application result. Nothing installs these schemes into production definitions yet.
pub(crate) struct TypedActSchemeInstantiation {
    pub(crate) destination_root_act: TypeDeclId,
    pub(crate) members: Vec<TypedActSchemeInstantiationMember>,
    pub(crate) types: TypeArena,
}

pub(crate) struct TypedActSchemeInstantiationMember {
    pub(crate) key: NominalActMemberKey,
    pub(crate) destination: DefId,
    pub(crate) scheme: Scheme,
}

impl TypedActTemplate {
    /// Capture only the type closure reachable from finalized template-member schemes.
    pub(crate) fn capture(
        identity: &NominalActTemplateIdentity,
        poly: &PolyArena,
    ) -> Result<Self, TypedActTemplateError> {
        let root_path = identity
            .nominal_types
            .iter()
            .find(|nominal| nominal.source == identity.root_act)
            .map(|nominal| path_names(&nominal.source_path))
            .ok_or(TypedActTemplateError::MalformedTemplateIdentity)?;
        let internal_paths = identity
            .nominal_types
            .iter()
            .map(|nominal| {
                let path = path_names(&nominal.source_path);
                (path.clone(), path)
            })
            .collect();
        let mut types = TypeArena::new();
        let mut external_references = FxHashSet::default();
        let members = {
            let mut cloner = NominalTypeGraphCloner::new(
                &poly.typ,
                &mut types,
                &internal_paths,
                Some(&mut external_references),
            );
            identity
                .value_members
                .iter()
                .map(|member| {
                    let Some(Def::Let {
                        scheme: Some(scheme),
                        ..
                    }) = poly.defs.get(member.source)
                    else {
                        return Err(TypedActTemplateError::MissingClosedScheme {
                            member: member.source,
                        });
                    };
                    Ok(TypedActTemplateMember {
                        key: member_key(identity, member, &root_path)?,
                        source: member.source,
                        scheme: cloner.clone_scheme(scheme),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?
        };
        Ok(Self {
            template_root_act: identity.root_act,
            internal_nominal_paths: internal_paths.keys().cloned().collect(),
            members,
            types,
            external_references,
        })
    }

    /// Apply the M1-1 nominal shell mapping without installing the result into lowering.
    pub(crate) fn apply(
        &self,
        substitution: &NominalActInstanceSubstitution,
    ) -> Result<TypedActSchemeInstantiation, TypedActTemplateError> {
        if substitution.template_root_act != self.template_root_act {
            return Err(TypedActTemplateError::WrongTemplateRoot {
                expected: self.template_root_act,
                actual: substitution.template_root_act,
            });
        }
        let path_substitution = substitution
            .type_path_map
            .iter()
            .map(|(source, destination)| (path_names(source), path_names(destination)))
            .collect::<FxHashMap<_, _>>();
        for source in &self.internal_nominal_paths {
            if !path_substitution.contains_key(source.as_slice()) {
                return Err(TypedActTemplateError::MissingDestinationTypePath {
                    source: source.clone(),
                });
            }
        }
        let mut types = TypeArena::new();
        let members = {
            let mut cloner =
                NominalTypeGraphCloner::new(&self.types, &mut types, &path_substitution, None);
            self.members
                .iter()
                .map(|member| {
                    let destination = substitution.def_map.get(&member.source).copied().ok_or(
                        TypedActTemplateError::MissingDestinationMember {
                            source: member.source,
                        },
                    )?;
                    Ok(TypedActSchemeInstantiationMember {
                        key: member.key.clone(),
                        destination,
                        scheme: cloner.clone_scheme(&member.scheme),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?
        };
        Ok(TypedActSchemeInstantiation {
            destination_root_act: substitution.destination_root_act,
            members,
            types,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn m1_2_nominal_graph_substitution_covers_every_current_type_variant() {
        let source_path = vec!["source".into(), "family".into()];
        let destination_path = vec!["destination".into(), "family".into()];
        let external_path = vec!["external".into(), "family".into()];
        let mut source = TypeArena::new();
        let pos_bot = source.alloc_pos(Pos::Bot);
        let pos_var = source.alloc_pos(Pos::Var(TypeVar(0)));
        let neg_top = source.alloc_neg(Neg::Top);
        let neg_bot = source.alloc_neg(Neg::Bot);
        let neg_var = source.alloc_neg(Neg::Var(TypeVar(1)));
        let neu_bounds = source.alloc_neu(Neu::Bounds(pos_bot, neg_top));
        let neu_internal = source.alloc_neu(Neu::Con(source_path.clone(), vec![neu_bounds]));
        let neu_external = source.alloc_neu(Neu::Con(external_path.clone(), vec![]));
        let neu_fun = source.alloc_neu(Neu::Fun {
            arg: neu_bounds,
            arg_eff: neu_internal,
            ret_eff: neu_external,
            ret: neu_bounds,
        });
        let neu_record = source.alloc_neu(Neu::Record(vec![RecordField {
            name: "field".into(),
            value: neu_internal,
            optional: false,
        }]));
        let neu_variant =
            source.alloc_neu(Neu::PolyVariant(vec![("tag".into(), vec![neu_external])]));
        let neu_tuple = source.alloc_neu(Neu::Tuple(vec![neu_fun, neu_record, neu_variant]));

        let weight = all_subtractability_forms(&source_path, &external_path, neu_internal);
        let neg_con = source.alloc_neg(Neg::Con(source_path.clone(), vec![neu_tuple]));
        let neg_fun = source.alloc_neg(Neg::Fun {
            arg: pos_var,
            arg_eff: pos_bot,
            ret_eff: neg_top,
            ret: neg_var,
        });
        let neg_record = source.alloc_neg(Neg::Record(vec![RecordField {
            name: "field".into(),
            value: neg_con,
            optional: true,
        }]));
        let neg_variant = source.alloc_neg(Neg::PolyVariant(vec![("tag".into(), vec![neg_fun])]));
        let neg_tuple = source.alloc_neg(Neg::Tuple(vec![neg_record, neg_variant, neg_bot]));
        let neg_row = source.alloc_neg(Neg::Row(vec![neg_con, neg_fun], neg_top));
        let neg_stack = source.alloc_neg(Neg::Stack {
            inner: neg_tuple,
            weight: weight.clone(),
        });
        let neg_intersection = source.alloc_neg(Neg::Intersection(neg_row, neg_stack));
        let all_neg_bounds = [
            neg_top,
            neg_bot,
            neg_var,
            neg_con,
            neg_fun,
            neg_record,
            neg_variant,
            neg_tuple,
            neg_row,
            neg_stack,
            neg_intersection,
        ]
        .into_iter()
        .map(|upper| source.alloc_neu(Neu::Bounds(pos_bot, upper)))
        .collect();
        let all_neg_bounds = source.alloc_neu(Neu::Tuple(all_neg_bounds));

        let pos_con = source.alloc_pos(Pos::Con(
            source_path.clone(),
            vec![neu_tuple, all_neg_bounds],
        ));
        let pos_fun = source.alloc_pos(Pos::Fun {
            arg: neg_intersection,
            arg_eff: neg_row,
            ret_eff: pos_bot,
            ret: pos_var,
        });
        let pos_record = source.alloc_pos(Pos::Record(vec![RecordField {
            name: "field".into(),
            value: pos_con,
            optional: false,
        }]));
        let pos_tail = source.alloc_pos(Pos::RecordTailSpread {
            fields: vec![RecordField {
                name: "tail".into(),
                value: pos_fun,
                optional: false,
            }],
            tail: pos_record,
        });
        let pos_head = source.alloc_pos(Pos::RecordHeadSpread {
            tail: pos_record,
            fields: vec![RecordField {
                name: "head".into(),
                value: pos_tail,
                optional: true,
            }],
        });
        let pos_variant = source.alloc_pos(Pos::PolyVariant(vec![("tag".into(), vec![pos_head])]));
        let pos_row = source.alloc_pos(Pos::Row(vec![pos_con, pos_fun]));
        let pos_stack = source.alloc_pos(Pos::Stack {
            inner: pos_variant,
            weight: weight.clone(),
        });
        let pos_non_subtract = source.alloc_pos(Pos::NonSubtract(pos_row, weight));
        let pos_union = source.alloc_pos(Pos::Union(pos_stack, pos_non_subtract));
        let predicate = source.alloc_pos(Pos::Tuple(vec![
            pos_bot,
            pos_var,
            pos_con,
            pos_fun,
            pos_record,
            pos_tail,
            pos_head,
            pos_variant,
            pos_row,
            pos_stack,
            pos_non_subtract,
            pos_union,
        ]));
        let scheme = Scheme {
            quantifiers: vec![TypeVar(0), TypeVar(1)],
            role_predicates: vec![RolePredicate {
                role: source_path.clone(),
                inputs: vec![
                    RolePredicateArg::Covariant(pos_con),
                    RolePredicateArg::Contravariant(neg_con),
                    RolePredicateArg::Invariant(neu_internal),
                ],
                associated: vec![RoleAssociatedType {
                    name: "out".into(),
                    value: neu_external,
                }],
            }],
            recursive_bounds: vec![SchemeRecursiveBound {
                var: TypeVar(1),
                bounds: neu_tuple,
            }],
            stack_quantifiers: vec![SubtractId(0)],
            predicate,
        };

        let paths = FxHashMap::from_iter([(source_path.clone(), destination_path.clone())]);
        let mut target = TypeArena::new();
        let mut external = FxHashSet::default();
        let cloned = NominalTypeGraphCloner::new(&source, &mut target, &paths, Some(&mut external))
            .clone_scheme(&scheme);
        let rendered = poly::dump::format_scheme(&target, &cloned);
        assert!(rendered.contains("destination::family"), "{rendered}");
        assert!(rendered.contains("external::family"), "{rendered}");
        assert!(!rendered.contains("source::family"), "{rendered}");
        assert!(external.contains(&StableExternalReferenceKey::NominalPath(external_path)));
    }

    fn all_subtractability_forms(
        internal: &[String],
        external: &[String],
        argument: NeuId,
    ) -> StackWeight {
        let mut weight = StackWeight::filter(Subtractability::AllExcept(
            internal.to_vec(),
            vec![argument],
        ));
        for (index, subtractability) in [
            Subtractability::Empty,
            Subtractability::All,
            Subtractability::AllExceptMany(vec![(external.to_vec(), vec![argument])]),
            Subtractability::Set(internal.to_vec(), vec![argument]),
            Subtractability::SetMany(vec![
                (internal.to_vec(), vec![argument]),
                (external.to_vec(), vec![]),
            ]),
        ]
        .into_iter()
        .enumerate()
        {
            weight = weight.compose(&StackWeight::floor(
                SubtractId(index as u32),
                subtractability,
            ));
        }
        weight
    }
}

fn member_key(
    identity: &NominalActTemplateIdentity,
    member: &super::nominal_act_identity::NominalActTemplateValueIdentity,
    root_path: &[String],
) -> Result<NominalActMemberKey, TypedActTemplateError> {
    let owner = identity
        .nominal_types
        .iter()
        .find(|nominal| nominal.source == member.owner)
        .ok_or(TypedActTemplateError::MalformedTemplateIdentity)?;
    let owner_path = path_names(&owner.source_path);
    let owner_relative_path = owner_path
        .strip_prefix(root_path)
        .ok_or(TypedActTemplateError::MalformedTemplateIdentity)?
        .to_vec();
    let kind = match member.kind {
        NominalActValueMemberKind::Operation { .. } => NominalActMemberKeyKind::Operation,
        NominalActValueMemberKind::Binding => NominalActMemberKeyKind::Binding,
        NominalActValueMemberKind::Constructor => NominalActMemberKeyKind::Constructor,
        NominalActValueMemberKind::FieldMethod {
            receiver: TypeMethodReceiver::Value,
        } => NominalActMemberKeyKind::FieldMethodValue,
        NominalActValueMemberKind::FieldMethod {
            receiver: TypeMethodReceiver::Ref,
        } => NominalActMemberKeyKind::FieldMethodRef,
    };
    Ok(NominalActMemberKey {
        owner_relative_path,
        kind,
        name: member.name.0.clone(),
    })
}

fn path_names(path: &sources::Path) -> Vec<String> {
    path.segments.iter().map(|name| name.0.clone()).collect()
}

struct NominalTypeGraphCloner<'a> {
    source: &'a TypeArena,
    target: &'a mut TypeArena,
    paths: &'a FxHashMap<Vec<String>, Vec<String>>,
    external_references: Option<&'a mut FxHashSet<StableExternalReferenceKey>>,
    pos_nodes: FxHashMap<PosId, PosId>,
    neg_nodes: FxHashMap<NegId, NegId>,
    neu_nodes: FxHashMap<NeuId, NeuId>,
}

impl<'a> NominalTypeGraphCloner<'a> {
    fn new(
        source: &'a TypeArena,
        target: &'a mut TypeArena,
        paths: &'a FxHashMap<Vec<String>, Vec<String>>,
        external_references: Option<&'a mut FxHashSet<StableExternalReferenceKey>>,
    ) -> Self {
        Self {
            source,
            target,
            paths,
            external_references,
            pos_nodes: FxHashMap::default(),
            neg_nodes: FxHashMap::default(),
            neu_nodes: FxHashMap::default(),
        }
    }

    fn clone_scheme(&mut self, scheme: &Scheme) -> Scheme {
        Scheme {
            quantifiers: scheme.quantifiers.clone(),
            role_predicates: scheme
                .role_predicates
                .iter()
                .map(|predicate| self.clone_role_predicate(predicate))
                .collect(),
            recursive_bounds: scheme
                .recursive_bounds
                .iter()
                .map(|bound| SchemeRecursiveBound {
                    var: bound.var,
                    bounds: self.clone_neu(bound.bounds),
                })
                .collect(),
            stack_quantifiers: scheme.stack_quantifiers.clone(),
            predicate: self.clone_pos(scheme.predicate),
        }
    }

    fn clone_role_predicate(&mut self, predicate: &RolePredicate) -> RolePredicate {
        RolePredicate {
            role: self.rewrite_path(&predicate.role),
            inputs: predicate
                .inputs
                .iter()
                .map(|input| match *input {
                    RolePredicateArg::Covariant(pos) => {
                        RolePredicateArg::Covariant(self.clone_pos(pos))
                    }
                    RolePredicateArg::Contravariant(neg) => {
                        RolePredicateArg::Contravariant(self.clone_neg(neg))
                    }
                    RolePredicateArg::Invariant(neu) => {
                        RolePredicateArg::Invariant(self.clone_neu(neu))
                    }
                })
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

    fn rewrite_path(&mut self, source: &[String]) -> Vec<String> {
        if let Some(destination) = self.paths.get(source) {
            return destination.clone();
        }
        if let Some(external_references) = self.external_references.as_deref_mut() {
            external_references.insert(StableExternalReferenceKey::NominalPath(source.to_vec()));
        }
        source.to_vec()
    }

    fn clone_pos(&mut self, id: PosId) -> PosId {
        if let Some(cloned) = self.pos_nodes.get(&id).copied() {
            return cloned;
        }
        let node = match self.source.pos(id).clone() {
            Pos::Bot => Pos::Bot,
            Pos::Var(var) => Pos::Var(var),
            Pos::Con(path, args) => Pos::Con(
                self.rewrite_path(&path),
                args.into_iter().map(|arg| self.clone_neu(arg)).collect(),
            ),
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
            Pos::Record(fields) => Pos::Record(self.clone_fields(fields, Self::clone_pos)),
            Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
                fields: self.clone_fields(fields, Self::clone_pos),
                tail: self.clone_pos(tail),
            },
            Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
                tail: self.clone_pos(tail),
                fields: self.clone_fields(fields, Self::clone_pos),
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
            Pos::Stack { inner, weight } => Pos::Stack {
                inner: self.clone_pos(inner),
                weight: self.clone_stack_weight(weight),
            },
            Pos::NonSubtract(inner, weight) => {
                Pos::NonSubtract(self.clone_pos(inner), self.clone_stack_weight(weight))
            }
            Pos::Union(left, right) => Pos::Union(self.clone_pos(left), self.clone_pos(right)),
        };
        let cloned = self.target.alloc_pos(node);
        self.pos_nodes.insert(id, cloned);
        cloned
    }

    fn clone_neg(&mut self, id: NegId) -> NegId {
        if let Some(cloned) = self.neg_nodes.get(&id).copied() {
            return cloned;
        }
        let node = match self.source.neg(id).clone() {
            Neg::Top => Neg::Top,
            Neg::Bot => Neg::Bot,
            Neg::Var(var) => Neg::Var(var),
            Neg::Con(path, args) => Neg::Con(
                self.rewrite_path(&path),
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
            Neg::Record(fields) => Neg::Record(self.clone_fields(fields, Self::clone_neg)),
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
        let cloned = self.target.alloc_neg(node);
        self.neg_nodes.insert(id, cloned);
        cloned
    }

    fn clone_neu(&mut self, id: NeuId) -> NeuId {
        if let Some(cloned) = self.neu_nodes.get(&id).copied() {
            return cloned;
        }
        let node = match self.source.neu(id).clone() {
            Neu::Bounds(lower, upper) => Neu::Bounds(self.clone_pos(lower), self.clone_neg(upper)),
            Neu::Con(path, args) => Neu::Con(
                self.rewrite_path(&path),
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
            Neu::Record(fields) => Neu::Record(self.clone_fields(fields, Self::clone_neu)),
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
        let cloned = self.target.alloc_neu(node);
        self.neu_nodes.insert(id, cloned);
        cloned
    }

    fn clone_fields<SourceId: Copy, TargetId>(
        &mut self,
        fields: Vec<RecordField<SourceId>>,
        clone: fn(&mut Self, SourceId) -> TargetId,
    ) -> Vec<RecordField<TargetId>> {
        fields
            .into_iter()
            .map(|field| RecordField {
                name: field.name,
                value: clone(self, field.value),
                optional: field.optional,
            })
            .collect()
    }

    fn clone_subtractability(&mut self, source: Subtractability) -> Subtractability {
        match source {
            Subtractability::Empty => Subtractability::Empty,
            Subtractability::All => Subtractability::All,
            Subtractability::AllExcept(path, args) => Subtractability::AllExcept(
                self.rewrite_path(&path),
                args.into_iter().map(|arg| self.clone_neu(arg)).collect(),
            ),
            Subtractability::AllExceptMany(families) => Subtractability::AllExceptMany(
                families
                    .into_iter()
                    .map(|(path, args)| {
                        (
                            self.rewrite_path(&path),
                            args.into_iter().map(|arg| self.clone_neu(arg)).collect(),
                        )
                    })
                    .collect(),
            ),
            Subtractability::Set(path, args) => Subtractability::Set(
                self.rewrite_path(&path),
                args.into_iter().map(|arg| self.clone_neu(arg)).collect(),
            ),
            Subtractability::SetMany(families) => Subtractability::SetMany(
                families
                    .into_iter()
                    .map(|(path, args)| {
                        (
                            self.rewrite_path(&path),
                            args.into_iter().map(|arg| self.clone_neu(arg)).collect(),
                        )
                    })
                    .collect(),
            ),
        }
    }

    fn clone_stack_weight(&mut self, source: StackWeight) -> StackWeight {
        let mut target =
            StackWeight::filter(self.clone_subtractability(source.filter_set().clone()));
        for entry in source.entries() {
            for floor in &entry.floor {
                target = target.compose(&StackWeight::floor(
                    entry.id,
                    self.clone_subtractability(floor.clone()),
                ));
            }
            target = target.compose(&StackWeight::pops(entry.id, entry.pops));
            for stack in &entry.stack {
                target = target.compose(&StackWeight::push(
                    entry.id,
                    self.clone_subtractability(stack.clone()),
                ));
            }
        }
        target
    }
}
