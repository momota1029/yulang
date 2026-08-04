//! Nominal namespace closure recorded for synthetic act copies.
//!
//! M1-1 records the shell correspondence only. Nothing in lowering consumes these maps yet.

use super::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NominalActTemplateIdentity {
    pub root_act: TypeDeclId,
    pub nominal_types: Vec<NominalActTemplateTypeIdentity>,
    pub value_members: Vec<NominalActTemplateValueIdentity>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NominalActTemplateTypeIdentity {
    pub source: TypeDeclId,
    pub source_path: ModulePath,
    pub role: NominalActTypeRole,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum NominalActTypeRole {
    RootAct,
    NestedDeclaration,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NominalActTemplateValueIdentity {
    pub owner: TypeDeclId,
    pub kind: NominalActValueMemberKind,
    pub name: Name,
    pub source: DefId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NominalActValueMemberKind {
    Operation { operation_path: ModulePath },
    Binding,
    Constructor,
    FieldMethod { receiver: TypeMethodReceiver },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NominalActInstanceSubstitution {
    pub template_root_act: TypeDeclId,
    pub destination_root_act: TypeDeclId,
    pub type_decl_map: FxHashMap<TypeDeclId, TypeDeclId>,
    pub type_path_map: FxHashMap<ModulePath, ModulePath>,
    pub def_map: FxHashMap<DefId, DefId>,
    pub operation_path_map: FxHashMap<ModulePath, ModulePath>,
}

impl ModuleTable {
    pub(crate) fn record_nominal_act_instance_substitution(
        &mut self,
        template_root_act: TypeDeclId,
        destination_root_act: TypeDeclId,
    ) {
        if !self
            .nominal_act_template_identities
            .contains_key(&template_root_act)
        {
            let Some(template) = self.collect_nominal_act_identity(template_root_act) else {
                return;
            };
            self.nominal_act_template_identities
                .insert(template_root_act, template);
        }
        let Some(destination) = self.collect_nominal_act_identity(destination_root_act) else {
            return;
        };
        let Some(substitution) = self
            .nominal_act_template_identities
            .get(&template_root_act)
            .and_then(|template| build_substitution(template, &destination))
        else {
            return;
        };
        self.nominal_act_instance_substitutions
            .insert(destination_root_act, substitution);
    }

    pub(crate) fn nominal_act_template_identity(
        &self,
        root: TypeDeclId,
    ) -> Option<&NominalActTemplateIdentity> {
        self.nominal_act_template_identities.get(&root)
    }

    pub(crate) fn nominal_act_instance_substitution(
        &self,
        destination: TypeDeclId,
    ) -> Option<&NominalActInstanceSubstitution> {
        self.nominal_act_instance_substitutions.get(&destination)
    }

    #[cfg(test)]
    pub(crate) fn nominal_act_instance_substitutions(
        &self,
    ) -> impl Iterator<Item = &NominalActInstanceSubstitution> {
        self.nominal_act_instance_substitutions.values()
    }

    pub(crate) fn capture_nominal_act_identity(
        &self,
        root: TypeDeclId,
    ) -> Option<NominalActTemplateIdentity> {
        self.collect_nominal_act_identity(root)
    }

    pub(super) fn remap_nominal_act_identity_defs(&mut self, import: &CompiledRuntimeImport) {
        for identity in self.nominal_act_template_identities.values_mut() {
            for member in &mut identity.value_members {
                member.source = import.map_def(member.source);
            }
        }
        for substitution in self.nominal_act_instance_substitutions.values_mut() {
            substitution.def_map = std::mem::take(&mut substitution.def_map)
                .into_iter()
                .map(|(source, destination)| (import.map_def(source), import.map_def(destination)))
                .collect();
        }
    }

    fn collect_nominal_act_identity(
        &self,
        root_act: TypeDeclId,
    ) -> Option<NominalActTemplateIdentity> {
        let root = self.type_decl_by_id(root_act)?;
        let mut nominal_types = vec![NominalActTemplateTypeIdentity {
            source: root_act,
            source_path: self.type_decl_path(&root),
            role: NominalActTypeRole::RootAct,
        }];
        let mut index = 0;
        while index < nominal_types.len() {
            let owner = nominal_types[index].source;
            if let Some(companion) = self.type_companion(owner) {
                for nested in self.module_type_decls(companion) {
                    if nominal_types
                        .iter()
                        .any(|identity| identity.source == nested.id)
                    {
                        continue;
                    }
                    nominal_types.push(NominalActTemplateTypeIdentity {
                        source: nested.id,
                        source_path: self.type_decl_path(&nested),
                        role: NominalActTypeRole::NestedDeclaration,
                    });
                }
            }
            index += 1;
        }

        let mut value_members = Vec::new();
        for nominal in &nominal_types {
            if let Some(companion) = self.type_companion(nominal.source) {
                for value in self.module_value_decls(companion) {
                    let (owner, kind) =
                        if let Some(operation) = self.act_operation_decl_by_def(value.def) {
                            let mut operation_path = self.type_decl_path(&operation.effect);
                            operation_path.segments.push(operation.name);
                            (
                                operation.effect.id,
                                NominalActValueMemberKind::Operation { operation_path },
                            )
                        } else if let Some(constructor) = self.constructor_by_def(value.def) {
                            (constructor.owner, NominalActValueMemberKind::Constructor)
                        } else {
                            (nominal.source, NominalActValueMemberKind::Binding)
                        };
                    value_members.push(NominalActTemplateValueIdentity {
                        owner,
                        kind,
                        name: value.name,
                        source: value.def,
                    });
                }
            }
            for method in self.type_field_methods(nominal.source) {
                value_members.push(NominalActTemplateValueIdentity {
                    owner: nominal.source,
                    kind: NominalActValueMemberKind::FieldMethod {
                        receiver: method.receiver_kind,
                    },
                    name: method.name.clone(),
                    source: method.def,
                });
            }
        }
        Some(NominalActTemplateIdentity {
            root_act,
            nominal_types,
            value_members,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct MemberShape {
    owner_path: Vec<Name>,
    name: Name,
    kind: MemberShapeKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum MemberShapeKind {
    Operation,
    Binding,
    Constructor,
    FieldMethodValue,
    FieldMethodRef,
}

fn build_substitution(
    template: &NominalActTemplateIdentity,
    destination: &NominalActTemplateIdentity,
) -> Option<NominalActInstanceSubstitution> {
    let template_root_path = root_path(template)?;
    let destination_root_path = root_path(destination)?;
    let mut destination_types = destination
        .nominal_types
        .iter()
        .map(|identity| {
            Some((
                relative_path(destination_root_path, &identity.source_path)?,
                identity,
            ))
        })
        .collect::<Option<FxHashMap<_, _>>>()?;
    if destination_types.len() != destination.nominal_types.len() {
        return None;
    }

    let mut type_decl_map = FxHashMap::default();
    let mut type_path_map = FxHashMap::default();
    for source in &template.nominal_types {
        let relative = relative_path(template_root_path, &source.source_path)?;
        let target = destination_types.remove(&relative)?;
        if source.role != target.role {
            return None;
        }
        type_decl_map.insert(source.source, target.source);
        type_path_map.insert(source.source_path.clone(), target.source_path.clone());
    }
    if !destination_types.is_empty() {
        return None;
    }

    let template_owner_paths = owner_paths(template, template_root_path)?;
    let destination_owner_paths = owner_paths(destination, destination_root_path)?;
    let mut destination_members = destination
        .value_members
        .iter()
        .map(|member| Some((member_shape(member, &destination_owner_paths)?, member)))
        .collect::<Option<FxHashMap<_, _>>>()?;
    if destination_members.len() != destination.value_members.len() {
        return None;
    }

    let mut def_map = FxHashMap::default();
    let mut operation_path_map = FxHashMap::default();
    for source in &template.value_members {
        let target = destination_members.remove(&member_shape(source, &template_owner_paths)?)?;
        def_map.insert(source.source, target.source);
        if let (
            NominalActValueMemberKind::Operation {
                operation_path: source_path,
            },
            NominalActValueMemberKind::Operation {
                operation_path: target_path,
            },
        ) = (&source.kind, &target.kind)
        {
            operation_path_map.insert(source_path.clone(), target_path.clone());
        }
    }
    if !destination_members.is_empty() {
        return None;
    }

    Some(NominalActInstanceSubstitution {
        template_root_act: template.root_act,
        destination_root_act: destination.root_act,
        type_decl_map,
        type_path_map,
        def_map,
        operation_path_map,
    })
}

fn root_path(identity: &NominalActTemplateIdentity) -> Option<&ModulePath> {
    identity
        .nominal_types
        .iter()
        .find(|ty| ty.role == NominalActTypeRole::RootAct)
        .map(|ty| &ty.source_path)
}

fn owner_paths(
    identity: &NominalActTemplateIdentity,
    root: &ModulePath,
) -> Option<FxHashMap<TypeDeclId, Vec<Name>>> {
    identity
        .nominal_types
        .iter()
        .map(|ty| Some((ty.source, relative_path(root, &ty.source_path)?)))
        .collect()
}

fn member_shape(
    member: &NominalActTemplateValueIdentity,
    owner_paths: &FxHashMap<TypeDeclId, Vec<Name>>,
) -> Option<MemberShape> {
    let kind = match member.kind {
        NominalActValueMemberKind::Operation { .. } => MemberShapeKind::Operation,
        NominalActValueMemberKind::Binding => MemberShapeKind::Binding,
        NominalActValueMemberKind::Constructor => MemberShapeKind::Constructor,
        NominalActValueMemberKind::FieldMethod {
            receiver: TypeMethodReceiver::Value,
        } => MemberShapeKind::FieldMethodValue,
        NominalActValueMemberKind::FieldMethod {
            receiver: TypeMethodReceiver::Ref,
        } => MemberShapeKind::FieldMethodRef,
    };
    Some(MemberShape {
        owner_path: owner_paths.get(&member.owner)?.clone(),
        name: member.name.clone(),
        kind,
    })
}

fn relative_path(root: &ModulePath, path: &ModulePath) -> Option<Vec<Name>> {
    path.segments
        .strip_prefix(root.segments.as_slice())
        .map(<[Name]>::to_vec)
}
