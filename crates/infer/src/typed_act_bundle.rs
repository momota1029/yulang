//! Portable, versioned cold-start assets for finalized synthetic-act templates.
//!
//! M1-6 only captures, encodes, and validates these bundles. Cold lowering does not consume them
//! until M1-7/M1-8.

use crate::lowering::BodyLowering;
use crate::module_table::nominal_act_identity::{NominalActTemplateIdentity, NominalActTypeRole};
use crate::module_table::typed_act_body::{CatchSite, TypedActBodyTemplate};
use crate::module_table::typed_act_template::{
    NominalActMemberKey, StableExternalReferenceKey, TypedActTemplate,
};
use crate::{ModuleOrder, Name};
use poly::dump::DumpLabels;
use poly::expr::{Arena as PolyArena, DefId, RefId, SelectId};
use poly::types::{Scheme, TypeArena};
use serde::{Deserialize, Serialize};

pub const TYPED_ACT_TEMPLATE_BUNDLE_VERSION: u32 = 1;
pub const TYPED_ACT_TEMPLATE_SCHEMA_VERSION: u32 = 1;

#[derive(Clone, Serialize, Deserialize)]
pub struct TypedActTemplateBundle {
    pub envelope_version: u32,
    pub typed_template_schema_version: u32,
    pub compiler_compatibility_version: String,
    pub profiles: Vec<TypedActTemplateBundleProfile>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum TypedActTemplateProfileKind {
    FullStd,
    PlaygroundStd,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticStdManifest {
    pub modules: Vec<SemanticStdModule>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SemanticStdModule {
    pub module_path: Vec<String>,
    pub source_hash: u64,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct TypedActTemplateBundleProfile {
    pub kind: TypedActTemplateProfileKind,
    pub std_manifest: SemanticStdManifest,
    templates: Vec<PortableTypedActTemplate>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum PortableTemplateKind {
    Var,
    LabelSub,
}

#[derive(Clone, Serialize, Deserialize)]
struct PortableTypedActTemplate {
    kind: PortableTemplateKind,
    identity: PortableNominalIdentity,
    schemes: PortableSchemeTemplate,
    body: PortableBodyTemplate,
}

#[derive(Clone, Serialize, Deserialize)]
struct PortableNominalIdentity {
    root_path: Vec<String>,
    nominal_types: Vec<(Vec<String>, NominalActTypeRole)>,
    value_members: Vec<NominalActMemberKey>,
}

#[derive(Clone, Serialize, Deserialize)]
struct PortableSchemeTemplate {
    internal_nominal_paths: Vec<Vec<String>>,
    members: Vec<(NominalActMemberKey, Scheme)>,
    types: TypeArena,
    external_references: Vec<StableExternalReferenceKey>,
}

#[derive(Clone, Serialize, Deserialize)]
struct PortableBodyTemplate {
    arena: PolyArena,
    labels: DumpLabels,
    members: Vec<(NominalActMemberKey, DefId)>,
    external_refs: Vec<(RefId, StableExternalReferenceKey)>,
    external_selects: Vec<(SelectId, StableExternalReferenceKey)>,
    external_catches: Vec<(CatchSite, StableExternalReferenceKey)>,
}

#[derive(Debug)]
pub enum TypedActTemplateBundleError {
    Encode(bincode::Error),
    Decode(bincode::Error),
    UnsupportedEnvelope(u32),
    UnsupportedSchema(u32),
    MissingCanonicalTemplate(Vec<String>),
    MissingTemplateIdentity(Vec<String>),
    Capture(String),
    MissingExternalAnchor(String),
}

impl TypedActTemplateBundle {
    pub fn from_profiles(mut profiles: Vec<TypedActTemplateBundleProfile>) -> Self {
        profiles.sort_by_key(|profile| profile.kind);
        Self {
            envelope_version: TYPED_ACT_TEMPLATE_BUNDLE_VERSION,
            typed_template_schema_version: TYPED_ACT_TEMPLATE_SCHEMA_VERSION,
            compiler_compatibility_version: env!("CARGO_PKG_VERSION").to_string(),
            profiles,
        }
    }

    pub fn encode(&self) -> Result<Vec<u8>, TypedActTemplateBundleError> {
        bincode::serialize(self).map_err(TypedActTemplateBundleError::Encode)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, TypedActTemplateBundleError> {
        let bundle: Self =
            bincode::deserialize(bytes).map_err(TypedActTemplateBundleError::Decode)?;
        if bundle.envelope_version != TYPED_ACT_TEMPLATE_BUNDLE_VERSION {
            return Err(TypedActTemplateBundleError::UnsupportedEnvelope(
                bundle.envelope_version,
            ));
        }
        if bundle.typed_template_schema_version != TYPED_ACT_TEMPLATE_SCHEMA_VERSION {
            return Err(TypedActTemplateBundleError::UnsupportedSchema(
                bundle.typed_template_schema_version,
            ));
        }
        Ok(bundle)
    }

    pub fn profile(
        &self,
        kind: TypedActTemplateProfileKind,
    ) -> Option<&TypedActTemplateBundleProfile> {
        self.profiles.iter().find(|profile| profile.kind == kind)
    }
}

impl SemanticStdManifest {
    pub fn new(mut modules: Vec<SemanticStdModule>) -> Self {
        modules.sort();
        modules.dedup();
        Self { modules }
    }
}

pub fn capture_profile_from_legacy_lowering(
    kind: TypedActTemplateProfileKind,
    std_manifest: SemanticStdManifest,
    lowering: &BodyLowering,
) -> Result<TypedActTemplateBundleProfile, TypedActTemplateBundleError> {
    let mut templates = Vec::new();
    for (template_kind, path) in [
        (
            PortableTemplateKind::Var,
            vec!["std", "control", "var", "var"],
        ),
        (
            PortableTemplateKind::LabelSub,
            vec!["std", "control", "flow", "label_sub"],
        ),
    ] {
        let names = path
            .iter()
            .map(|item| Name((*item).into()))
            .collect::<Vec<_>>();
        let decl = lowering
            .modules
            .type_path_at(
                lowering.modules.root_id(),
                &names,
                ModuleOrder::from_index(u32::MAX),
            )
            .found()
            .ok_or_else(|| {
                TypedActTemplateBundleError::MissingCanonicalTemplate(
                    path.iter().map(|item| (*item).to_string()).collect(),
                )
            })?;
        let identity = lowering
            .modules
            .capture_nominal_act_identity(decl.id)
            .ok_or_else(|| {
                TypedActTemplateBundleError::MissingTemplateIdentity(
                    path.iter().map(|item| (*item).to_string()).collect(),
                )
            })?;
        let typed = TypedActTemplate::capture(&identity, &lowering.session.poly)
            .map_err(|error| TypedActTemplateBundleError::Capture(format!("{error:?}")))?;
        let body = typed
            .capture_body(
                &identity,
                &lowering.session.poly,
                &lowering.modules,
                &lowering.labels,
            )
            .map_err(|error| TypedActTemplateBundleError::Capture(format!("{error:?}")))?;
        templates.push(portable_template(template_kind, identity, typed, body)?);
    }
    templates.sort_by_key(|template| template.kind);
    Ok(TypedActTemplateBundleProfile {
        kind,
        std_manifest,
        templates,
    })
}

pub fn verify_profile_external_anchors(
    profile: &TypedActTemplateBundleProfile,
    lowering: &BodyLowering,
) -> Result<usize, TypedActTemplateBundleError> {
    let mut keys = Vec::new();
    for template in &profile.templates {
        keys.extend(template.schemes.external_references.iter().cloned());
        keys.extend(
            template
                .body
                .external_refs
                .iter()
                .map(|(_, key)| key.clone()),
        );
        keys.extend(
            template
                .body
                .external_selects
                .iter()
                .map(|(_, key)| key.clone()),
        );
        keys.extend(
            template
                .body
                .external_catches
                .iter()
                .map(|(_, key)| key.clone()),
        );
    }
    keys.sort_by_key(stable_key_sort_key);
    keys.dedup();
    for key in &keys {
        let found = match key {
            StableExternalReferenceKey::BuiltinType(_) => true,
            StableExternalReferenceKey::NominalPath(path) => {
                let names = path.iter().cloned().map(Name).collect::<Vec<_>>();
                lowering
                    .modules
                    .type_path_at(
                        lowering.modules.root_id(),
                        &names,
                        ModuleOrder::from_index(u32::MAX),
                    )
                    .found()
                    .is_some()
            }
            _ => lowering
                .modules
                .resolve_stable_external_reference_key(key)
                .is_some(),
        };
        if !found {
            return Err(TypedActTemplateBundleError::MissingExternalAnchor(format!(
                "{key:?}"
            )));
        }
    }
    Ok(keys.len())
}

fn portable_template(
    kind: PortableTemplateKind,
    identity: NominalActTemplateIdentity,
    typed: TypedActTemplate,
    body: TypedActBodyTemplate,
) -> Result<PortableTypedActTemplate, TypedActTemplateBundleError> {
    let root = identity
        .nominal_types
        .iter()
        .find(|item| item.source == identity.root_act)
        .ok_or_else(|| TypedActTemplateBundleError::Capture("missing root identity".into()))?;
    let root_path = root
        .source_path
        .segments
        .iter()
        .map(|name| name.0.clone())
        .collect::<Vec<_>>();
    let nominal_types = identity
        .nominal_types
        .iter()
        .map(|item| {
            let path = item
                .source_path
                .segments
                .iter()
                .map(|name| name.0.clone())
                .collect::<Vec<_>>();
            let relative = path
                .strip_prefix(root_path.as_slice())
                .ok_or_else(|| {
                    TypedActTemplateBundleError::Capture("non-nested nominal identity".into())
                })?
                .to_vec();
            Ok((relative, item.role))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut value_members = typed
        .members
        .iter()
        .map(|member| member.key.clone())
        .collect::<Vec<_>>();
    value_members.sort_by_key(member_sort_key);

    let mut scheme_members = typed
        .members
        .into_iter()
        .map(|member| (member.key, member.scheme))
        .collect::<Vec<_>>();
    scheme_members.sort_by_key(|(key, _)| member_sort_key(key));
    let mut external_references = typed.external_references.into_iter().collect::<Vec<_>>();
    external_references.sort_by_key(stable_key_sort_key);

    let mut body_members = body
        .members
        .into_iter()
        .map(|member| (member.key, member.detached))
        .collect::<Vec<_>>();
    body_members.sort_by_key(|(key, _)| member_sort_key(key));
    let mut external_refs = body.external_refs.into_iter().collect::<Vec<_>>();
    external_refs.sort_by_key(|(id, _)| id.0);
    let mut external_selects = body.external_selects.into_iter().collect::<Vec<_>>();
    external_selects.sort_by_key(|(id, _)| id.0);
    let mut external_catches = body.external_catches.into_iter().collect::<Vec<_>>();
    external_catches.sort_by_key(|(site, _)| (site.expr.0, site.arm));

    Ok(PortableTypedActTemplate {
        kind,
        identity: PortableNominalIdentity {
            root_path,
            nominal_types,
            value_members,
        },
        schemes: PortableSchemeTemplate {
            internal_nominal_paths: typed.internal_nominal_paths,
            members: scheme_members,
            types: typed.types,
            external_references,
        },
        body: PortableBodyTemplate {
            arena: body.arena,
            labels: body.labels,
            members: body_members,
            external_refs,
            external_selects,
            external_catches,
        },
    })
}

fn member_sort_key(key: &NominalActMemberKey) -> String {
    format!("{:?}/{:?}/{}", key.owner_relative_path, key.kind, key.name)
}

fn stable_key_sort_key(key: &StableExternalReferenceKey) -> String {
    format!("{key:?}")
}
