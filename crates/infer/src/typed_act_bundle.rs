//! Portable, versioned cold-start assets for finalized synthetic-act templates.
//!
//! M1-6 only captures, encodes, and validates these bundles. Cold lowering does not consume them
//! until M1-7/M1-8.

use crate::lowering::BodyLowering;
use crate::module_table::nominal_act_identity::{NominalActTemplateIdentity, NominalActTypeRole};
use crate::module_table::typed_act_body::TypedActBodyMember;
use crate::module_table::typed_act_body::{CatchSite, TypedActBodyTemplate};
use crate::module_table::typed_act_catalog::{
    SyntheticActCopyKind, TypedActTemplateCatalog, TypedActTemplateCatalogEntry,
};
use crate::module_table::typed_act_template::{
    NominalActMemberKey, StableExternalReferenceKey, TypedActTemplate, TypedActTemplateMember,
    member_key,
};
use crate::{ModuleOrder, ModuleTable, Name, TypeDeclId};
use poly::dump::DumpLabels;
use poly::expr::{Arena as PolyArena, DefId, RefId, SelectId};
use poly::types::{Scheme, TypeArena};
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::sync::Arc;

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

#[derive(Serialize, Deserialize)]
struct ShadowInstantiationSnapshot {
    schemes: PortableSchemeTemplate,
    body: PortableBodyTemplate,
}

pub(crate) fn compare_shadow_snapshots(embedded: &[u8], legacy: &[u8]) -> Result<(), String> {
    let embedded: ShadowInstantiationSnapshot = bincode::deserialize(embedded)
        .map_err(|error| format!("decode embedded snapshot: {error}"))?;
    let legacy: ShadowInstantiationSnapshot =
        bincode::deserialize(legacy).map_err(|error| format!("decode legacy snapshot: {error}"))?;
    let mut embedded_paths = embedded.schemes.internal_nominal_paths.clone();
    let mut legacy_paths = legacy.schemes.internal_nominal_paths.clone();
    embedded_paths.sort();
    legacy_paths.sort();
    if embedded_paths != legacy_paths {
        return Err(format!(
            "scheme internal nominal paths: embedded={:?}, legacy={:?}",
            embedded_paths, legacy_paths
        ));
    }
    if embedded.schemes.members.len() != legacy.schemes.members.len() {
        return Err(format!(
            "scheme member count: embedded={} legacy={}",
            embedded.schemes.members.len(),
            legacy.schemes.members.len()
        ));
    }
    for ((embedded_key, embedded_scheme), (legacy_key, legacy_scheme)) in
        embedded.schemes.members.iter().zip(&legacy.schemes.members)
    {
        compare_serialized("scheme member key", embedded_key, legacy_key)?;
        let embedded_view = poly::dump::format_scheme(&embedded.schemes.types, embedded_scheme);
        let legacy_view = poly::dump::format_scheme(&legacy.schemes.types, legacy_scheme);
        if embedded_view != legacy_view {
            return Err(format!(
                "scheme member {embedded_key:?}: embedded={embedded_view:?}, legacy={legacy_view:?}"
            ));
        }
    }
    compare_serialized(
        "scheme external references",
        &embedded.schemes.external_references,
        &legacy.schemes.external_references,
    )?;
    let embedded_body = normalized_body_view(&embedded.body.arena);
    let legacy_body = normalized_body_view(&legacy.body.arena);
    if embedded_body != legacy_body {
        let first = embedded_body
            .chars()
            .zip(legacy_body.chars())
            .position(|(left, right)| left != right)
            .unwrap_or_else(|| embedded_body.len().min(legacy_body.len()));
        return Err(format!(
            "normalized body graph: first_char={first}, embedded_len={}, legacy_len={}, embedded={embedded_body:?}, legacy={legacy_body:?}",
            embedded_body.len(),
            legacy_body.len()
        ));
    }
    compare_serialized("body members", &embedded.body.members, &legacy.body.members)?;
    compare_serialized(
        "body external refs",
        &embedded.body.external_refs,
        &legacy.body.external_refs,
    )?;
    compare_serialized(
        "body external selects",
        &embedded.body.external_selects,
        &legacy.body.external_selects,
    )?;
    compare_serialized(
        "body external catches",
        &embedded.body.external_catches,
        &legacy.body.external_catches,
    )?;
    Ok(())
}

fn normalized_body_view(arena: &PolyArena) -> String {
    let mut arena = arena.clone();
    arena.roots.sort_by_key(|def| def.0);
    poly::dump::dump_arena(&arena)
}

fn compare_serialized(
    field: &str,
    embedded: &impl Serialize,
    legacy: &impl Serialize,
) -> Result<(), String> {
    let embedded = bincode::serialize(embedded).map_err(|error| format!("{field}: {error}"))?;
    let legacy = bincode::serialize(legacy).map_err(|error| format!("{field}: {error}"))?;
    if embedded == legacy {
        return Ok(());
    }
    let first = embedded
        .iter()
        .zip(&legacy)
        .position(|(left, right)| left != right)
        .unwrap_or_else(|| embedded.len().min(legacy.len()));
    Err(format!(
        "snapshot mismatch in {field}: first_byte={first}, embedded_len={}, legacy_len={}",
        embedded.len(),
        legacy.len()
    ))
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
    MissingLiveMember(String),
    Snapshot(String),
}

std::thread_local! {
    static COLD_SHADOW_PROFILE: RefCell<Option<Arc<TypedActTemplateBundleProfile>>> =
        const { RefCell::new(None) };
    static COLD_SHADOW_REPORT: RefCell<Option<ColdTypedActShadowReport>> =
        const { RefCell::new(None) };
    static COLD_TYPED_ACT_CUTOVER: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Cross-crate observation seam for proving an embedded profile before cold cutover.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ColdTypedActShadowReport {
    pub var_passed: usize,
    pub label_sub_passed: usize,
    pub var_eligible: usize,
    pub label_sub_eligible: usize,
    pub misses: usize,
    pub fallbacks: usize,
    pub legacy_lowerings: usize,
    pub failures: Vec<String>,
}

#[derive(Clone, Copy)]
pub(crate) enum ColdTypedActAttemptOutcome {
    Eligible,
    Miss,
    Fallback,
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

pub fn with_cold_typed_act_template_shadow<T>(
    profile: Arc<TypedActTemplateBundleProfile>,
    run: impl FnOnce() -> T,
) -> T {
    struct Reset(Option<Arc<TypedActTemplateBundleProfile>>);
    impl Drop for Reset {
        fn drop(&mut self) {
            COLD_SHADOW_PROFILE.with(|slot| {
                slot.replace(self.0.take());
            });
        }
    }
    let reset = Reset(COLD_SHADOW_PROFILE.with(|slot| slot.replace(Some(profile))));
    let output = run();
    drop(reset);
    output
}

pub fn with_cold_typed_act_template_shadow_report<T>(
    profile: Arc<TypedActTemplateBundleProfile>,
    run: impl FnOnce() -> T,
) -> (T, ColdTypedActShadowReport) {
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            COLD_SHADOW_REPORT.with(|slot| {
                slot.borrow_mut().take();
            });
        }
    }
    COLD_SHADOW_REPORT.with(|slot| {
        assert!(
            slot.borrow().is_none(),
            "nested cold typed-act shadow report"
        );
        slot.replace(Some(ColdTypedActShadowReport::default()));
    });
    let reset = Reset;
    let output = with_cold_typed_act_template_shadow(profile, run);
    let report = COLD_SHADOW_REPORT.with(|slot| {
        slot.borrow_mut()
            .take()
            .expect("cold typed-act shadow report remains installed")
    });
    std::mem::forget(reset);
    (output, report)
}

pub fn with_cold_typed_act_template_cutover<T>(
    profile: Arc<TypedActTemplateBundleProfile>,
    run: impl FnOnce() -> T,
) -> T {
    struct Reset(bool);
    impl Drop for Reset {
        fn drop(&mut self) {
            COLD_TYPED_ACT_CUTOVER.with(|flag| flag.set(self.0));
        }
    }
    let reset = Reset(COLD_TYPED_ACT_CUTOVER.with(|flag| flag.replace(true)));
    let output = with_cold_typed_act_template_shadow(profile, run);
    drop(reset);
    output
}

pub fn with_cold_typed_act_template_cutover_report<T>(
    profile: Arc<TypedActTemplateBundleProfile>,
    run: impl FnOnce() -> T,
) -> (T, ColdTypedActShadowReport) {
    COLD_SHADOW_REPORT.with(|slot| {
        assert!(
            slot.borrow().is_none(),
            "nested cold typed-act cutover report"
        );
        slot.replace(Some(ColdTypedActShadowReport::default()));
    });
    let output = with_cold_typed_act_template_cutover(profile, run);
    let report = COLD_SHADOW_REPORT.with(|slot| {
        slot.borrow_mut()
            .take()
            .expect("cold typed-act cutover report remains installed")
    });
    (output, report)
}

pub(crate) fn record_cold_typed_act_shadow_result(
    kind: SyntheticActCopyKind,
    result: &Result<(), String>,
) {
    COLD_SHADOW_REPORT.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(report) = slot.as_mut() else {
            return;
        };
        match (kind, result) {
            (SyntheticActCopyKind::Var, Ok(())) => report.var_passed += 1,
            (SyntheticActCopyKind::LabelSub, Ok(())) => report.label_sub_passed += 1,
            (kind, Err(detail)) => report.failures.push(format!("{kind:?}: {detail}")),
        }
    });
}

pub(crate) fn cold_typed_act_cutover_active() -> bool {
    COLD_TYPED_ACT_CUTOVER.with(std::cell::Cell::get)
}

pub(crate) fn record_cold_typed_act_attempt(
    kind: SyntheticActCopyKind,
    outcome: ColdTypedActAttemptOutcome,
) {
    COLD_SHADOW_REPORT.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(report) = slot.as_mut() else {
            return;
        };
        match (kind, outcome) {
            (SyntheticActCopyKind::Var, ColdTypedActAttemptOutcome::Eligible) => {
                report.var_eligible += 1
            }
            (SyntheticActCopyKind::LabelSub, ColdTypedActAttemptOutcome::Eligible) => {
                report.label_sub_eligible += 1
            }
            (_, ColdTypedActAttemptOutcome::Miss) => report.misses += 1,
            (_, ColdTypedActAttemptOutcome::Fallback) => report.fallbacks += 1,
        }
    });
}

pub(crate) fn record_cold_typed_act_legacy_lowering() {
    COLD_SHADOW_REPORT.with(|slot| {
        if let Some(report) = slot.borrow_mut().as_mut() {
            report.legacy_lowerings += 1;
        }
    });
}

pub fn profile_for_loaded_files(
    bundle: &TypedActTemplateBundle,
    files: &[sources::LoadedFile],
) -> Option<Arc<TypedActTemplateBundleProfile>> {
    let manifest = semantic_manifest_for_loaded_files(files);
    bundle
        .profiles
        .iter()
        .find(|profile| profile.std_manifest == manifest)
        .cloned()
        .map(Arc::new)
}

pub(crate) fn current_cold_shadow_catalog(
    modules: &ModuleTable,
) -> Result<Option<TypedActTemplateCatalog>, TypedActTemplateBundleError> {
    COLD_SHADOW_PROFILE.with(|slot| {
        slot.borrow()
            .as_deref()
            .map(|profile| profile.to_live_catalog(modules))
            .transpose()
    })
}

pub(crate) fn has_current_cold_shadow_profile() -> bool {
    COLD_SHADOW_PROFILE.with(|slot| slot.borrow().is_some())
}

pub(crate) fn applied_catalog_entry_snapshot(
    entry: &TypedActTemplateCatalogEntry,
    substitution: &crate::module_table::nominal_act_identity::NominalActInstanceSubstitution,
) -> Result<Vec<u8>, TypedActTemplateBundleError> {
    let schemes = entry
        .typed
        .apply(substitution)
        .map_err(|error| TypedActTemplateBundleError::Snapshot(format!("{error:?}")))?;
    let body = entry
        .body
        .apply(substitution)
        .map_err(|error| TypedActTemplateBundleError::Snapshot(format!("{error:?}")))?;
    let destination_keys = entry
        .typed
        .members
        .iter()
        .filter_map(|member| {
            substitution
                .def_map
                .get(&member.source)
                .map(|destination| (*destination, member.key.clone()))
        })
        .collect::<rustc_hash::FxHashMap<_, _>>();
    let mut scheme_members = schemes
        .members
        .into_iter()
        .map(|member| (member.key, member.scheme))
        .collect::<Vec<_>>();
    scheme_members.sort_by_key(|(key, _)| member_sort_key(key));
    let mut body_members = body
        .member_destinations
        .into_iter()
        .map(|(detached, destination)| {
            destination_keys
                .get(&destination)
                .cloned()
                .map(|key| (key, detached))
                .ok_or_else(|| {
                    TypedActTemplateBundleError::MissingLiveMember(format!("{destination:?}"))
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    body_members.sort_by_key(|(key, _)| member_sort_key(key));
    encode_shadow_snapshot(ShadowInstantiationSnapshot {
        schemes: PortableSchemeTemplate {
            internal_nominal_paths: entry
                .typed
                .internal_nominal_paths
                .iter()
                .map(|path| {
                    substitution
                        .type_path_map
                        .iter()
                        .find(|(source, _)| {
                            source.segments.iter().map(|name| &name.0).eq(path.iter())
                        })
                        .map(|(_, destination)| {
                            destination
                                .segments
                                .iter()
                                .map(|name| name.0.clone())
                                .collect()
                        })
                        .unwrap_or_else(|| path.clone())
                })
                .collect(),
            members: scheme_members,
            types: schemes.types,
            external_references: sorted_keys(entry.typed.external_references.iter().cloned()),
        },
        body: PortableBodyTemplate {
            arena: body.arena,
            labels: body.labels,
            members: body_members,
            external_refs: sorted_refs(body.external_refs.into_iter().collect()),
            external_selects: sorted_selects(body.external_selects.into_iter().collect()),
            external_catches: sorted_catches(body.external_catches.into_iter().collect()),
        },
    })
}

pub(crate) fn legacy_instance_snapshot(
    root: TypeDeclId,
    modules: &ModuleTable,
    poly: &PolyArena,
    labels: &DumpLabels,
) -> Result<Vec<u8>, TypedActTemplateBundleError> {
    let identity = modules.capture_nominal_act_identity(root).ok_or_else(|| {
        TypedActTemplateBundleError::MissingTemplateIdentity(vec![format!("{root:?}")])
    })?;
    let typed = TypedActTemplate::capture(&identity, poly)
        .map_err(|error| TypedActTemplateBundleError::Snapshot(format!("{error:?}")))?;
    let body = typed
        .capture_body(&identity, poly, modules, labels)
        .map_err(|error| TypedActTemplateBundleError::Snapshot(format!("{error:?}")))?;
    let mut scheme_members = typed
        .members
        .iter()
        .map(|member| (member.key.clone(), member.scheme.clone()))
        .collect::<Vec<_>>();
    scheme_members.sort_by_key(|(key, _)| member_sort_key(key));
    let mut body_members = body
        .members
        .iter()
        .map(|member| (member.key.clone(), member.detached))
        .collect::<Vec<_>>();
    body_members.sort_by_key(|(key, _)| member_sort_key(key));
    encode_shadow_snapshot(ShadowInstantiationSnapshot {
        schemes: PortableSchemeTemplate {
            internal_nominal_paths: typed.internal_nominal_paths,
            members: scheme_members,
            types: typed.types,
            external_references: sorted_keys(typed.external_references.into_iter()),
        },
        body: PortableBodyTemplate {
            arena: body.arena,
            labels: body.labels,
            members: body_members,
            external_refs: sorted_refs(body.external_refs.into_iter().collect()),
            external_selects: sorted_selects(body.external_selects.into_iter().collect()),
            external_catches: sorted_catches(body.external_catches.into_iter().collect()),
        },
    })
}

fn encode_shadow_snapshot(
    snapshot: ShadowInstantiationSnapshot,
) -> Result<Vec<u8>, TypedActTemplateBundleError> {
    bincode::serialize(&snapshot)
        .map_err(|error| TypedActTemplateBundleError::Snapshot(format!("snapshot encode: {error}")))
}

fn sorted_keys(
    keys: impl IntoIterator<Item = StableExternalReferenceKey>,
) -> Vec<StableExternalReferenceKey> {
    let mut keys = keys.into_iter().collect::<Vec<_>>();
    keys.sort_by_key(stable_key_sort_key);
    keys
}

fn sorted_refs(
    mut items: Vec<(RefId, StableExternalReferenceKey)>,
) -> Vec<(RefId, StableExternalReferenceKey)> {
    items.sort_by_key(|(id, _)| id.0);
    items
}

fn sorted_selects(
    mut items: Vec<(SelectId, StableExternalReferenceKey)>,
) -> Vec<(SelectId, StableExternalReferenceKey)> {
    items.sort_by_key(|(id, _)| id.0);
    items
}

fn sorted_catches(
    mut items: Vec<(CatchSite, StableExternalReferenceKey)>,
) -> Vec<(CatchSite, StableExternalReferenceKey)> {
    items.sort_by_key(|(site, _)| (site.expr.0, site.arm));
    items
}

impl SemanticStdManifest {
    pub fn new(mut modules: Vec<SemanticStdModule>) -> Self {
        modules.sort();
        modules.dedup();
        Self { modules }
    }
}

impl TypedActTemplateBundleProfile {
    fn to_live_catalog(
        &self,
        modules: &ModuleTable,
    ) -> Result<TypedActTemplateCatalog, TypedActTemplateBundleError> {
        let mut catalog = TypedActTemplateCatalog::new();
        for portable in &self.templates {
            let names = portable
                .identity
                .root_path
                .iter()
                .cloned()
                .map(Name)
                .collect::<Vec<_>>();
            let root = modules
                .type_path_at(modules.root_id(), &names, ModuleOrder::from_index(u32::MAX))
                .found()
                .ok_or_else(|| {
                    TypedActTemplateBundleError::MissingCanonicalTemplate(
                        portable.identity.root_path.clone(),
                    )
                })?;
            let identity = modules
                .capture_nominal_act_identity(root.id)
                .ok_or_else(|| {
                    TypedActTemplateBundleError::MissingTemplateIdentity(
                        portable.identity.root_path.clone(),
                    )
                })?;
            let root_path = portable.identity.root_path.as_slice();
            let live_members = identity
                .value_members
                .iter()
                .map(|member| {
                    Ok((
                        member_key(&identity, member, root_path).map_err(|error| {
                            TypedActTemplateBundleError::Capture(format!("{error:?}"))
                        })?,
                        member.source,
                    ))
                })
                .collect::<Result<Vec<_>, TypedActTemplateBundleError>>()?;
            let source_for = |key: &NominalActMemberKey| {
                live_members
                    .iter()
                    .find(|(candidate, _)| candidate == key)
                    .map(|(_, source)| *source)
                    .ok_or_else(|| {
                        TypedActTemplateBundleError::MissingLiveMember(member_sort_key(key))
                    })
            };
            let typed = TypedActTemplate {
                template_root_act: root.id,
                internal_nominal_paths: portable.schemes.internal_nominal_paths.clone(),
                members: portable
                    .schemes
                    .members
                    .iter()
                    .map(|(key, scheme)| {
                        Ok(TypedActTemplateMember {
                            key: key.clone(),
                            source: source_for(key)?,
                            scheme: scheme.clone(),
                        })
                    })
                    .collect::<Result<Vec<_>, TypedActTemplateBundleError>>()?,
                types: portable.schemes.types.clone(),
                external_references: portable
                    .schemes
                    .external_references
                    .iter()
                    .cloned()
                    .collect(),
            };
            let body = TypedActBodyTemplate {
                arena: portable.body.arena.clone(),
                labels: portable.body.labels.clone(),
                source_defs: Vec::new(),
                members: portable
                    .body
                    .members
                    .iter()
                    .map(|(key, detached)| {
                        Ok(TypedActBodyMember {
                            key: key.clone(),
                            source: source_for(key)?,
                            detached: *detached,
                        })
                    })
                    .collect::<Result<Vec<_>, TypedActTemplateBundleError>>()?,
                external_refs: portable.body.external_refs.iter().cloned().collect(),
                external_selects: portable.body.external_selects.iter().cloned().collect(),
                external_catches: portable.body.external_catches.iter().cloned().collect(),
            };
            let kind = match portable.kind {
                PortableTemplateKind::Var => SyntheticActCopyKind::Var,
                PortableTemplateKind::LabelSub => SyntheticActCopyKind::LabelSub,
            };
            catalog.insert_entry(TypedActTemplateCatalogEntry {
                kind,
                source_root: root.id,
                identity,
                typed,
                body,
            });
        }
        Ok(catalog)
    }
}

fn semantic_manifest_for_loaded_files(files: &[sources::LoadedFile]) -> SemanticStdManifest {
    SemanticStdManifest::new(
        files
            .iter()
            .filter(|file| {
                file.module_path
                    .segments
                    .first()
                    .is_some_and(|segment| segment.0 == "std")
            })
            .map(|file| SemanticStdModule {
                module_path: file
                    .module_path
                    .segments
                    .iter()
                    .map(|segment| segment.0.clone())
                    .collect(),
                source_hash: stable_source_hash(file.source.as_bytes()),
            })
            .collect(),
    )
}

fn stable_source_hash(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
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
