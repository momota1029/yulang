//! Shared, shadow-only catalog and finalized-instance installation for typed act templates.

#![allow(
    dead_code,
    reason = "M1-4 remains a comparison harness until the M1-5 cutover"
)]

use super::ModuleTable;
use super::nominal_act_identity::{NominalActInstanceSubstitution, NominalActTemplateIdentity};
use super::typed_act_body::{CatchSite, TypedActBodyError, TypedActBodyTemplate};
use super::typed_act_template::{
    StableExternalReferenceKey, TypedActSchemeInstantiation, TypedActTemplate,
    TypedActTemplateError,
};
use crate::analysis::{AnalysisSession, FinalizedTemplateInstallError};
use crate::{CompiledBoundaryInterface, CompiledRuntimeSurface, TypeDeclId};
use poly::dump::DumpLabels;
use poly::expr::{DefId, Expr, SelectResolution};
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum SyntheticActCopyKind {
    Var,
    LabelSub,
}

pub(crate) struct TypedActTemplateCatalog {
    entries: FxHashMap<(SyntheticActCopyKind, TypeDeclId), TypedActTemplateCatalogEntry>,
}

pub(crate) struct TypedActTemplateCatalogEntry {
    pub(crate) kind: SyntheticActCopyKind,
    pub(crate) source_root: TypeDeclId,
    pub(crate) identity: NominalActTemplateIdentity,
    pub(crate) typed: TypedActTemplate,
    pub(crate) body: TypedActBodyTemplate,
}

pub(crate) struct TypedActInstalledInstance {
    pub(crate) schemes: TypedActSchemeInstantiation,
    pub(crate) member_defs: Vec<DefId>,
}

#[derive(Debug)]
pub(crate) enum TypedActCatalogError {
    Scheme(TypedActTemplateError),
    Body(TypedActBodyError),
    MissingEntry,
    MissingExternal(StableExternalReferenceKey),
    UnsupportedExternalSelection(StableExternalReferenceKey),
    Install(FinalizedTemplateInstallError),
}

impl TypedActTemplateCatalog {
    pub(crate) fn new() -> Self {
        Self {
            entries: FxHashMap::default(),
        }
    }

    pub(crate) fn capture(
        &mut self,
        kind: SyntheticActCopyKind,
        identity: NominalActTemplateIdentity,
        source: &poly::expr::Arena,
        modules: &ModuleTable,
        labels: &DumpLabels,
    ) -> Result<(), TypedActCatalogError> {
        let typed =
            TypedActTemplate::capture(&identity, source).map_err(TypedActCatalogError::Scheme)?;
        let body = typed
            .capture_body(&identity, source, modules, labels)
            .map_err(TypedActCatalogError::Body)?;
        let source_root = identity.root_act;
        self.entries.insert(
            (kind, source_root),
            TypedActTemplateCatalogEntry {
                kind,
                source_root,
                identity,
                typed,
                body,
            },
        );
        Ok(())
    }

    pub(crate) fn entry(
        &self,
        kind: SyntheticActCopyKind,
        source_root: TypeDeclId,
    ) -> Option<&TypedActTemplateCatalogEntry> {
        self.entries.get(&(kind, source_root))
    }
}

impl TypedActTemplateCatalogEntry {
    /// Install one verified detached instance into its already-minted destination member IDs.
    pub(crate) fn install(
        &self,
        substitution: &NominalActInstanceSubstitution,
        session: &mut AnalysisSession,
        modules: &ModuleTable,
        labels: &mut DumpLabels,
    ) -> Result<TypedActInstalledInstance, TypedActCatalogError> {
        let schemes = self
            .typed
            .apply(substitution)
            .map_err(TypedActCatalogError::Scheme)?;
        let product = self
            .body
            .apply(substitution)
            .map_err(TypedActCatalogError::Body)?;
        let mut arena = product.arena;
        let mut proxies = FxHashMap::<StableExternalReferenceKey, DefId>::default();
        let mut external_defs = Vec::new();
        let mut proxy_for = |key: &StableExternalReferenceKey,
                             arena: &mut poly::expr::Arena|
         -> Result<DefId, TypedActCatalogError> {
            if let Some(proxy) = proxies.get(key) {
                return Ok(*proxy);
            }
            let target = modules
                .resolve_stable_external_reference_key(key)
                .ok_or_else(|| TypedActCatalogError::MissingExternal(key.clone()))?;
            let proxy = arena.defs.fresh();
            proxies.insert(key.clone(), proxy);
            external_defs.push((proxy, target));
            Ok(proxy)
        };
        for (reference, key) in &product.external_refs {
            let proxy = proxy_for(key, &mut arena)?;
            arena.resolve_ref(*reference, proxy);
        }
        for (select, key) in &product.external_selects {
            let proxy = proxy_for(key, &mut arena)?;
            match key {
                StableExternalReferenceKey::Method { .. }
                | StableExternalReferenceKey::FieldMethod { .. }
                | StableExternalReferenceKey::Operation { .. } => {
                    arena.resolve_select(*select, SelectResolution::Method { def: proxy });
                }
                _ => {
                    return Err(TypedActCatalogError::UnsupportedExternalSelection(
                        key.clone(),
                    ));
                }
            }
        }
        for (CatchSite { expr, arm }, key) in &product.external_catches {
            let proxy = proxy_for(key, &mut arena)?;
            let mut body = arena.expr(*expr).clone();
            let Expr::Catch(_, arms) = &mut body else {
                return Err(TypedActCatalogError::Body(
                    TypedActBodyError::MissingExternalOperationPath(Vec::new()),
                ));
            };
            let operation = arms
                .get_mut(*arm)
                .and_then(|arm| arm.operation.as_mut())
                .ok_or_else(|| {
                    TypedActCatalogError::Body(TypedActBodyError::MissingExternalOperationPath(
                        Vec::new(),
                    ))
                })?;
            operation.def = Some(proxy);
            arena.set_expr(*expr, body);
        }

        let surface = CompiledRuntimeSurface {
            arena,
            boundary: CompiledBoundaryInterface::empty(),
            labels: product.labels,
            modules: Vec::new(),
            values: Vec::new(),
        };
        let preallocated = product.member_destinations.into_iter().collect::<Vec<_>>();
        let member_defs = preallocated
            .iter()
            .map(|(_, destination)| *destination)
            .collect::<Vec<_>>();
        surface.import_into_with_mapped_defs(
            &mut session.poly,
            labels,
            preallocated,
            external_defs,
        );
        session
            .install_finalized_template_defs(member_defs.iter().copied())
            .map_err(TypedActCatalogError::Install)?;
        Ok(TypedActInstalledInstance {
            schemes,
            member_defs,
        })
    }
}
