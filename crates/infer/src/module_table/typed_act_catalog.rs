//! Shared catalog and finalized-instance installation for typed act templates.

use super::ModuleTable;
use super::nominal_act_identity::{NominalActInstanceSubstitution, NominalActTemplateIdentity};
use super::typed_act_body::{CatchSite, TypedActBodyError, TypedActBodyTemplate};
use super::typed_act_template::{
    StableExternalReferenceKey, TypedActSchemeInstantiation, TypedActTemplate,
    TypedActTemplateError,
};
use crate::analysis::{AnalysisSession, FinalizedTemplateInstallError};
use crate::instantiate::{
    ImportedBoundarySubstitution, validate_imported_scheme_for_instantiation,
};
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
    #[allow(dead_code, reason = "retained as the catalog entry's audited identity")]
    pub(crate) kind: SyntheticActCopyKind,
    #[allow(dead_code, reason = "retained as the catalog entry's audited identity")]
    pub(crate) source_root: TypeDeclId,
    #[allow(
        dead_code,
        reason = "retained for catalog parity and later serialization"
    )]
    pub(crate) identity: NominalActTemplateIdentity,
    pub(crate) typed: TypedActTemplate,
    pub(crate) body: TypedActBodyTemplate,
}

pub(crate) struct TypedActInstalledInstance {
    #[allow(dead_code, reason = "consumed by shadow parity oracles in test builds")]
    pub(crate) schemes: TypedActSchemeInstantiation,
    #[allow(
        dead_code,
        reason = "consumed by lifecycle parity oracles in test builds"
    )]
    pub(crate) member_defs: Vec<DefId>,
}

pub(crate) struct PreparedTypedActInstance {
    surface: CompiledRuntimeSurface,
    preallocated: Vec<(DefId, DefId)>,
    external_defs: Vec<(DefId, DefId)>,
    schemes: TypedActSchemeInstantiation,
    member_defs: Vec<DefId>,
}

#[derive(Debug)]
#[allow(
    dead_code,
    reason = "fail-closed production fallback retains detailed rejection evidence for tests and debugging"
)]
pub(crate) enum TypedActCatalogError {
    Scheme(TypedActTemplateError),
    Body(TypedActBodyError),
    MissingExternal(StableExternalReferenceKey),
    SourceDefinitionOutsidePrefix(DefId),
    ExternalDefinitionOutsidePrefix {
        key: StableExternalReferenceKey,
        def: DefId,
    },
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

    pub(crate) fn insert_entry(&mut self, entry: TypedActTemplateCatalogEntry) {
        self.entries.insert((entry.kind, entry.source_root), entry);
    }
}

impl TypedActTemplateCatalogEntry {
    pub(crate) fn source_definitions_are_prefix_owned(
        &self,
        contains: impl Fn(DefId) -> bool,
    ) -> Result<(), TypedActCatalogError> {
        self.body
            .source_defs
            .iter()
            .copied()
            .find(|def| !contains(*def))
            .map_or(Ok(()), |def| {
                Err(TypedActCatalogError::SourceDefinitionOutsidePrefix(def))
            })
    }

    /// Validate and detach every fallible input without mutating the live compilation arena.
    pub(crate) fn prepare(
        &self,
        substitution: &NominalActInstanceSubstitution,
        modules: &ModuleTable,
        external_def_is_eligible: impl Fn(DefId) -> bool,
    ) -> Result<PreparedTypedActInstance, TypedActCatalogError> {
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
            if !external_def_is_eligible(target) {
                return Err(TypedActCatalogError::ExternalDefinitionOutsidePrefix {
                    key: key.clone(),
                    def: target,
                });
            }
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
        let mut preallocated = product.member_destinations.into_iter().collect::<Vec<_>>();
        preallocated.sort_by_key(|(detached, destination)| (detached.0, destination.0));
        let member_defs = preallocated
            .iter()
            .map(|(_, destination)| *destination)
            .collect::<Vec<_>>();
        let empty_boundary = ImportedBoundarySubstitution::default();
        for member in &schemes.members {
            validate_imported_scheme_for_instantiation(
                &schemes.types,
                &member.scheme,
                &empty_boundary,
            )
            .map_err(|error| {
                TypedActCatalogError::Install(FinalizedTemplateInstallError::InvalidScheme {
                    def: member.destination,
                    error,
                })
            })?;
        }
        for (detached, destination) in &preallocated {
            let Some(poly::expr::Def::Let {
                scheme: Some(scheme),
                ..
            }) = surface.arena.defs.get(*detached)
            else {
                return Err(TypedActCatalogError::Install(
                    FinalizedTemplateInstallError::MissingClosedScheme { def: *destination },
                ));
            };
            validate_imported_scheme_for_instantiation(&surface.arena.typ, scheme, &empty_boundary)
                .map_err(|error| {
                    TypedActCatalogError::Install(FinalizedTemplateInstallError::InvalidScheme {
                        def: *destination,
                        error,
                    })
                })?;
        }
        Ok(PreparedTypedActInstance {
            surface,
            preallocated,
            external_defs,
            schemes,
            member_defs,
        })
    }

    #[cfg(test)]
    pub(crate) fn install(
        &self,
        substitution: &NominalActInstanceSubstitution,
        session: &mut AnalysisSession,
        modules: &ModuleTable,
        labels: &mut DumpLabels,
    ) -> Result<TypedActInstalledInstance, TypedActCatalogError> {
        Ok(self
            .prepare(substitution, modules, |_| true)?
            .commit(session, labels))
    }
}

impl PreparedTypedActInstance {
    /// Infallible commit after `prepare` has validated closure, anchors, and closed schemes.
    pub(crate) fn commit(
        self,
        session: &mut AnalysisSession,
        labels: &mut DumpLabels,
    ) -> TypedActInstalledInstance {
        self.surface.import_into_with_mapped_defs(
            &mut session.poly,
            labels,
            self.preallocated,
            self.external_defs,
        );
        session.seed_validated_finalized_template_defs(self.member_defs.iter().copied());
        TypedActInstalledInstance {
            schemes: self.schemes,
            member_defs: self.member_defs,
        }
    }
}
