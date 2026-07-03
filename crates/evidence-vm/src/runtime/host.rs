use std::collections::{HashMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};

use super::{HostCtx, HostOpFn, HostOpRegistration, HostOutcome};

#[derive(Debug, Clone)]
pub(super) struct RuntimeHostRegistry {
    generated_manifest: Option<RuntimeGeneratedHostManifestLookup>,
    native_host_operations_enabled: bool,
}

impl RuntimeHostRegistry {
    #[cfg(test)]
    pub(super) fn new(native_host_operations_enabled: bool) -> Self {
        Self::with_manifest_and_registrations(native_host_operations_enabled, None, Vec::new())
    }

    pub(super) fn with_manifest(
        native_host_operations_enabled: bool,
        manifest: Option<poly::host_manifest::HostActManifest>,
    ) -> Self {
        Self::with_manifest_and_registrations(
            native_host_operations_enabled,
            manifest,
            super::builtin_host_registrations(),
        )
    }

    pub(super) fn with_manifest_and_registrations(
        native_host_operations_enabled: bool,
        generated_manifest: Option<poly::host_manifest::HostActManifest>,
        registrations: Vec<HostOpRegistration>,
    ) -> Self {
        let generated_manifest = generated_manifest
            .map(|manifest| RuntimeGeneratedHostManifestLookup::new(manifest, &registrations));
        Self {
            generated_manifest,
            native_host_operations_enabled,
        }
    }

    pub(super) fn resolve(&self, path: &[String]) -> Option<RuntimeHostRequestResolution> {
        self.generated_manifest
            .as_ref()?
            .resolve(path, self.native_host_operations_enabled)
    }

    pub(super) fn call(
        &self,
        operation: RuntimeHostResolvedOperation,
        ctx: &mut HostCtx<'_>,
        payload: &super::BoundaryValue,
    ) -> HostOutcome {
        catch_unwind(AssertUnwindSafe(|| (operation.f)(ctx, payload))).unwrap_or_else(|_| {
            HostOutcome::HostError(format!(
                "host operation {} panicked",
                operation.path.join("::")
            ))
        })
    }
}

#[derive(Debug, Clone)]
struct RuntimeGeneratedHostManifestLookup {
    act_paths: HashSet<Vec<String>>,
    operations: HashMap<Vec<String>, RuntimeGeneratedHostOperation>,
}

impl RuntimeGeneratedHostManifestLookup {
    fn new(
        manifest: poly::host_manifest::HostActManifest,
        registrations: &[HostOpRegistration],
    ) -> Self {
        assert_manifest_act_registrations_have_operations(&manifest, registrations);
        let act_path_by_id = manifest
            .acts
            .iter()
            .map(|act| (act.act_id.clone(), act.path.clone()))
            .collect::<HashMap<_, _>>();
        let act_paths = manifest
            .acts
            .iter()
            .map(|act| act.path.clone())
            .collect::<HashSet<_>>();
        let operations = manifest
            .operations
            .into_iter()
            .map(|operation| {
                let act_path = act_path_by_id
                    .get(&operation.act_id)
                    .expect("validated host manifest operation should reference an act")
                    .clone();
                let f = host_registration_for(
                    registrations,
                    &operation.act_id,
                    &operation.operation_id,
                );
                (
                    operation.path.clone(),
                    RuntimeGeneratedHostOperation {
                        act_id: operation.act_id,
                        operation_id: operation.operation_id,
                        act_path,
                        path: operation.path,
                        column: operation.column,
                        symbol: operation.symbol,
                        f,
                    },
                )
            })
            .collect::<HashMap<_, _>>();
        Self {
            act_paths,
            operations,
        }
    }

    fn resolve(
        &self,
        path: &[String],
        native_host_operations_enabled: bool,
    ) -> Option<RuntimeHostRequestResolution> {
        let Some(act_path) = self.act_path_for(path) else {
            return None;
        };
        let Some(operation) = self.operations.get(path) else {
            return Some(RuntimeHostRequestResolution::UnsupportedCapability(
                RuntimeHostCapabilityFailure { act_path },
            ));
        };
        if !native_host_operations_enabled {
            return Some(RuntimeHostRequestResolution::UnsupportedCapability(
                RuntimeHostCapabilityFailure {
                    act_path: operation.act_path.clone(),
                },
            ));
        }
        let Some(f) = operation.f else {
            return Some(RuntimeHostRequestResolution::UnsupportedCapability(
                RuntimeHostCapabilityFailure {
                    act_path: operation.act_path.clone(),
                },
            ));
        };
        Some(RuntimeHostRequestResolution::Operation(
            RuntimeHostResolvedOperation {
                act_id: operation.act_id.clone(),
                operation_id: operation.operation_id.clone(),
                path: operation.path.clone(),
                column: operation.column,
                symbol: operation.symbol.clone(),
                f,
            },
        ))
    }

    fn act_path_for(&self, path: &[String]) -> Option<Vec<String>> {
        (0..=path.len())
            .rev()
            .find_map(|len| self.act_paths.get(&path[..len]).cloned())
    }
}

#[derive(Debug, Clone)]
struct RuntimeGeneratedHostOperation {
    act_id: String,
    operation_id: String,
    act_path: Vec<String>,
    path: Vec<String>,
    column: u32,
    symbol: String,
    f: Option<HostOpFn>,
}

fn host_registration_for(
    registrations: &[HostOpRegistration],
    act_id: &str,
    operation_id: &str,
) -> Option<HostOpFn> {
    registrations
        .iter()
        .rev()
        .find(|registration| {
            registration.act_id == act_id && registration.operation_id == operation_id
        })
        .map(|registration| registration.f)
}

fn assert_manifest_act_registrations_have_operations(
    manifest: &poly::host_manifest::HostActManifest,
    registrations: &[HostOpRegistration],
) {
    if cfg!(debug_assertions) {
        let manifest_act_ids = manifest
            .acts
            .iter()
            .map(|act| act.act_id.as_str())
            .collect::<HashSet<_>>();
        for registration in registrations {
            if !manifest_act_ids.contains(registration.act_id) {
                continue;
            }
            debug_assert!(
                manifest.operations.iter().any(|operation| {
                    operation.act_id == registration.act_id
                        && operation.operation_id == registration.operation_id
                }),
                "host registration {}.{} has no operation in generated manifest",
                registration.act_id,
                registration.operation_id
            );
        }
    }
}

#[derive(Debug, Clone)]
pub(super) enum RuntimeHostRequestResolution {
    Operation(RuntimeHostResolvedOperation),
    UnsupportedCapability(RuntimeHostCapabilityFailure),
}

#[derive(Debug, Clone)]
pub(super) struct RuntimeHostResolvedOperation {
    act_id: String,
    operation_id: String,
    path: Vec<String>,
    column: u32,
    symbol: String,
    f: HostOpFn,
}

impl RuntimeHostResolvedOperation {
    pub(super) fn act_id(&self) -> &str {
        &self.act_id
    }

    pub(super) fn operation_id(&self) -> &str {
        &self.operation_id
    }

    pub(super) fn path_strings(&self) -> Vec<String> {
        self.path.clone()
    }

    pub(super) fn column(&self) -> u32 {
        self.column
    }

    pub(super) fn symbol(&self) -> &str {
        &self.symbol
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RuntimeHostCapabilityFailure {
    act_path: Vec<String>,
}

impl RuntimeHostCapabilityFailure {
    pub(super) fn act_path_strings(self) -> Vec<String> {
        self.act_path
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_host_registry_reports_unsupported_capability_before_operation() {
        let registry = RuntimeHostRegistry::with_manifest_and_registrations(
            false,
            Some(custom_host_manifest()),
            vec![custom_host_registration("call")],
        );
        let path = ["test".into(), "host".into(), "bridge".into(), "call".into()];

        let Some(RuntimeHostRequestResolution::UnsupportedCapability(failure)) =
            registry.resolve(&path)
        else {
            panic!("disabled host operation should report unsupported capability");
        };
        assert_eq!(
            failure,
            RuntimeHostCapabilityFailure {
                act_path: vec!["test".into(), "host".into(), "bridge".into()]
            }
        );
    }

    #[test]
    fn runtime_host_registry_resolves_to_operation_spec_when_enabled() {
        let registry = RuntimeHostRegistry::with_manifest_and_registrations(
            true,
            Some(custom_host_manifest()),
            vec![custom_host_registration("call")],
        );
        let path = ["test".into(), "host".into(), "bridge".into(), "call".into()];

        let Some(RuntimeHostRequestResolution::Operation(operation)) = registry.resolve(&path)
        else {
            panic!("enabled host operation should resolve to registered operation");
        };
        assert_eq!(operation.act_id(), "test.host.bridge");
        assert_eq!(operation.operation_id(), "call");
        assert_eq!(operation.path_strings(), path.to_vec());
        assert_eq!(operation.column(), 0);
        assert_eq!(operation.symbol(), "yu_host_4test4host6bridge_4call");
    }

    #[test]
    fn runtime_host_registry_reports_known_act_unknown_op_as_capability_failure() {
        let registry = RuntimeHostRegistry::with_manifest_and_registrations(
            true,
            Some(custom_host_manifest()),
            vec![custom_host_registration("call")],
        );
        let path = [
            "test".into(),
            "host".into(),
            "bridge".into(),
            "missing".into(),
        ];

        let Some(RuntimeHostRequestResolution::UnsupportedCapability(failure)) =
            registry.resolve(&path)
        else {
            panic!("known file act with unknown op should report unsupported capability");
        };
        assert_eq!(
            failure,
            RuntimeHostCapabilityFailure {
                act_path: vec!["test".into(), "host".into(), "bridge".into()]
            }
        );
    }

    #[test]
    fn runtime_host_registry_uses_longest_manifest_act_prefix() {
        let registry = RuntimeHostRegistry::with_manifest_and_registrations(
            true,
            Some(nested_custom_host_manifest()),
            Vec::new(),
        );
        let path = [
            "test".into(),
            "host".into(),
            "bridge".into(),
            "missing".into(),
        ];

        let Some(RuntimeHostRequestResolution::UnsupportedCapability(failure)) =
            registry.resolve(&path)
        else {
            panic!("known nested host act with unknown op should report unsupported capability");
        };
        assert_eq!(
            failure,
            RuntimeHostCapabilityFailure {
                act_path: vec!["test".into(), "host".into(), "bridge".into()]
            }
        );
    }

    #[test]
    fn runtime_host_registry_uses_generated_manifest_for_custom_host_act_capability() {
        let registry = RuntimeHostRegistry::with_manifest_and_registrations(
            true,
            Some(custom_host_manifest()),
            Vec::new(),
        );
        let path = ["test".into(), "host".into(), "bridge".into(), "call".into()];

        let Some(RuntimeHostRequestResolution::UnsupportedCapability(failure)) =
            registry.resolve(&path)
        else {
            panic!(
                "manifest host act without a runtime registration should be a capability failure"
            );
        };
        assert_eq!(
            failure,
            RuntimeHostCapabilityFailure {
                act_path: vec!["test".into(), "host".into(), "bridge".into()]
            }
        );
    }

    #[test]
    fn runtime_host_registry_resolves_generated_manifest_registration() {
        let registry = RuntimeHostRegistry::with_manifest_and_registrations(
            true,
            Some(custom_host_manifest()),
            vec![custom_host_registration("call")],
        );
        let path = ["test".into(), "host".into(), "bridge".into(), "call".into()];

        let Some(RuntimeHostRequestResolution::Operation(operation)) = registry.resolve(&path)
        else {
            panic!("registered generated host operation should resolve");
        };
        assert_eq!(operation.act_id(), "test.host.bridge");
        assert_eq!(operation.operation_id(), "call");
        assert_eq!(operation.path_strings(), path.to_vec());
        assert_eq!(operation.column(), 0);
        assert_eq!(operation.symbol(), "yu_host_4test4host6bridge_4call");
    }

    #[test]
    fn runtime_host_registry_prefers_later_registration_for_same_operation() {
        let registry = RuntimeHostRegistry::with_manifest_and_registrations(
            true,
            Some(custom_host_manifest()),
            vec![
                custom_host_registration_with("call", first_custom_host_call),
                custom_host_registration_with("call", second_custom_host_call),
            ],
        );
        let path = ["test".into(), "host".into(), "bridge".into(), "call".into()];

        let Some(RuntimeHostRequestResolution::Operation(operation)) = registry.resolve(&path)
        else {
            panic!("registered generated host operation should resolve");
        };
        let mut state = ();
        let mut ctx = HostCtx::new(&mut state);

        assert_eq!(
            registry.call(operation, &mut ctx, &super::super::BoundaryValue::Unit),
            HostOutcome::Return(super::super::BoundaryValue::Int(2))
        );
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(
        expected = "host registration test.host.bridge.missing has no operation in generated manifest"
    )]
    fn runtime_host_registry_rejects_missing_operation_registration_for_manifest_act() {
        RuntimeHostRegistry::with_manifest_and_registrations(
            true,
            Some(custom_host_manifest()),
            vec![custom_host_registration("missing")],
        );
    }

    #[test]
    fn runtime_host_registry_ignores_registrations_for_absent_manifest_acts() {
        let registry = RuntimeHostRegistry::with_manifest_and_registrations(
            true,
            Some(unrelated_host_manifest()),
            vec![custom_host_registration("call")],
        );
        let path = ["test".into(), "host".into(), "bridge".into(), "call".into()];

        assert!(registry.resolve(&path).is_none());
    }

    #[test]
    fn runtime_host_registry_leaves_unknown_effects_unresolved() {
        let registry = RuntimeHostRegistry::new(false);
        let path = ["std".into(), "unknown".into(), "op".into()];

        assert!(registry.resolve(&path).is_none());
    }

    fn custom_host_registration(operation_id: &'static str) -> HostOpRegistration {
        custom_host_registration_with(operation_id, custom_host_call)
    }

    fn custom_host_registration_with(
        operation_id: &'static str,
        f: HostOpFn,
    ) -> HostOpRegistration {
        HostOpRegistration {
            act_id: "test.host.bridge",
            operation_id,
            f,
        }
    }

    fn custom_host_call(_: &mut HostCtx<'_>, _: &super::super::BoundaryValue) -> HostOutcome {
        HostOutcome::Return(super::super::BoundaryValue::Unit)
    }

    fn first_custom_host_call(_: &mut HostCtx<'_>, _: &super::super::BoundaryValue) -> HostOutcome {
        HostOutcome::Return(super::super::BoundaryValue::Int(1))
    }

    fn second_custom_host_call(
        _: &mut HostCtx<'_>,
        _: &super::super::BoundaryValue,
    ) -> HostOutcome {
        HostOutcome::Return(super::super::BoundaryValue::Int(2))
    }

    fn custom_host_manifest() -> poly::host_manifest::HostActManifest {
        poly::host_manifest::HostActManifest::new(
            vec![poly::host_manifest::HostActManifestAct {
                act_id: "test.host.bridge".to_string(),
                path: vec!["test".into(), "host".into(), "bridge".into()],
            }],
            vec![poly::host_manifest::HostActManifestOperationInput {
                act_id: "test.host.bridge".to_string(),
                operation_id: "call".to_string(),
                path: vec!["test".into(), "host".into(), "bridge".into(), "call".into()],
                tier: poly::host_manifest::HostOperationTier::Sync,
                surface: poly::host_manifest::HostOperationSurface::Contract,
                signature: "() -> int".to_string(),
            }],
        )
        .expect("custom host manifest should be valid")
    }

    fn nested_custom_host_manifest() -> poly::host_manifest::HostActManifest {
        poly::host_manifest::HostActManifest::new(
            vec![
                poly::host_manifest::HostActManifestAct {
                    act_id: "test.host".to_string(),
                    path: vec!["test".into(), "host".into()],
                },
                poly::host_manifest::HostActManifestAct {
                    act_id: "test.host.bridge".to_string(),
                    path: vec!["test".into(), "host".into(), "bridge".into()],
                },
            ],
            vec![
                poly::host_manifest::HostActManifestOperationInput {
                    act_id: "test.host".to_string(),
                    operation_id: "root".to_string(),
                    path: vec!["test".into(), "host".into(), "root".into()],
                    tier: poly::host_manifest::HostOperationTier::Sync,
                    surface: poly::host_manifest::HostOperationSurface::Contract,
                    signature: "() -> int".to_string(),
                },
                poly::host_manifest::HostActManifestOperationInput {
                    act_id: "test.host.bridge".to_string(),
                    operation_id: "call".to_string(),
                    path: vec!["test".into(), "host".into(), "bridge".into(), "call".into()],
                    tier: poly::host_manifest::HostOperationTier::Sync,
                    surface: poly::host_manifest::HostOperationSurface::Contract,
                    signature: "() -> int".to_string(),
                },
            ],
        )
        .expect("nested custom host manifest should be valid")
    }

    fn unrelated_host_manifest() -> poly::host_manifest::HostActManifest {
        poly::host_manifest::HostActManifest::new(
            vec![poly::host_manifest::HostActManifestAct {
                act_id: "other.host.bridge".to_string(),
                path: vec!["other".into(), "host".into(), "bridge".into()],
            }],
            vec![poly::host_manifest::HostActManifestOperationInput {
                act_id: "other.host.bridge".to_string(),
                operation_id: "call".to_string(),
                path: vec![
                    "other".into(),
                    "host".into(),
                    "bridge".into(),
                    "call".into(),
                ],
                tier: poly::host_manifest::HostOperationTier::Sync,
                surface: poly::host_manifest::HostOperationSurface::Contract,
                signature: "() -> int".to_string(),
            }],
        )
        .expect("unrelated custom host manifest should be valid")
    }
}
