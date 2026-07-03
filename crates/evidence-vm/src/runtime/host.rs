use std::panic::{AssertUnwindSafe, catch_unwind};

use super::{HostCtx, HostOpFn, HostOpRegistration, HostOutcome};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeHostAct {
    ConsoleOut,
    File,
}

impl RuntimeHostAct {
    pub(super) fn path(self) -> &'static [&'static str] {
        match self {
            Self::ConsoleOut => &["std", "io", "console", "out"],
            Self::File => &["std", "io", "file", "file"],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuntimeHostOperationTier {
    Sync,
    SuspendOneShot,
    SuspendMultiShot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuntimeHostOperationSurface {
    Contract,
    RawCompatibility,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeHostOperation {
    ConsoleOutWrite,
    FileLoad,
    FileStore,
    FileMeta,
    FileReadAt,
    FileWriteAt,
    FileAmbientTouch,
    FileAmbientGet,
    FileAmbientSet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostOperationSpec {
    pub(super) act: RuntimeHostAct,
    operation_id: &'static str,
    tier: RuntimeHostOperationTier,
    surface: RuntimeHostOperationSurface,
    signature: &'static str,
    path: &'static [&'static str],
    pub(super) operation: RuntimeHostOperation,
}

impl RuntimeHostOperationSpec {
    pub(super) fn path_strings(self) -> Vec<String> {
        self.path.iter().map(|part| (*part).to_string()).collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostManifest {
    operations: &'static [RuntimeHostOperationSpec],
    acts: &'static [RuntimeHostAct],
}

impl RuntimeHostManifest {
    const fn new(
        operations: &'static [RuntimeHostOperationSpec],
        acts: &'static [RuntimeHostAct],
    ) -> Self {
        Self { operations, acts }
    }

    fn operation_spec(self, path: &[String]) -> Option<&'static RuntimeHostOperationSpec> {
        self.operations
            .iter()
            .find(|spec| runtime_host_path_matches(path, spec.path))
            .inspect(|spec| {
                debug_assert_eq!(spec.tier, RuntimeHostOperationTier::Sync);
                debug_assert!(spec.path.starts_with(spec.act.path()));
                debug_assert_eq!(spec.path.last().copied(), Some(spec.operation_id));
            })
    }

    fn act_for_path(self, path: &[String]) -> Option<RuntimeHostAct> {
        self.acts
            .iter()
            .copied()
            .find(|act| runtime_host_path_starts_with(path, act.path()))
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct RuntimeHostRegistry {
    manifest: RuntimeHostManifest,
    native_host_operations_enabled: bool,
    registrations: &'static [HostOpRegistration],
}

impl RuntimeHostRegistry {
    pub(super) fn new(native_host_operations_enabled: bool) -> Self {
        Self::with_registrations(
            native_host_operations_enabled,
            super::builtin_host_registrations(),
        )
    }

    pub(super) fn with_registrations(
        native_host_operations_enabled: bool,
        registrations: Vec<HostOpRegistration>,
    ) -> Self {
        Self {
            manifest: RUNTIME_HOST_MANIFEST,
            native_host_operations_enabled,
            registrations: Box::leak(registrations.into_boxed_slice()),
        }
    }

    pub(super) fn resolve(&self, path: &[String]) -> Option<RuntimeHostRequestResolution> {
        let Some(spec) = self.manifest.operation_spec(path) else {
            return self.resolve_known_act_without_registered_operation(path);
        };
        if !self.native_host_operations_enabled {
            return Some(RuntimeHostRequestResolution::UnsupportedCapability(
                RuntimeHostCapabilityFailure { act: spec.act },
            ));
        }
        let Some(f) = self.registration_for(spec) else {
            return Some(RuntimeHostRequestResolution::UnsupportedCapability(
                RuntimeHostCapabilityFailure { act: spec.act },
            ));
        };
        Some(RuntimeHostRequestResolution::Operation(
            RuntimeHostResolvedOperation { spec, f },
        ))
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
                operation.spec.path.join("::")
            ))
        })
    }

    fn registration_for(&self, spec: &RuntimeHostOperationSpec) -> Option<HostOpFn> {
        let act_id = spec.act.manifest_id();
        self.registrations
            .iter()
            .rev()
            .find(|registration| {
                registration.act_id == act_id && registration.operation_id == spec.operation_id
            })
            .map(|registration| registration.f)
    }

    fn resolve_known_act_without_registered_operation(
        &self,
        path: &[String],
    ) -> Option<RuntimeHostRequestResolution> {
        let act = self.manifest.act_for_path(path)?;
        Some(RuntimeHostRequestResolution::UnsupportedCapability(
            RuntimeHostCapabilityFailure { act },
        ))
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) enum RuntimeHostRequestResolution {
    Operation(RuntimeHostResolvedOperation),
    UnsupportedCapability(RuntimeHostCapabilityFailure),
}

#[derive(Debug, Clone, Copy)]
pub(super) struct RuntimeHostResolvedOperation {
    pub(super) spec: &'static RuntimeHostOperationSpec,
    f: HostOpFn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostCapabilityFailure {
    act: RuntimeHostAct,
}

impl RuntimeHostCapabilityFailure {
    pub(super) fn act_path_strings(self) -> Vec<String> {
        self.act
            .path()
            .iter()
            .map(|part| (*part).to_string())
            .collect()
    }
}

pub(crate) fn runtime_host_manifest_has_known_act(path: &[String]) -> bool {
    RUNTIME_HOST_MANIFEST.act_for_path(path).is_some()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct RuntimeHostManifestOperation {
    pub act_id: &'static str,
    pub operation_id: &'static str,
    pub tier: &'static str,
    pub surface: &'static str,
    pub signature: &'static str,
    pub path: &'static [&'static str],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct RuntimeHostManifestTier {
    pub id: &'static str,
}

pub fn runtime_host_manifest_operations() -> Vec<RuntimeHostManifestOperation> {
    RUNTIME_HOST_OPERATIONS
        .iter()
        .map(|spec| RuntimeHostManifestOperation {
            act_id: spec.act.manifest_id(),
            operation_id: spec.operation_id,
            tier: spec.tier.manifest_id(),
            surface: spec.surface.manifest_id(),
            signature: spec.signature,
            path: spec.path,
        })
        .collect()
}

pub fn runtime_host_manifest_tiers() -> Vec<RuntimeHostManifestTier> {
    RUNTIME_HOST_OPERATION_TIERS
        .iter()
        .map(|tier| RuntimeHostManifestTier {
            id: tier.manifest_id(),
        })
        .collect()
}

impl RuntimeHostAct {
    fn manifest_id(self) -> &'static str {
        match self {
            Self::ConsoleOut => "std.io.console.out",
            Self::File => "std.io.file.file",
        }
    }
}

impl RuntimeHostOperationTier {
    fn manifest_id(self) -> &'static str {
        match self {
            Self::Sync => "sync",
            Self::SuspendOneShot => "suspend-one-shot",
            Self::SuspendMultiShot => "suspend-multi-shot",
        }
    }
}

impl RuntimeHostOperationSurface {
    fn manifest_id(self) -> &'static str {
        match self {
            Self::Contract => "contract",
            Self::RawCompatibility => "raw-compat",
        }
    }
}

const RUNTIME_HOST_OPERATION_TIERS: &[RuntimeHostOperationTier] = &[
    RuntimeHostOperationTier::Sync,
    RuntimeHostOperationTier::SuspendOneShot,
    RuntimeHostOperationTier::SuspendMultiShot,
];

const RUNTIME_HOST_OPERATIONS: &[RuntimeHostOperationSpec] = &[
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::ConsoleOut,
        operation_id: "write",
        tier: RuntimeHostOperationTier::Sync,
        surface: RuntimeHostOperationSurface::Contract,
        signature: "str -> ()",
        path: &["std", "io", "console", "out", "write"],
        operation: RuntimeHostOperation::ConsoleOutWrite,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "load",
        tier: RuntimeHostOperationTier::Sync,
        surface: RuntimeHostOperationSurface::Contract,
        signature: "path -> result str io_err",
        path: &["std", "io", "file", "file", "load"],
        operation: RuntimeHostOperation::FileLoad,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "store",
        tier: RuntimeHostOperationTier::Sync,
        surface: RuntimeHostOperationSurface::Contract,
        signature: "(path, str) -> result unit io_err",
        path: &["std", "io", "file", "file", "store"],
        operation: RuntimeHostOperation::FileStore,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "meta",
        tier: RuntimeHostOperationTier::Sync,
        surface: RuntimeHostOperationSurface::Contract,
        signature: "path -> file_meta",
        path: &["std", "io", "file", "file", "meta"],
        operation: RuntimeHostOperation::FileMeta,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "read_at",
        tier: RuntimeHostOperationTier::Sync,
        surface: RuntimeHostOperationSurface::RawCompatibility,
        signature: "(path, range) -> result (str, range) io_err",
        path: &["std", "io", "file", "file", "read_at"],
        operation: RuntimeHostOperation::FileReadAt,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "write_at",
        tier: RuntimeHostOperationTier::Sync,
        surface: RuntimeHostOperationSurface::RawCompatibility,
        signature: "(path, range, str) -> result unit io_err",
        path: &["std", "io", "file", "file", "write_at"],
        operation: RuntimeHostOperation::FileWriteAt,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "ambient_touch",
        tier: RuntimeHostOperationTier::Sync,
        surface: RuntimeHostOperationSurface::Contract,
        signature: "path -> result unit io_err",
        path: &["std", "io", "file", "file", "ambient_touch"],
        operation: RuntimeHostOperation::FileAmbientTouch,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "ambient_get",
        tier: RuntimeHostOperationTier::Sync,
        surface: RuntimeHostOperationSurface::Contract,
        signature: "path -> str",
        path: &["std", "io", "file", "file", "ambient_get"],
        operation: RuntimeHostOperation::FileAmbientGet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "ambient_set",
        tier: RuntimeHostOperationTier::Sync,
        surface: RuntimeHostOperationSurface::Contract,
        signature: "(path, str) -> unit",
        path: &["std", "io", "file", "file", "ambient_set"],
        operation: RuntimeHostOperation::FileAmbientSet,
    },
];

const RUNTIME_HOST_ACTS: &[RuntimeHostAct] = &[RuntimeHostAct::ConsoleOut, RuntimeHostAct::File];

const RUNTIME_HOST_MANIFEST: RuntimeHostManifest =
    RuntimeHostManifest::new(RUNTIME_HOST_OPERATIONS, RUNTIME_HOST_ACTS);

#[cfg(test)]
fn runtime_host_operation_spec(path: &[String]) -> Option<&'static RuntimeHostOperationSpec> {
    RUNTIME_HOST_MANIFEST.operation_spec(path)
}

#[cfg(test)]
fn runtime_host_operation(path: &[String]) -> Option<RuntimeHostOperation> {
    runtime_host_operation_spec(path).map(|spec| spec.operation)
}

fn runtime_host_path_matches(path: &[String], expected: &[&str]) -> bool {
    path.iter().map(String::as_str).eq(expected.iter().copied())
}

fn runtime_host_path_starts_with(path: &[String], expected_prefix: &[&str]) -> bool {
    path.iter()
        .map(String::as_str)
        .zip(expected_prefix.iter().copied())
        .all(|(actual, expected)| actual == expected)
        && path.len() >= expected_prefix.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn runtime_host_operation_table_resolves_current_console_and_file_ops() {
        for spec in RUNTIME_HOST_OPERATIONS {
            let path = spec
                .path
                .iter()
                .map(|part| (*part).to_string())
                .collect::<Vec<_>>();
            assert_eq!(runtime_host_operation(&path), Some(spec.operation));
        }
        assert_eq!(
            runtime_host_operation(&[
                "std".into(),
                "io".into(),
                "file".into(),
                "file".into(),
                "unknown".into()
            ]),
            None
        );
    }

    #[test]
    fn runtime_host_operation_table_has_unique_paths() {
        let mut paths = BTreeSet::new();
        for spec in RUNTIME_HOST_OPERATIONS {
            assert!(
                paths.insert(spec.path),
                "duplicate runtime host operation path {:?}",
                spec.path
            );
        }
    }

    #[test]
    fn runtime_host_operation_table_carries_act_and_sync_tier_metadata() {
        for spec in RUNTIME_HOST_OPERATIONS {
            assert_eq!(
                spec.tier,
                RuntimeHostOperationTier::Sync,
                "current host operation {:?} should stay sync until a suspend tier is explicit",
                spec.operation
            );
            assert!(
                spec.path.starts_with(spec.act.path()),
                "host operation {:?} path {:?} should live under act {:?}",
                spec.operation,
                spec.path,
                spec.act
            );
            assert_eq!(
                spec.path.last().copied(),
                Some(spec.operation_id),
                "host operation {:?} should expose its manifest operation id as the final path segment",
                spec.operation
            );
        }
    }

    #[test]
    fn runtime_host_operation_table_separates_console_and_file_acts() {
        let mut console_ops = 0;
        let mut file_ops = 0;
        for spec in RUNTIME_HOST_OPERATIONS {
            match spec.act {
                RuntimeHostAct::ConsoleOut => console_ops += 1,
                RuntimeHostAct::File => file_ops += 1,
            }
        }

        assert_eq!(console_ops, 1, "console out should have one current op");
        assert_eq!(file_ops, 8, "file act should have current file host ops");
    }

    #[test]
    fn runtime_host_operation_table_separates_contract_and_raw_surfaces() {
        let mut contract_ops = 0;
        let mut raw_compat_ops = 0;
        for spec in RUNTIME_HOST_OPERATIONS {
            match spec.surface {
                RuntimeHostOperationSurface::Contract => contract_ops += 1,
                RuntimeHostOperationSurface::RawCompatibility => raw_compat_ops += 1,
            }
        }

        assert_eq!(
            contract_ops, 7,
            "contract host ops should cover console plus file protocol and ambient ops"
        );
        assert_eq!(
            raw_compat_ops, 2,
            "only provisional range helpers should stay isolated from the contract surface"
        );
    }

    #[test]
    fn runtime_host_operation_surface_sets_are_explicit() {
        let contract_paths = RUNTIME_HOST_OPERATIONS
            .iter()
            .filter(|spec| spec.surface == RuntimeHostOperationSurface::Contract)
            .map(|spec| spec.path.join("."))
            .collect::<BTreeSet<_>>();
        let raw_compat_paths = RUNTIME_HOST_OPERATIONS
            .iter()
            .filter(|spec| spec.surface == RuntimeHostOperationSurface::RawCompatibility)
            .map(|spec| spec.path.join("."))
            .collect::<BTreeSet<_>>();

        assert_eq!(
            contract_paths,
            BTreeSet::from([
                "std.io.console.out.write".to_string(),
                "std.io.file.file.ambient_get".to_string(),
                "std.io.file.file.ambient_set".to_string(),
                "std.io.file.file.ambient_touch".to_string(),
                "std.io.file.file.load".to_string(),
                "std.io.file.file.meta".to_string(),
                "std.io.file.file.store".to_string(),
            ]),
            "only the protocol and ambient file ops should be contract surface"
        );
        assert_eq!(
            raw_compat_paths,
            BTreeSet::from([
                "std.io.file.file.read_at".to_string(),
                "std.io.file.file.write_at".to_string(),
            ]),
            "only provisional range helpers should remain isolated as raw-compat"
        );
    }

    #[test]
    fn runtime_host_operation_manifest_view_has_stable_act_op_tier_keys() {
        let entries = runtime_host_manifest_operations();
        let mut act_op_keys = BTreeSet::new();

        assert_eq!(entries.len(), RUNTIME_HOST_OPERATIONS.len());
        for entry in entries {
            assert!(
                act_op_keys.insert((entry.act_id, entry.operation_id)),
                "duplicate host manifest operation key {}.{}",
                entry.act_id,
                entry.operation_id
            );
            assert_eq!(entry.tier, "sync");
            assert!(
                matches!(entry.surface, "contract" | "raw-compat"),
                "host manifest operation {}.{} should expose a known surface",
                entry.act_id,
                entry.operation_id
            );
            assert!(
                !entry.signature.is_empty(),
                "host manifest operation {}.{} should expose a provisional signature",
                entry.act_id,
                entry.operation_id
            );
            assert!(
                entry
                    .path
                    .iter()
                    .copied()
                    .eq(entry.act_id.split('.').chain([entry.operation_id])),
                "manifest key {}.{} should reconstruct operation path {:?}",
                entry.act_id,
                entry.operation_id,
                entry.path
            );
        }
    }

    #[test]
    fn runtime_host_manifest_exposes_suspend_tiers_before_server_ops() {
        let tiers = runtime_host_manifest_tiers()
            .into_iter()
            .map(|tier| tier.id)
            .collect::<Vec<_>>();

        assert_eq!(
            tiers,
            ["sync", "suspend-one-shot", "suspend-multi-shot"],
            "host act manifest should expose the suspend tiers required by server resources"
        );
        assert!(
            RUNTIME_HOST_OPERATIONS
                .iter()
                .all(|spec| spec.tier == RuntimeHostOperationTier::Sync),
            "registered operations should stay sync until the scheduler branch table lands"
        );
    }

    #[test]
    fn runtime_host_registry_reports_unsupported_capability_before_operation() {
        let registry = RuntimeHostRegistry::new(false);
        let path = [
            "std".into(),
            "io".into(),
            "file".into(),
            "file".into(),
            "meta".into(),
        ];

        let resolution = registry.resolve(&path);
        let spec = runtime_host_operation_spec(&path).expect("file meta op should be registered");

        let Some(RuntimeHostRequestResolution::UnsupportedCapability(failure)) = resolution else {
            panic!("disabled host operation should report unsupported capability");
        };
        assert_eq!(failure, RuntimeHostCapabilityFailure { act: spec.act });
    }

    #[test]
    fn runtime_host_registry_resolves_to_operation_spec_when_enabled() {
        let registry = RuntimeHostRegistry::new(true);
        let path = [
            "std".into(),
            "io".into(),
            "file".into(),
            "file".into(),
            "meta".into(),
        ];

        let spec = runtime_host_operation_spec(&path).expect("file meta op should be registered");

        let Some(RuntimeHostRequestResolution::Operation(operation)) = registry.resolve(&path)
        else {
            panic!("enabled host operation should resolve to registered operation");
        };
        assert_eq!(operation.spec, spec);
        assert_eq!(operation.spec.operation, RuntimeHostOperation::FileMeta);
        assert_eq!(operation.spec.path_strings(), path.to_vec());
    }

    #[test]
    fn runtime_host_registry_reports_known_act_unknown_op_as_capability_failure() {
        let registry = RuntimeHostRegistry::new(true);
        let path = [
            "std".into(),
            "io".into(),
            "file".into(),
            "file".into(),
            "not_registered".into(),
        ];

        let Some(RuntimeHostRequestResolution::UnsupportedCapability(failure)) =
            registry.resolve(&path)
        else {
            panic!("known act with unknown op should report unsupported capability");
        };
        assert_eq!(
            failure,
            RuntimeHostCapabilityFailure {
                act: RuntimeHostAct::File
            }
        );
    }

    #[test]
    fn runtime_host_registry_reports_known_file_unknown_op_as_capability_failure() {
        let registry = RuntimeHostRegistry::new(true);
        let path = [
            "std".into(),
            "io".into(),
            "file".into(),
            "file".into(),
            "not_registered".into(),
        ];

        let Some(RuntimeHostRequestResolution::UnsupportedCapability(failure)) =
            registry.resolve(&path)
        else {
            panic!("known file act with unknown op should report unsupported capability");
        };
        assert_eq!(
            failure,
            RuntimeHostCapabilityFailure {
                act: RuntimeHostAct::File
            }
        );
    }

    #[test]
    fn runtime_host_registry_leaves_unknown_effects_unresolved() {
        let registry = RuntimeHostRegistry::new(false);
        let path = ["std".into(), "unknown".into(), "op".into()];

        assert!(registry.resolve(&path).is_none());
    }
}
