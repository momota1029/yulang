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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeHostOperation {
    ConsoleOutWrite,
    FileReadAt,
    FileWriteAt,
    FileOpenTextRaw,
    FileGet,
    FileSet,
    FileFlush,
    FileOpenTextSnapshotRaw,
    FileSnapshotGet,
    FileSnapshotSet,
    FileSnapshotCommit,
    FileMetaRaw,
    FileExists,
    FileIsFile,
    FileIsDir,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostOperationSpec {
    pub(super) act: RuntimeHostAct,
    operation_id: &'static str,
    tier: RuntimeHostOperationTier,
    path: &'static [&'static str],
    pub(super) operation: RuntimeHostOperation,
}

impl RuntimeHostOperationSpec {
    pub(super) fn path_strings(self) -> Vec<String> {
        self.path.iter().map(|part| (*part).to_string()).collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostRegistry {
    native_host_operations_enabled: bool,
}

impl RuntimeHostRegistry {
    pub(super) fn new(native_host_operations_enabled: bool) -> Self {
        Self {
            native_host_operations_enabled,
        }
    }

    pub(super) fn resolve(&self, path: &[String]) -> Option<RuntimeHostRequestResolution> {
        let Some(spec) = runtime_host_operation_spec(path) else {
            return self.resolve_known_act_without_registered_operation(path);
        };
        if !self.native_host_operations_enabled {
            return Some(RuntimeHostRequestResolution::UnsupportedCapability(
                RuntimeHostCapabilityFailure { act: spec.act },
            ));
        }
        Some(RuntimeHostRequestResolution::Operation(spec))
    }

    fn resolve_known_act_without_registered_operation(
        &self,
        path: &[String],
    ) -> Option<RuntimeHostRequestResolution> {
        let act = runtime_host_act_for_path(path)?;
        Some(RuntimeHostRequestResolution::UnsupportedCapability(
            RuntimeHostCapabilityFailure { act },
        ))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeHostRequestResolution {
    Operation(&'static RuntimeHostOperationSpec),
    UnsupportedCapability(RuntimeHostCapabilityFailure),
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

const RUNTIME_HOST_OPERATIONS: &[RuntimeHostOperationSpec] = &[
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::ConsoleOut,
        operation_id: "write",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "console", "out", "write"],
        operation: RuntimeHostOperation::ConsoleOutWrite,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "read_at",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "read_at"],
        operation: RuntimeHostOperation::FileReadAt,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "write_at",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "write_at"],
        operation: RuntimeHostOperation::FileWriteAt,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "open_text_raw",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "open_text_raw"],
        operation: RuntimeHostOperation::FileOpenTextRaw,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_get",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "file_get"],
        operation: RuntimeHostOperation::FileGet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_set",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "file_set"],
        operation: RuntimeHostOperation::FileSet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_flush",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "file_flush"],
        operation: RuntimeHostOperation::FileFlush,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "open_text_snapshot_raw",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "open_text_snapshot_raw"],
        operation: RuntimeHostOperation::FileOpenTextSnapshotRaw,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_snapshot_get",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "file_snapshot_get"],
        operation: RuntimeHostOperation::FileSnapshotGet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_snapshot_set",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "file_snapshot_set"],
        operation: RuntimeHostOperation::FileSnapshotSet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_snapshot_commit",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "file_snapshot_commit"],
        operation: RuntimeHostOperation::FileSnapshotCommit,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "meta_raw",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "meta_raw"],
        operation: RuntimeHostOperation::FileMetaRaw,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "exists",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "exists"],
        operation: RuntimeHostOperation::FileExists,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "is_file",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "is_file"],
        operation: RuntimeHostOperation::FileIsFile,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "is_dir",
        tier: RuntimeHostOperationTier::Sync,
        path: &["std", "io", "file", "file", "is_dir"],
        operation: RuntimeHostOperation::FileIsDir,
    },
];

const RUNTIME_HOST_ACTS: &[RuntimeHostAct] = &[RuntimeHostAct::ConsoleOut, RuntimeHostAct::File];

pub(super) fn runtime_host_operation_spec(
    path: &[String],
) -> Option<&'static RuntimeHostOperationSpec> {
    RUNTIME_HOST_OPERATIONS
        .iter()
        .find(|spec| runtime_host_path_matches(path, spec.path))
        .inspect(|spec| {
            debug_assert_eq!(spec.tier, RuntimeHostOperationTier::Sync);
            debug_assert!(spec.path.starts_with(spec.act.path()));
            debug_assert_eq!(spec.path.last().copied(), Some(spec.operation_id));
        })
}

fn runtime_host_act_for_path(path: &[String]) -> Option<RuntimeHostAct> {
    RUNTIME_HOST_ACTS
        .iter()
        .copied()
        .find(|act| runtime_host_path_starts_with(path, act.path()))
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct RuntimeHostOperationManifestEntry {
    act_id: &'static str,
    operation_id: &'static str,
    tier: &'static str,
    path: &'static [&'static str],
}

#[cfg(test)]
fn runtime_host_operation_manifest_entries() -> Vec<RuntimeHostOperationManifestEntry> {
    RUNTIME_HOST_OPERATIONS
        .iter()
        .map(|spec| RuntimeHostOperationManifestEntry {
            act_id: spec.act.manifest_id(),
            operation_id: spec.operation_id,
            tier: spec.tier.manifest_id(),
            path: spec.path,
        })
        .collect()
}

#[cfg(test)]
impl RuntimeHostAct {
    fn manifest_id(self) -> &'static str {
        match self {
            Self::ConsoleOut => "std.io.console.out",
            Self::File => "std.io.file.file",
        }
    }
}

#[cfg(test)]
impl RuntimeHostOperationTier {
    fn manifest_id(self) -> &'static str {
        match self {
            Self::Sync => "sync",
        }
    }
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
        assert_eq!(file_ops, 14, "file act should have current file host ops");
    }

    #[test]
    fn runtime_host_operation_manifest_view_has_stable_act_op_tier_keys() {
        let entries = runtime_host_operation_manifest_entries();
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
    fn runtime_host_registry_reports_unsupported_capability_before_operation() {
        let registry = RuntimeHostRegistry::new(false);
        let path = [
            "std".into(),
            "io".into(),
            "file".into(),
            "file".into(),
            "exists".into(),
        ];

        let resolution = registry.resolve(&path);
        let spec = runtime_host_operation_spec(&path).expect("file exists op should be registered");

        assert_eq!(
            resolution,
            Some(RuntimeHostRequestResolution::UnsupportedCapability(
                RuntimeHostCapabilityFailure { act: spec.act }
            ))
        );
    }

    #[test]
    fn runtime_host_registry_resolves_to_operation_spec_when_enabled() {
        let registry = RuntimeHostRegistry::new(true);
        let path = [
            "std".into(),
            "io".into(),
            "file".into(),
            "file".into(),
            "exists".into(),
        ];

        let spec = runtime_host_operation_spec(&path).expect("file exists op should be registered");

        assert_eq!(
            registry.resolve(&path),
            Some(RuntimeHostRequestResolution::Operation(spec))
        );
        assert_eq!(spec.operation, RuntimeHostOperation::FileExists);
        assert_eq!(spec.path_strings(), path.to_vec());
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

        assert_eq!(
            registry.resolve(&path),
            Some(RuntimeHostRequestResolution::UnsupportedCapability(
                RuntimeHostCapabilityFailure {
                    act: RuntimeHostAct::File
                }
            ))
        );
    }

    #[test]
    fn runtime_host_registry_leaves_unknown_effects_unresolved() {
        let registry = RuntimeHostRegistry::new(false);
        let path = ["std".into(), "unknown".into(), "op".into()];

        assert_eq!(registry.resolve(&path), None);
    }
}
