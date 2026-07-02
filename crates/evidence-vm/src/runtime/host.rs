#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeHostAct {
    ConsoleOut,
    File,
    FileBuffer,
}

impl RuntimeHostAct {
    pub(super) fn path(self) -> &'static [&'static str] {
        match self {
            Self::ConsoleOut => &["std", "io", "console", "out"],
            Self::File => &["std", "io", "file", "file"],
            Self::FileBuffer => &["std", "io", "file", "file_buffer"],
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
    FileLoad,
    FileStore,
    FileMeta,
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
    FileExists,
    FileIsFile,
    FileIsDir,
    FileBufferAmbientGet,
    FileBufferAmbientSet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostOperationSpec {
    pub(super) act: RuntimeHostAct,
    operation_id: &'static str,
    tier: RuntimeHostOperationTier,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostRegistry {
    manifest: RuntimeHostManifest,
    native_host_operations_enabled: bool,
}

impl RuntimeHostRegistry {
    pub(super) fn new(native_host_operations_enabled: bool) -> Self {
        Self {
            manifest: RUNTIME_HOST_MANIFEST,
            native_host_operations_enabled,
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
        Some(RuntimeHostRequestResolution::Operation(spec))
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

pub(crate) fn runtime_host_manifest_has_known_act(path: &[String]) -> bool {
    RUNTIME_HOST_MANIFEST.act_for_path(path).is_some()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct RuntimeHostManifestOperation {
    pub act_id: &'static str,
    pub operation_id: &'static str,
    pub tier: &'static str,
    pub signature: &'static str,
    pub path: &'static [&'static str],
}

pub fn runtime_host_manifest_operations() -> Vec<RuntimeHostManifestOperation> {
    RUNTIME_HOST_OPERATIONS
        .iter()
        .map(|spec| RuntimeHostManifestOperation {
            act_id: spec.act.manifest_id(),
            operation_id: spec.operation_id,
            tier: spec.tier.manifest_id(),
            signature: spec.signature,
            path: spec.path,
        })
        .collect()
}

impl RuntimeHostAct {
    fn manifest_id(self) -> &'static str {
        match self {
            Self::ConsoleOut => "std.io.console.out",
            Self::File => "std.io.file.file",
            Self::FileBuffer => "std.io.file.file_buffer",
        }
    }
}

impl RuntimeHostOperationTier {
    fn manifest_id(self) -> &'static str {
        match self {
            Self::Sync => "sync",
        }
    }
}

const RUNTIME_HOST_OPERATIONS: &[RuntimeHostOperationSpec] = &[
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::ConsoleOut,
        operation_id: "write",
        tier: RuntimeHostOperationTier::Sync,
        signature: "str -> ()",
        path: &["std", "io", "console", "out", "write"],
        operation: RuntimeHostOperation::ConsoleOutWrite,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "load",
        tier: RuntimeHostOperationTier::Sync,
        signature: "path -> result str io_err",
        path: &["std", "io", "file", "file", "load"],
        operation: RuntimeHostOperation::FileLoad,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "store",
        tier: RuntimeHostOperationTier::Sync,
        signature: "(path, str) -> result unit io_err",
        path: &["std", "io", "file", "file", "store"],
        operation: RuntimeHostOperation::FileStore,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "meta",
        tier: RuntimeHostOperationTier::Sync,
        signature: "path -> file_meta",
        path: &["std", "io", "file", "file", "meta"],
        operation: RuntimeHostOperation::FileMeta,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "read_at",
        tier: RuntimeHostOperationTier::Sync,
        signature: "(path, range) -> result (str, range) io_err",
        path: &["std", "io", "file", "file", "read_at"],
        operation: RuntimeHostOperation::FileReadAt,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "write_at",
        tier: RuntimeHostOperationTier::Sync,
        signature: "(path, range, str) -> result unit io_err",
        path: &["std", "io", "file", "file", "write_at"],
        operation: RuntimeHostOperation::FileWriteAt,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "open_text_raw",
        tier: RuntimeHostOperationTier::Sync,
        signature: "path -> (int, file_handle)",
        path: &["std", "io", "file", "file", "open_text_raw"],
        operation: RuntimeHostOperation::FileOpenTextRaw,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_get",
        tier: RuntimeHostOperationTier::Sync,
        signature: "file_handle -> str",
        path: &["std", "io", "file", "file", "file_get"],
        operation: RuntimeHostOperation::FileGet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_set",
        tier: RuntimeHostOperationTier::Sync,
        signature: "(file_handle, str) -> ()",
        path: &["std", "io", "file", "file", "file_set"],
        operation: RuntimeHostOperation::FileSet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_flush",
        tier: RuntimeHostOperationTier::Sync,
        signature: "file_handle -> int",
        path: &["std", "io", "file", "file", "file_flush"],
        operation: RuntimeHostOperation::FileFlush,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "open_text_snapshot_raw",
        tier: RuntimeHostOperationTier::Sync,
        signature: "path -> (int, file_handle)",
        path: &["std", "io", "file", "file", "open_text_snapshot_raw"],
        operation: RuntimeHostOperation::FileOpenTextSnapshotRaw,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_snapshot_get",
        tier: RuntimeHostOperationTier::Sync,
        signature: "file_handle -> str",
        path: &["std", "io", "file", "file", "file_snapshot_get"],
        operation: RuntimeHostOperation::FileSnapshotGet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_snapshot_set",
        tier: RuntimeHostOperationTier::Sync,
        signature: "(file_handle, str) -> ()",
        path: &["std", "io", "file", "file", "file_snapshot_set"],
        operation: RuntimeHostOperation::FileSnapshotSet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "file_snapshot_commit",
        tier: RuntimeHostOperationTier::Sync,
        signature: "file_handle -> int",
        path: &["std", "io", "file", "file", "file_snapshot_commit"],
        operation: RuntimeHostOperation::FileSnapshotCommit,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "exists",
        tier: RuntimeHostOperationTier::Sync,
        signature: "path -> bool",
        path: &["std", "io", "file", "file", "exists"],
        operation: RuntimeHostOperation::FileExists,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "is_file",
        tier: RuntimeHostOperationTier::Sync,
        signature: "path -> bool",
        path: &["std", "io", "file", "file", "is_file"],
        operation: RuntimeHostOperation::FileIsFile,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::File,
        operation_id: "is_dir",
        tier: RuntimeHostOperationTier::Sync,
        signature: "path -> bool",
        path: &["std", "io", "file", "file", "is_dir"],
        operation: RuntimeHostOperation::FileIsDir,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::FileBuffer,
        operation_id: "ambient_get",
        tier: RuntimeHostOperationTier::Sync,
        signature: "path -> str",
        path: &["std", "io", "file", "file_buffer", "ambient_get"],
        operation: RuntimeHostOperation::FileBufferAmbientGet,
    },
    RuntimeHostOperationSpec {
        act: RuntimeHostAct::FileBuffer,
        operation_id: "ambient_set",
        tier: RuntimeHostOperationTier::Sync,
        signature: "(path, str) -> unit",
        path: &["std", "io", "file", "file_buffer", "ambient_set"],
        operation: RuntimeHostOperation::FileBufferAmbientSet,
    },
];

const RUNTIME_HOST_ACTS: &[RuntimeHostAct] = &[
    RuntimeHostAct::ConsoleOut,
    RuntimeHostAct::File,
    RuntimeHostAct::FileBuffer,
];

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
        let mut file_buffer_ops = 0;
        for spec in RUNTIME_HOST_OPERATIONS {
            match spec.act {
                RuntimeHostAct::ConsoleOut => console_ops += 1,
                RuntimeHostAct::File => file_ops += 1,
                RuntimeHostAct::FileBuffer => file_buffer_ops += 1,
            }
        }

        assert_eq!(console_ops, 1, "console out should have one current op");
        assert_eq!(file_ops, 16, "file act should have current file host ops");
        assert_eq!(
            file_buffer_ops, 2,
            "file buffer act should have current ambient host ops"
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
    fn runtime_host_registry_reports_known_file_buffer_unknown_op_as_capability_failure() {
        let registry = RuntimeHostRegistry::new(true);
        let path = [
            "std".into(),
            "io".into(),
            "file".into(),
            "file_buffer".into(),
            "not_registered".into(),
        ];

        assert_eq!(
            registry.resolve(&path),
            Some(RuntimeHostRequestResolution::UnsupportedCapability(
                RuntimeHostCapabilityFailure {
                    act: RuntimeHostAct::FileBuffer
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
