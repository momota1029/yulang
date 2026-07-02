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

pub(super) struct RuntimeHostOperationSpec {
    pub(super) act: RuntimeHostAct,
    operation_id: &'static str,
    tier: RuntimeHostOperationTier,
    path: &'static [&'static str],
    pub(super) operation: RuntimeHostOperation,
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

#[cfg(test)]
fn runtime_host_operation(path: &[String]) -> Option<RuntimeHostOperation> {
    runtime_host_operation_spec(path).map(|spec| spec.operation)
}

fn runtime_host_path_matches(path: &[String], expected: &[&str]) -> bool {
    path.iter().map(String::as_str).eq(expected.iter().copied())
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
}
