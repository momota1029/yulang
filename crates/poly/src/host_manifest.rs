//! Compiler-produced host act manifest.
//!
//! This is the shared schema for host operations. The compiler owns the list of
//! host acts and operations; runtimes only bind implementations to this surface.

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostActManifest {
    pub acts: Vec<HostActManifestAct>,
    pub operations: Vec<HostActManifestOperation>,
    pub hash: HostManifestHash,
}

impl HostActManifest {
    pub fn new(
        acts: Vec<HostActManifestAct>,
        operations: Vec<HostActManifestOperationInput>,
    ) -> Result<Self, HostManifestError> {
        let acts = normalized_acts(acts)?;
        let act_paths = acts
            .iter()
            .map(|act| (act.act_id.clone(), act.path.clone()))
            .collect::<BTreeMap<_, _>>();

        let mut operation_keys = BTreeSet::<(String, String)>::new();
        let mut operation_paths = BTreeSet::<Vec<String>>::new();
        let mut normalized_ops = Vec::with_capacity(operations.len());

        for op in operations {
            let Some(act_path) = act_paths.get(&op.act_id) else {
                return Err(HostManifestError::UnknownAct {
                    act_id: op.act_id,
                    operation_id: op.operation_id,
                });
            };
            if !op.path.starts_with(act_path) {
                return Err(HostManifestError::OperationPathOutsideAct {
                    act_id: op.act_id,
                    operation_id: op.operation_id,
                    act_path: act_path.clone(),
                    operation_path: op.path,
                });
            }
            let key = (op.act_id.clone(), op.operation_id.clone());
            if !operation_keys.insert(key.clone()) {
                return Err(HostManifestError::DuplicateOperation {
                    act_id: key.0,
                    operation_id: key.1,
                });
            }
            if !operation_paths.insert(op.path.clone()) {
                return Err(HostManifestError::DuplicateOperationPath { path: op.path });
            }
            normalized_ops.push(op);
        }

        normalized_ops.sort_by(|left, right| {
            (&left.act_id, &left.operation_id).cmp(&(&right.act_id, &right.operation_id))
        });

        let operations = normalized_ops
            .into_iter()
            .enumerate()
            .map(|(column, op)| HostActManifestOperation {
                symbol: mangle_host_symbol(&op.act_id, &op.operation_id),
                act_id: op.act_id,
                operation_id: op.operation_id,
                path: op.path,
                tier: op.tier,
                surface: op.surface,
                signature: op.signature,
                column: column as u32,
            })
            .collect::<Vec<_>>();

        let hash = hash_manifest(&acts, &operations);
        Ok(Self {
            acts,
            operations,
            hash,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostActManifestAct {
    pub act_id: String,
    pub path: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostActManifestOperation {
    pub act_id: String,
    pub operation_id: String,
    pub path: Vec<String>,
    pub tier: HostOperationTier,
    pub surface: HostOperationSurface,
    pub signature: String,
    pub column: u32,
    pub symbol: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostActManifestOperationInput {
    pub act_id: String,
    pub operation_id: String,
    pub path: Vec<String>,
    pub tier: HostOperationTier,
    pub surface: HostOperationSurface,
    pub signature: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum HostOperationTier {
    Sync,
    SuspendOneShot,
    SuspendMultiShot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum HostOperationSurface {
    Contract,
    RawCompat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostManifestHash(pub u64);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostManifestError {
    DuplicateAct {
        act_id: String,
    },
    DuplicateOperation {
        act_id: String,
        operation_id: String,
    },
    DuplicateOperationPath {
        path: Vec<String>,
    },
    UnknownAct {
        act_id: String,
        operation_id: String,
    },
    OperationPathOutsideAct {
        act_id: String,
        operation_id: String,
        act_path: Vec<String>,
        operation_path: Vec<String>,
    },
}

pub fn mangle_host_symbol(act_id: &str, operation_id: &str) -> String {
    let mut out = String::from("yu_host_");
    for segment in act_id.split('.') {
        out.push_str(&segment.len().to_string());
        out.push_str(segment);
    }
    out.push('_');
    out.push_str(&operation_id.len().to_string());
    out.push_str(operation_id);
    out
}

fn normalized_acts(
    mut acts: Vec<HostActManifestAct>,
) -> Result<Vec<HostActManifestAct>, HostManifestError> {
    let mut ids = BTreeSet::new();
    for act in &acts {
        if !ids.insert(act.act_id.clone()) {
            return Err(HostManifestError::DuplicateAct {
                act_id: act.act_id.clone(),
            });
        }
    }
    acts.sort_by(|left, right| left.act_id.cmp(&right.act_id));
    Ok(acts)
}

fn hash_manifest(
    acts: &[HostActManifestAct],
    operations: &[HostActManifestOperation],
) -> HostManifestHash {
    let mut hasher = HostManifestHasher::new();
    hasher.string("yulang.host-manifest.v0");
    hasher.usize(acts.len());
    for act in acts {
        hasher.string(&act.act_id);
        hasher.path(&act.path);
    }
    hasher.usize(operations.len());
    for op in operations {
        hasher.string(&op.act_id);
        hasher.string(&op.operation_id);
        hasher.path(&op.path);
        hasher.u8(match op.tier {
            HostOperationTier::Sync => 0,
            HostOperationTier::SuspendOneShot => 1,
            HostOperationTier::SuspendMultiShot => 2,
        });
        hasher.u8(match op.surface {
            HostOperationSurface::Contract => 0,
            HostOperationSurface::RawCompat => 1,
        });
        hasher.string(&op.signature);
        hasher.u32(op.column);
        hasher.string(&op.symbol);
    }
    HostManifestHash(hasher.finish())
}

struct HostManifestHasher {
    state: u64,
}

impl HostManifestHasher {
    fn new() -> Self {
        Self {
            state: 0xcbf29ce484222325,
        }
    }

    fn finish(self) -> u64 {
        self.state
    }

    fn bytes(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.state ^= u64::from(*byte);
            self.state = self.state.wrapping_mul(0x100000001b3);
        }
    }

    fn u8(&mut self, value: u8) {
        self.bytes(&[value]);
    }

    fn u32(&mut self, value: u32) {
        self.bytes(&value.to_le_bytes());
    }

    fn usize(&mut self, value: usize) {
        self.bytes(&(value as u64).to_le_bytes());
    }

    fn string(&mut self, value: &str) {
        self.usize(value.len());
        self.bytes(value.as_bytes());
    }

    fn path(&mut self, path: &[String]) {
        self.usize(path.len());
        for segment in path {
            self.string(segment);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn manifest_sorts_columns_and_hash_independent_of_input_order() {
        let left = sample_manifest(vec![
            op(
                "std.io.console.out",
                "write",
                HostOperationSurface::Contract,
            ),
            op(
                "std.io.file.file",
                "read_at",
                HostOperationSurface::RawCompat,
            ),
            op("std.io.file.file", "load", HostOperationSurface::Contract),
        ]);
        let right = sample_manifest(vec![
            op("std.io.file.file", "load", HostOperationSurface::Contract),
            op(
                "std.io.console.out",
                "write",
                HostOperationSurface::Contract,
            ),
            op(
                "std.io.file.file",
                "read_at",
                HostOperationSurface::RawCompat,
            ),
        ]);

        assert_eq!(left.hash, right.hash);
        assert_eq!(
            left.operations
                .iter()
                .map(|op| (op.column, op.act_id.as_str(), op.operation_id.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (0, "std.io.console.out", "write"),
                (1, "std.io.file.file", "load"),
                (2, "std.io.file.file", "read_at"),
            ]
        );
    }

    #[test]
    fn mangles_host_symbols_with_length_prefixes() {
        assert_eq!(
            mangle_host_symbol("std.io.file.file", "load"),
            "yu_host_3std2io4file4file_4load"
        );
        assert_eq!(
            mangle_host_symbol("std.io.my_file.file", "read_at"),
            "yu_host_3std2io7my_file4file_7read_at"
        );
    }

    #[test]
    fn mangled_host_symbols_distinguish_ambiguous_segments() {
        let samples = [
            ("a.bc", "d"),
            ("ab.c", "d"),
            ("a.b_c", "d"),
            ("a_b.c", "d"),
            ("a.b", "c_d"),
            ("a.b_c", "d1"),
        ];

        let mut seen = std::collections::BTreeSet::new();
        for (act_id, operation_id) in samples {
            let symbol = mangle_host_symbol(act_id, operation_id);
            assert!(
                seen.insert(symbol.clone()),
                "duplicate symbol {symbol} for {act_id}.{operation_id}"
            );
        }
        assert_eq!(seen.len(), samples.len());
    }

    #[test]
    fn rejects_duplicate_operation_keys() {
        let err = HostActManifest::new(
            sample_acts(),
            vec![
                op("std.io.file.file", "load", HostOperationSurface::Contract),
                op("std.io.file.file", "load", HostOperationSurface::Contract),
            ],
        )
        .unwrap_err();
        assert_eq!(
            err,
            HostManifestError::DuplicateOperation {
                act_id: "std.io.file.file".to_string(),
                operation_id: "load".to_string()
            }
        );
    }

    #[test]
    fn rejects_operation_paths_outside_act_path() {
        let mut input = op("std.io.file.file", "load", HostOperationSurface::Contract);
        input.path = vec!["std".into(), "io".into(), "other".into(), "load".into()];
        let err = HostActManifest::new(sample_acts(), vec![input]).unwrap_err();
        assert!(matches!(
            err,
            HostManifestError::OperationPathOutsideAct { .. }
        ));
    }

    fn sample_manifest(operations: Vec<HostActManifestOperationInput>) -> HostActManifest {
        HostActManifest::new(sample_acts(), operations).unwrap()
    }

    fn sample_acts() -> Vec<HostActManifestAct> {
        vec![
            HostActManifestAct {
                act_id: "std.io.file.file".to_string(),
                path: vec!["std".into(), "io".into(), "file".into(), "file".into()],
            },
            HostActManifestAct {
                act_id: "std.io.console.out".to_string(),
                path: vec!["std".into(), "io".into(), "console".into(), "out".into()],
            },
        ]
    }

    fn op(
        act_id: &str,
        operation_id: &str,
        surface: HostOperationSurface,
    ) -> HostActManifestOperationInput {
        let mut path = act_id.split('.').map(str::to_string).collect::<Vec<_>>();
        path.push(operation_id.to_string());
        HostActManifestOperationInput {
            act_id: act_id.to_string(),
            operation_id: operation_id.to_string(),
            path,
            tier: HostOperationTier::Sync,
            surface,
            signature: "placeholder".to_string(),
        }
    }
}
