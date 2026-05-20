use std::path::PathBuf;

use serde::{Deserialize, Serialize};

use crate::{BandPath, RealmIdentity, ResolvedRealmId};

pub const YULANG_LOCK_FORMAT_VERSION: u32 = 1;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct YulangLockFile {
    pub format_version: u32,
    pub realms: Vec<LockedRealm>,
    pub dependencies: Vec<LockedRealmDependency>,
    pub with_constraints: Vec<LockedWithConstraint>,
}

impl YulangLockFile {
    pub fn new() -> Self {
        Self {
            format_version: YULANG_LOCK_FORMAT_VERSION,
            realms: Vec::new(),
            dependencies: Vec::new(),
            with_constraints: Vec::new(),
        }
    }
}

impl Default for YulangLockFile {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LockedRealm {
    pub id: ResolvedRealmId,
    pub source: LockedRealmSource,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum LockedRealmSource {
    Local(PathBuf),
    Cached(PathBuf),
    Embedded(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LockedRealmDependency {
    pub from: ResolvedRealmId,
    pub to: ResolvedRealmId,
    pub requirement: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LockedWithConstraint {
    pub requester: ResolvedRealmId,
    pub target: RealmIdentity,
    pub anchor: BandPath,
    pub resolved: ResolvedRealmId,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RealmVersion;

    #[test]
    fn lock_file_round_trips_through_json() {
        let program = ResolvedRealmId {
            identity: RealmIdentity("user/program".to_string()),
            version: Some(RealmVersion("0.1.0".to_string())),
        };
        let ui = ResolvedRealmId {
            identity: RealmIdentity("ui/widget".to_string()),
            version: Some(RealmVersion("2.4.0".to_string())),
        };
        let lock = YulangLockFile {
            format_version: YULANG_LOCK_FORMAT_VERSION,
            realms: vec![
                LockedRealm {
                    id: program.clone(),
                    source: LockedRealmSource::Local(PathBuf::from("/workspace/program")),
                },
                LockedRealm {
                    id: ui.clone(),
                    source: LockedRealmSource::Cached(PathBuf::from(
                        "/home/me/.cache/yulang/realms/ui/widget/2.4.0",
                    )),
                },
            ],
            dependencies: vec![LockedRealmDependency {
                from: program.clone(),
                to: ui.clone(),
                requirement: "^2.4".to_string(),
            }],
            with_constraints: vec![LockedWithConstraint {
                requester: program,
                target: RealmIdentity("ui/widget".to_string()),
                anchor: BandPath::from_segments(vec![yulang_typed_ir::Name("ui".to_string())]),
                resolved: ui,
            }],
        };

        let json = serde_json::to_string_pretty(&lock).expect("lock file should serialize");
        let decoded: YulangLockFile =
            serde_json::from_str(&json).expect("lock file should deserialize");

        assert_eq!(decoded, lock);
    }
}
