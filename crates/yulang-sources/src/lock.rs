use std::path::PathBuf;
use std::{collections::HashMap, error::Error, fmt};

use serde::{Deserialize, Serialize};
use yulang_typed_ir::Path as ModulePath;

use crate::{
    BandPath, RealmIdentity, RealmVersion, ResolvedRealmId, SourceRealmRoot, SourceSet, UseImport,
    import_module_path,
};

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

    pub fn from_source_set(source_set: &SourceSet) -> Result<Self, WithConstraintConflict> {
        let realms = source_set
            .realms
            .iter()
            .map(|realm| LockedRealm {
                id: realm.id.clone(),
                source: LockedRealmSource::from_source_root(&realm.root),
            })
            .collect();
        let dependencies = source_set
            .realms
            .iter()
            .flat_map(|realm| {
                realm
                    .dependencies
                    .iter()
                    .map(|dependency| LockedRealmDependency {
                        from: realm.id.clone(),
                        to: resolved_dependency_realm(source_set, dependency),
                        requirement: dependency.requirement.clone(),
                    })
            })
            .collect();
        let with_constraints = collect_source_with_constraints(source_set)
            .into_iter()
            .map(|constraint| LockedWithConstraint {
                requester: constraint.requester,
                target: constraint.target.clone(),
                anchor: constraint.anchor,
                resolved: ResolvedRealmId {
                    identity: constraint.target,
                    version: constraint.target_version,
                },
            })
            .collect();

        let lock = Self {
            format_version: YULANG_LOCK_FORMAT_VERSION,
            realms,
            dependencies,
            with_constraints,
        };
        lock.validate_with_constraints()?;
        Ok(lock)
    }

    pub fn validate_with_constraints(&self) -> Result<(), WithConstraintConflict> {
        let mut resolved_by_key = HashMap::<WithConstraintKey, ResolvedRealmId>::new();
        for constraint in &self.with_constraints {
            let key = WithConstraintKey {
                target: constraint.target.clone(),
                anchor: constraint.anchor.clone(),
            };
            if let Some(existing) = resolved_by_key.get(&key) {
                if existing != &constraint.resolved {
                    return Err(WithConstraintConflict {
                        target: key.target,
                        anchor: key.anchor,
                        left: existing.clone(),
                        right: constraint.resolved.clone(),
                    });
                }
            } else {
                resolved_by_key.insert(key, constraint.resolved.clone());
            }
        }
        Ok(())
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
    Virtual,
}

impl LockedRealmSource {
    fn from_source_root(root: &SourceRealmRoot) -> Self {
        match root {
            SourceRealmRoot::Local(path) => Self::Local(path.clone()),
            SourceRealmRoot::Cached(path) => Self::Cached(path.clone()),
            SourceRealmRoot::Embedded(name) => Self::Embedded(name.clone()),
            SourceRealmRoot::Virtual => Self::Virtual,
        }
    }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceWithConstraint {
    pub requester: ResolvedRealmId,
    pub requester_band: BandPath,
    pub import_path: ModulePath,
    pub target: RealmIdentity,
    pub target_version: Option<RealmVersion>,
    pub anchor: BandPath,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WithConstraintConflict {
    pub target: RealmIdentity,
    pub anchor: BandPath,
    pub left: ResolvedRealmId,
    pub right: ResolvedRealmId,
}

impl fmt::Display for WithConstraintConflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "`with` constraint conflict for {} with {}: {} vs {}",
            self.target.0,
            format_band_path(&self.anchor),
            format_resolved_realm(&self.left),
            format_resolved_realm(&self.right)
        )
    }
}

impl Error for WithConstraintConflict {}

pub fn collect_source_with_constraints(source_set: &SourceSet) -> Vec<SourceWithConstraint> {
    let mut constraints = Vec::new();
    for file in &source_set.files {
        let Some(requester_band) = &file.band else {
            continue;
        };
        for use_ in &file.meta.uses {
            let Some(anchor) = use_with_anchor(&use_.import) else {
                continue;
            };
            let Some(import_path) = import_module_path(&use_.import) else {
                continue;
            };
            let Some(resolved_target) = resolved_realm_from_import_path(&import_path, source_set)
            else {
                continue;
            };
            constraints.push(SourceWithConstraint {
                requester: requester_band.realm.clone(),
                requester_band: requester_band.band.clone(),
                import_path,
                target: resolved_target.identity,
                target_version: use_realm_version(&use_.import).or(resolved_target.version),
                anchor,
            });
        }
    }
    constraints
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct WithConstraintKey {
    target: RealmIdentity,
    anchor: BandPath,
}

fn use_with_anchor(import: &UseImport) -> Option<BandPath> {
    match import {
        UseImport::Alias { with_anchor, .. } | UseImport::Glob { with_anchor, .. } => with_anchor
            .as_ref()
            .map(|path| BandPath::from_segments(path.segments.clone())),
    }
}

fn use_realm_version(import: &UseImport) -> Option<RealmVersion> {
    match import {
        UseImport::Alias { realm_version, .. } | UseImport::Glob { realm_version, .. } => {
            realm_version.clone()
        }
    }
}

fn resolved_realm_from_import_path(
    path: &ModulePath,
    source_set: &SourceSet,
) -> Option<ResolvedRealmId> {
    if path.segments.is_empty() {
        return None;
    }
    source_set
        .realms
        .iter()
        .filter_map(|realm| {
            let segments = realm_identity_segments(&realm.id.identity);
            (!segments.is_empty()
                && segments.len() < path.segments.len()
                && segments
                    .iter()
                    .zip(&path.segments)
                    .all(|(left, right)| left == &right.0))
            .then_some((segments.len(), realm.id.clone()))
        })
        .max_by_key(|(len, _)| *len)
        .map(|(_, realm)| realm)
        .or_else(|| {
            path.segments.first().map(|segment| ResolvedRealmId {
                identity: RealmIdentity(segment.0.clone()),
                version: None,
            })
        })
}

fn resolved_dependency_realm(
    source_set: &SourceSet,
    dependency: &crate::SourceRealmDependency,
) -> ResolvedRealmId {
    source_set
        .realms
        .iter()
        .find(|realm| realm.id.identity == dependency.identity)
        .map(|realm| realm.id.clone())
        .unwrap_or_else(|| ResolvedRealmId {
            identity: dependency.identity.clone(),
            version: exact_dependency_version(&dependency.requirement),
        })
}

fn exact_dependency_version(requirement: &str) -> Option<RealmVersion> {
    let requirement = requirement.trim();
    if requirement.is_empty()
        || requirement
            .chars()
            .any(|ch| matches!(ch, '^' | '~' | '*' | '<' | '>' | '=' | ',' | ' '))
    {
        return None;
    }
    Some(RealmVersion(requirement.to_string()))
}

fn realm_identity_segments(identity: &RealmIdentity) -> Vec<String> {
    identity
        .0
        .split('/')
        .filter(|segment| !segment.is_empty())
        .map(str::to_string)
        .collect()
}

fn format_band_path(path: &BandPath) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn format_resolved_realm(realm: &ResolvedRealmId) -> String {
    match &realm.version {
        Some(version) => format!("{}@{}", realm.identity.0, version.0),
        None => realm.identity.0.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        InlineSource, SourceOptions, SourceOrigin, collect_inline_source_files_with_options,
    };
    use yulang_typed_ir::Name;

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
                anchor: BandPath::from_segments(vec![Name("ui".to_string())]),
                resolved: ui,
            }],
        };

        let json = serde_json::to_string_pretty(&lock).expect("lock file should serialize");
        let decoded: YulangLockFile =
            serde_json::from_str(&json).expect("lock file should deserialize");

        assert_eq!(decoded, lock);
    }

    #[test]
    fn source_set_collects_with_constraints() {
        let source_set = collect_inline_source_files_with_options(
            "use ui/widget::a with program::ui\nx\n",
            [InlineSource {
                path: PathBuf::from("<ui/widget>.yu"),
                module_path: ModulePath {
                    segments: vec![Name("ui".to_string()), Name("widget".to_string())],
                },
                origin: SourceOrigin::User,
                source: "pub a = 1\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );

        let constraints = collect_source_with_constraints(&source_set);

        assert_eq!(constraints.len(), 1);
        assert_eq!(constraints[0].target, RealmIdentity("ui".to_string()));
        assert_eq!(
            constraints[0].anchor,
            BandPath::from_segments(vec![Name("program".to_string()), Name("ui".to_string())])
        );
    }

    #[test]
    fn source_set_collects_with_constraint_version_suffix() {
        let source_set = collect_inline_source_files_with_options(
            "use ui/widget::a v2.4 with program::ui\nx\n",
            [InlineSource {
                path: PathBuf::from("<ui/widget>.yu"),
                module_path: ModulePath {
                    segments: vec![Name("ui".to_string()), Name("widget".to_string())],
                },
                origin: SourceOrigin::User,
                source: "pub a = 1\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );

        let lock = YulangLockFile::from_source_set(&source_set).expect("lock should build");

        assert_eq!(
            lock.with_constraints[0].resolved,
            ResolvedRealmId {
                identity: RealmIdentity("ui".to_string()),
                version: Some(RealmVersion("2.4".to_string())),
            }
        );
    }

    #[test]
    fn lock_file_from_source_set_records_with_constraints() {
        let source_set = collect_inline_source_files_with_options(
            "use ui/widget::a with program::ui\nx\n",
            [InlineSource {
                path: PathBuf::from("<ui/widget>.yu"),
                module_path: ModulePath {
                    segments: vec![Name("ui".to_string()), Name("widget".to_string())],
                },
                origin: SourceOrigin::User,
                source: "pub a = 1\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );

        let lock = YulangLockFile::from_source_set(&source_set).expect("lock should build");

        assert_eq!(lock.realms.len(), 1);
        assert_eq!(lock.with_constraints.len(), 1);
        assert_eq!(
            lock.with_constraints[0].target,
            RealmIdentity("ui".to_string())
        );
        assert_eq!(
            lock.with_constraints[0].resolved,
            ResolvedRealmId {
                identity: RealmIdentity("ui".to_string()),
                version: None,
            }
        );
    }

    #[test]
    fn lock_file_rejects_conflicting_with_constraints() {
        let target = RealmIdentity("ui/widget".to_string());
        let anchor = BandPath::from_segments(vec![Name("program".to_string())]);
        let requester = ResolvedRealmId {
            identity: RealmIdentity("user/program".to_string()),
            version: None,
        };
        let left = ResolvedRealmId {
            identity: target.clone(),
            version: Some(RealmVersion("1.0.0".to_string())),
        };
        let right = ResolvedRealmId {
            identity: target.clone(),
            version: Some(RealmVersion("2.0.0".to_string())),
        };
        let lock = YulangLockFile {
            format_version: YULANG_LOCK_FORMAT_VERSION,
            realms: Vec::new(),
            dependencies: Vec::new(),
            with_constraints: vec![
                LockedWithConstraint {
                    requester: requester.clone(),
                    target: target.clone(),
                    anchor: anchor.clone(),
                    resolved: left.clone(),
                },
                LockedWithConstraint {
                    requester,
                    target: target.clone(),
                    anchor: anchor.clone(),
                    resolved: right.clone(),
                },
            ],
        };

        let err = lock.validate_with_constraints().unwrap_err();

        assert_eq!(
            err,
            WithConstraintConflict {
                target,
                anchor,
                left,
                right,
            }
        );
    }
}
