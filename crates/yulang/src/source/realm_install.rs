use super::*;
use crate::stdlib::default_user_lib_root;

const LOCAL_REALM_PROVIDER: &str = "local";
const INSTALLED_REALMS_DIR: &str = "realms";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RealmInstallOutput {
    pub source_root: PathBuf,
    pub frozen_root: PathBuf,
    pub installed_root: PathBuf,
    pub snapshot: sources::FrozenRealmSnapshot,
    pub already_installed: bool,
}

#[derive(Debug)]
pub enum RealmInstallError {
    Manifest(sources::RealmManifestError),
    Freeze(sources::FreezeRealmError),
    MissingManifest {
        root: PathBuf,
    },
    MissingLocalName {
        root: PathBuf,
    },
    MissingVersion {
        root: PathBuf,
    },
    VersionMismatch {
        manifest_version: String,
        requested_version: String,
    },
    InvalidLocalName {
        name: String,
    },
    Io {
        path: PathBuf,
        error: io::Error,
    },
    InstalledSnapshotMismatch {
        path: PathBuf,
        existing_hash: u64,
        new_hash: u64,
    },
}

impl fmt::Display for RealmInstallError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RealmInstallError::Manifest(error) => write!(f, "{error}"),
            RealmInstallError::Freeze(error) => write!(f, "{error}"),
            RealmInstallError::MissingManifest { root } => {
                write!(f, "realm manifest not found under {}", root.display())
            }
            RealmInstallError::MissingLocalName { root } => write!(
                f,
                "realm install requires [realm] name in {}",
                root.join(sources::YULANG_MANIFEST_FILE).display()
            ),
            RealmInstallError::MissingVersion { root } => write!(
                f,
                "realm install requires --version <version> or [realm] version in {}",
                root.join(sources::YULANG_MANIFEST_FILE).display()
            ),
            RealmInstallError::VersionMismatch {
                manifest_version,
                requested_version,
            } => write!(
                f,
                "realm version mismatch: manifest declares `{manifest_version}` but command requested `{requested_version}`"
            ),
            RealmInstallError::InvalidLocalName { name } => {
                write!(f, "invalid local realm name `{name}`")
            }
            RealmInstallError::Io { path, error } => {
                write!(f, "failed to access {}: {error}", path.display())
            }
            RealmInstallError::InstalledSnapshotMismatch {
                path,
                existing_hash,
                new_hash,
            } => write!(
                f,
                "installed realm {} already exists with a different hash: existing={existing_hash:016x} new={new_hash:016x}",
                path.display()
            ),
        }
    }
}

impl std::error::Error for RealmInstallError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstalledLocalRealmBand {
    pub realm: sources::ResolvedRealmId,
    pub source_path: PathBuf,
    pub module_path: Path,
    pub band_path: Path,
}

pub fn install_local_realm(
    root: impl AsRef<FsPath>,
    requested_version: Option<String>,
) -> Result<RealmInstallOutput, RealmInstallError> {
    let source_root = canonicalize_for_dedupe(root.as_ref());
    let manifest = sources::load_realm_manifest(&source_root)
        .map_err(RealmInstallError::Manifest)?
        .ok_or_else(|| RealmInstallError::MissingManifest {
            root: source_root.clone(),
        })?;
    let local_name =
        manifest
            .local_name
            .as_deref()
            .ok_or_else(|| RealmInstallError::MissingLocalName {
                root: source_root.clone(),
            })?;
    let local_name_segments = local_realm_name_segments(local_name)?;
    let version = resolve_realm_install_version(&source_root, requested_version, &manifest)?;
    let frozen = sources::freeze_realm_version(&source_root, version.0.clone())
        .map_err(RealmInstallError::Freeze)?;
    let installed_root = installed_local_realm_version_root(&local_name_segments, &version);
    let snapshot_path = installed_root.join("snapshot.json");

    if installed_root.exists() {
        let existing = sources::read_frozen_realm_snapshot(&snapshot_path)
            .map_err(RealmInstallError::Freeze)?;
        if existing.identity == frozen.snapshot.identity
            && existing.version == frozen.snapshot.version
            && existing.source_hash == frozen.snapshot.source_hash
        {
            return Ok(RealmInstallOutput {
                source_root,
                frozen_root: frozen.root,
                installed_root,
                snapshot: existing,
                already_installed: true,
            });
        }
        return Err(RealmInstallError::InstalledSnapshotMismatch {
            path: installed_root,
            existing_hash: existing.source_hash,
            new_hash: frozen.snapshot.source_hash,
        });
    }

    let temp_root = install_temp_root(&installed_root);
    if temp_root.exists() {
        fs::remove_dir_all(&temp_root).map_err(|error| RealmInstallError::Io {
            path: temp_root.clone(),
            error,
        })?;
    }
    copy_dir_recursive(&frozen.root, &temp_root)?;
    ensure_parent_dir_for_source_path(&installed_root)?;
    fs::rename(&temp_root, &installed_root).map_err(|error| RealmInstallError::Io {
        path: installed_root.clone(),
        error,
    })?;

    Ok(RealmInstallOutput {
        source_root,
        frozen_root: frozen.root,
        installed_root,
        snapshot: frozen.snapshot,
        already_installed: false,
    })
}

pub(crate) fn installed_local_import_module_path(import: &sources::UseImport) -> Option<Path> {
    let (path, route) = use_import_path_and_route(import);
    let sources::UsePathRoute::SlashQualified { prefix_segments } = route else {
        return None;
    };
    let prefix = slash_qualified_prefix(path, prefix_segments)?;
    if prefix
        .first()
        .is_none_or(|segment| segment.0 != LOCAL_REALM_PROVIDER)
    {
        return None;
    }
    Some(Path {
        segments: prefix.to_vec(),
    })
}

pub(crate) fn resolve_installed_local_realm_band(
    import: &sources::UseImport,
) -> Result<Option<InstalledLocalRealmBand>, RouteError> {
    let (path, route) = use_import_path_and_route(import);
    let sources::UsePathRoute::SlashQualified { prefix_segments } = route else {
        return Ok(None);
    };
    let Some(prefix) = slash_qualified_prefix(path, prefix_segments) else {
        return Err(RouteError::InvalidInstalledRealmImport {
            path: path.clone(),
            reason: "slash-qualified prefix is outside the import path".to_string(),
        });
    };
    if prefix
        .first()
        .is_none_or(|segment| segment.0 != LOCAL_REALM_PROVIDER)
    {
        return Ok(None);
    }
    let Some(realm_and_band) = prefix.get(1..) else {
        return Err(RouteError::InvalidInstalledRealmImport {
            path: path.clone(),
            reason: "local realm import must include a realm name and band".to_string(),
        });
    };
    if realm_and_band.len() < 2 {
        return Err(RouteError::InvalidInstalledRealmImport {
            path: path.clone(),
            reason: "local realm import must include a realm name and band".to_string(),
        });
    }
    let requested_version = use_import_version(import).map(normalize_import_realm_version);
    let Some(installed) = resolve_installed_local_realm_prefix(realm_and_band, requested_version)?
    else {
        let local_root = installed_local_realms_root();
        let candidates = local_realm_name_candidate_paths(&local_root, realm_and_band);
        return Err(RouteError::InstalledRealmNotFound {
            name: Path {
                segments: realm_and_band.to_vec(),
            },
            version: use_import_version(import).map(str::to_string),
            root: local_root,
            candidates,
        });
    };
    let band_file = resolve_realm_band_file(&installed.version_root, &installed.band_path)?;
    let module_path = Path {
        segments: prefix.to_vec(),
    };
    let name = Path {
        segments: installed.name_segments.clone(),
    };
    Ok(Some(InstalledLocalRealmBand {
        realm: sources::ResolvedRealmId {
            identity: sources::RealmIdentity(format!(
                "local/{}",
                name.segments
                    .iter()
                    .map(|segment| segment.0.as_str())
                    .collect::<Vec<_>>()
                    .join("/")
            )),
            version: Some(installed.version),
        },
        source_path: band_file,
        module_path: module_path.clone(),
        band_path: module_path,
    }))
}

fn use_import_path_and_route(import: &sources::UseImport) -> (&Path, sources::UsePathRoute) {
    match import {
        sources::UseImport::Alias { path, route, .. } => (path, *route),
        sources::UseImport::Glob { prefix, route, .. } => (prefix, *route),
    }
}

fn use_import_version(import: &sources::UseImport) -> Option<&str> {
    match import {
        sources::UseImport::Alias { version, .. } | sources::UseImport::Glob { version, .. } => {
            version.as_deref()
        }
    }
}

fn slash_qualified_prefix(path: &Path, prefix_segments: usize) -> Option<&[Name]> {
    (prefix_segments > 0 && prefix_segments <= path.segments.len())
        .then_some(&path.segments[..prefix_segments])
}

fn resolve_realm_install_version(
    root: &FsPath,
    requested_version: Option<String>,
    manifest: &sources::SourceRealmManifest,
) -> Result<sources::RealmVersion, RealmInstallError> {
    match (requested_version, manifest.declared_version.clone()) {
        (Some(requested), Some(declared)) if requested != declared.0 => {
            Err(RealmInstallError::VersionMismatch {
                manifest_version: declared.0,
                requested_version: requested,
            })
        }
        (Some(requested), _) if requested.trim().is_empty() => {
            Err(RealmInstallError::MissingVersion {
                root: root.to_path_buf(),
            })
        }
        (Some(requested), _) => Ok(sources::RealmVersion(requested)),
        (None, Some(declared)) => Ok(declared),
        (None, None) => Err(RealmInstallError::MissingVersion {
            root: root.to_path_buf(),
        }),
    }
}

fn local_realm_name_segments(name: &str) -> Result<Vec<Name>, RealmInstallError> {
    let mut segments = Vec::new();
    for segment in name.split('/') {
        if segment.is_empty()
            || segment == "."
            || segment == ".."
            || segment.contains('\\')
            || segment.contains(':')
        {
            return Err(RealmInstallError::InvalidLocalName {
                name: name.to_string(),
            });
        }
        segments.push(Name(segment.to_string()));
    }
    if segments.is_empty() {
        return Err(RealmInstallError::InvalidLocalName {
            name: name.to_string(),
        });
    }
    Ok(segments)
}

fn installed_local_realms_root() -> PathBuf {
    default_user_lib_root()
        .join(INSTALLED_REALMS_DIR)
        .join(LOCAL_REALM_PROVIDER)
}

fn installed_local_realm_version_root(
    name_segments: &[Name],
    version: &sources::RealmVersion,
) -> PathBuf {
    installed_local_realms_root()
        .join(relative_path(name_segments))
        .join(&version.0)
}

#[derive(Debug, Clone)]
struct InstalledLocalRealmPrefix {
    name_segments: Vec<Name>,
    band_path: Path,
    version: sources::RealmVersion,
    version_root: PathBuf,
}

fn resolve_installed_local_realm_prefix(
    realm_and_band: &[Name],
    requested_version: Option<String>,
) -> Result<Option<InstalledLocalRealmPrefix>, RouteError> {
    let local_root = installed_local_realms_root();
    for name_len in (1..realm_and_band.len()).rev() {
        let name_segments = &realm_and_band[..name_len];
        let band_segments = &realm_and_band[name_len..];
        let name_root = local_root.join(relative_path(name_segments));
        if !name_root.is_dir() {
            continue;
        }
        let Some((version, version_root)) =
            select_installed_local_realm_version(&name_root, requested_version.as_deref())?
        else {
            return Err(RouteError::InstalledRealmVersionNotFound {
                name: Path {
                    segments: name_segments.to_vec(),
                },
                version: requested_version.clone(),
                root: name_root,
            });
        };
        return Ok(Some(InstalledLocalRealmPrefix {
            name_segments: name_segments.to_vec(),
            band_path: Path {
                segments: band_segments.to_vec(),
            },
            version,
            version_root,
        }));
    }
    Ok(None)
}

fn select_installed_local_realm_version(
    name_root: &FsPath,
    requested_version: Option<&str>,
) -> Result<Option<(sources::RealmVersion, PathBuf)>, RouteError> {
    if let Some(requested_version) = requested_version {
        let version = normalize_import_realm_version(requested_version);
        let version_root = name_root.join(&version);
        if version_root.join("snapshot.json").is_file() {
            return Ok(Some((sources::RealmVersion(version), version_root)));
        }
        return Ok(None);
    }

    let mut versions = Vec::new();
    let entries = fs::read_dir(name_root).map_err(|error| RouteError::Io {
        path: name_root.to_path_buf(),
        error,
    })?;
    for entry in entries {
        let entry = entry.map_err(|error| RouteError::Io {
            path: name_root.to_path_buf(),
            error,
        })?;
        let path = entry.path();
        if !path.join("snapshot.json").is_file() {
            continue;
        }
        let Some(version) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        versions.push((version.to_string(), path));
    }
    versions.sort_by(|left, right| left.0.cmp(&right.0));
    Ok(versions
        .pop()
        .map(|(version, path)| (sources::RealmVersion(version), path)))
}

fn normalize_import_realm_version(version: &str) -> String {
    version
        .strip_prefix('v')
        .filter(|rest| rest.chars().next().is_some_and(|ch| ch.is_ascii_digit()))
        .unwrap_or(version)
        .to_string()
}

fn local_realm_name_candidate_paths(local_root: &FsPath, realm_and_band: &[Name]) -> Vec<PathBuf> {
    (1..realm_and_band.len())
        .rev()
        .map(|name_len| local_root.join(relative_path(&realm_and_band[..name_len])))
        .collect()
}

fn copy_dir_recursive(source: &FsPath, target: &FsPath) -> Result<(), RealmInstallError> {
    fs::create_dir_all(target).map_err(|error| RealmInstallError::Io {
        path: target.to_path_buf(),
        error,
    })?;
    for entry in fs::read_dir(source).map_err(|error| RealmInstallError::Io {
        path: source.to_path_buf(),
        error,
    })? {
        let entry = entry.map_err(|error| RealmInstallError::Io {
            path: source.to_path_buf(),
            error,
        })?;
        let source_path = entry.path();
        let target_path = target.join(entry.file_name());
        let file_type = entry.file_type().map_err(|error| RealmInstallError::Io {
            path: source_path.clone(),
            error,
        })?;
        if file_type.is_dir() {
            copy_dir_recursive(&source_path, &target_path)?;
        } else if file_type.is_file() {
            fs::copy(&source_path, &target_path)
                .map(|_| ())
                .map_err(|error| RealmInstallError::Io {
                    path: target_path,
                    error,
                })?;
        }
    }
    Ok(())
}

fn install_temp_root(path: &FsPath) -> PathBuf {
    path.with_file_name(format!(
        ".{}.install-tmp-{}",
        path.file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("realm"),
        std::process::id()
    ))
}

fn ensure_parent_dir_for_source_path(path: &FsPath) -> Result<(), RealmInstallError> {
    let Some(parent) = path.parent() else {
        return Ok(());
    };
    fs::create_dir_all(parent).map_err(|error| RealmInstallError::Io {
        path: parent.to_path_buf(),
        error,
    })
}
