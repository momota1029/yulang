use std::env;
use std::path::{Path, PathBuf};

pub const YULANG_MANIFEST_FILE: &str = "realm.toml";
pub const YULANG_LOCK_FILE: &str = "yulang.lock";
pub const YULANG_TARGET_DIR: &str = "target/yulang";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YulangCachePaths {
    pub project_target_root: PathBuf,
    pub project_bin: PathBuf,
    pub project_obj: PathBuf,
    pub project_build: PathBuf,
    pub project_dump: PathBuf,
    pub user_cache_root: PathBuf,
    pub realm_store: PathBuf,
    pub compiled_units: PathBuf,
    pub native: PathBuf,
}

impl YulangCachePaths {
    pub fn for_project(project_root: impl AsRef<Path>) -> Self {
        Self::with_user_cache_root(project_root, default_user_cache_root())
    }

    pub fn with_user_cache_root(
        project_root: impl AsRef<Path>,
        user_cache_root: impl Into<PathBuf>,
    ) -> Self {
        let project_target_root = project_target_root(project_root);
        let user_cache_root = user_cache_root.into();
        Self {
            project_bin: project_target_root.join("bin"),
            project_obj: project_target_root.join("obj"),
            project_build: project_target_root.join("build"),
            project_dump: project_target_root.join("dump"),
            realm_store: user_cache_root.join("realms"),
            compiled_units: user_cache_root.join("compiled-units"),
            native: user_cache_root.join("native"),
            project_target_root,
            user_cache_root,
        }
    }

    pub fn native_for_target(&self, target: impl AsRef<str>) -> PathBuf {
        self.native.join(target.as_ref())
    }

    pub fn project_dump_dir(&self, kind: impl AsRef<str>) -> PathBuf {
        self.project_dump.join(kind.as_ref())
    }

    pub fn manifest_path(&self, project_root: impl AsRef<Path>) -> PathBuf {
        project_root.as_ref().join(YULANG_MANIFEST_FILE)
    }

    pub fn lock_path(&self, project_root: impl AsRef<Path>) -> PathBuf {
        project_root.as_ref().join(YULANG_LOCK_FILE)
    }
}

pub fn project_target_root(project_root: impl AsRef<Path>) -> PathBuf {
    project_root.as_ref().join(YULANG_TARGET_DIR)
}

pub fn default_user_cache_root() -> PathBuf {
    if let Some(path) = non_empty_env_path("YULANG_CACHE_DIR") {
        return path;
    }
    if let Some(path) = non_empty_env_path("XDG_CACHE_HOME") {
        return path.join("yulang");
    }
    if let Some(path) = non_empty_env_path("HOME") {
        return path.join(".cache").join("yulang");
    }
    env::temp_dir().join("yulang-cache")
}

fn non_empty_env_path(key: &str) -> Option<PathBuf> {
    let value = env::var_os(key)?;
    if value.is_empty() {
        return None;
    }
    Some(PathBuf::from(value))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn project_target_root_is_under_target_yulang() {
        assert_eq!(
            project_target_root("/workspace/app"),
            PathBuf::from("/workspace/app/target/yulang")
        );
    }

    #[test]
    fn cache_paths_split_project_and_user_cache_roots() {
        let paths =
            YulangCachePaths::with_user_cache_root("/workspace/app", "/home/me/.cache/yulang");

        assert_eq!(
            paths.project_target_root,
            PathBuf::from("/workspace/app/target/yulang")
        );
        assert_eq!(
            paths.project_bin,
            PathBuf::from("/workspace/app/target/yulang/bin")
        );
        assert_eq!(
            paths.project_obj,
            PathBuf::from("/workspace/app/target/yulang/obj")
        );
        assert_eq!(
            paths.project_build,
            PathBuf::from("/workspace/app/target/yulang/build")
        );
        assert_eq!(
            paths.project_dump,
            PathBuf::from("/workspace/app/target/yulang/dump")
        );
        assert_eq!(
            paths.user_cache_root,
            PathBuf::from("/home/me/.cache/yulang")
        );
        assert_eq!(
            paths.realm_store,
            PathBuf::from("/home/me/.cache/yulang/realms")
        );
        assert_eq!(
            paths.compiled_units,
            PathBuf::from("/home/me/.cache/yulang/compiled-units")
        );
        assert_eq!(paths.native, PathBuf::from("/home/me/.cache/yulang/native"));
    }

    #[test]
    fn cache_paths_have_dump_kind_and_native_target_helpers() {
        let paths =
            YulangCachePaths::with_user_cache_root("/workspace/app", "/home/me/.cache/yulang");

        assert_eq!(
            paths.project_dump_dir("abi-ir"),
            PathBuf::from("/workspace/app/target/yulang/dump/abi-ir")
        );
        assert_eq!(
            paths.native_for_target("x86_64-unknown-linux-gnu"),
            PathBuf::from("/home/me/.cache/yulang/native/x86_64-unknown-linux-gnu")
        );
    }

    #[test]
    fn manifest_and_lock_live_at_project_root() {
        let paths =
            YulangCachePaths::with_user_cache_root("/workspace/app", "/home/me/.cache/yulang");

        assert_eq!(
            paths.manifest_path("/workspace/app"),
            PathBuf::from("/workspace/app/realm.toml")
        );
        assert_eq!(
            paths.lock_path("/workspace/app"),
            PathBuf::from("/workspace/app/yulang.lock")
        );
    }
}
