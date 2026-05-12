use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

pub const YULANG_STDLIB_VERSION: &str = "0.1.0";
pub const YULANG_STD_ENV: &str = "YULANG_STD";
pub const YULANG_LIB_DIR_ENV: &str = "YULANG_LIB_DIR";

pub fn resolve_or_install_std_root(
    explicit: Option<PathBuf>,
    base_dir: Option<&Path>,
) -> io::Result<Option<PathBuf>> {
    if let Some(root) = explicit.filter(|root| is_std_root(root)) {
        return Ok(Some(root));
    }

    if let Some(root) = env_path(YULANG_STD_ENV).filter(|root| is_std_root(root)) {
        return Ok(Some(root));
    }

    if let Some(root) = base_dir.and_then(find_std_root_near) {
        return Ok(Some(root));
    }

    let root = default_versioned_std_root();
    install_embedded_std(&root)?;
    Ok(is_std_root(&root).then_some(root))
}

pub fn default_user_lib_root() -> PathBuf {
    if let Some(path) = env_path(YULANG_LIB_DIR_ENV) {
        return path;
    }
    if let Some(home) = env_path("HOME") {
        return home.join(".yulang").join("lib");
    }
    env::temp_dir().join("yulang").join("lib")
}

pub fn default_versioned_std_root() -> PathBuf {
    default_user_lib_root()
        .join(format!("yulang-{YULANG_STDLIB_VERSION}"))
        .join("std")
}

pub fn find_std_root_near(base_dir: &Path) -> Option<PathBuf> {
    for ancestor in base_dir.ancestors() {
        let candidate = ancestor.join("lib/std");
        if is_std_root(&candidate) {
            return Some(candidate);
        }
    }
    None
}

pub fn is_std_root(path: impl AsRef<Path>) -> bool {
    path.as_ref().join("prelude.yu").is_file()
}

pub fn install_embedded_std(root: impl AsRef<Path>) -> io::Result<()> {
    let root = root.as_ref();
    fs::create_dir_all(root)?;
    for file in EMBEDDED_STD_FILES {
        let path = root.join(file.name);
        if fs::read_to_string(&path).ok().as_deref() == Some(file.source) {
            continue;
        }
        fs::write(path, file.source)?;
    }
    Ok(())
}

fn env_path(key: &str) -> Option<PathBuf> {
    let value = env::var_os(key)?;
    if value.is_empty() {
        return None;
    }
    Some(PathBuf::from(value))
}

struct EmbeddedStdFile {
    name: &'static str,
    source: &'static str,
}

const EMBEDDED_STD_FILES: &[EmbeddedStdFile] = &[
    EmbeddedStdFile {
        name: "console.yu",
        source: include_str!("../std/console.yu"),
    },
    EmbeddedStdFile {
        name: "error.yu",
        source: include_str!("../std/error.yu"),
    },
    EmbeddedStdFile {
        name: "flow.yu",
        source: include_str!("../std/flow.yu"),
    },
    EmbeddedStdFile {
        name: "fold.yu",
        source: include_str!("../std/fold.yu"),
    },
    EmbeddedStdFile {
        name: "fs.yu",
        source: include_str!("../std/fs.yu"),
    },
    EmbeddedStdFile {
        name: "index.yu",
        source: include_str!("../std/index.yu"),
    },
    EmbeddedStdFile {
        name: "junction.yu",
        source: include_str!("../std/junction.yu"),
    },
    EmbeddedStdFile {
        name: "list.yu",
        source: include_str!("../std/list.yu"),
    },
    EmbeddedStdFile {
        name: "ops.yu",
        source: include_str!("../std/ops.yu"),
    },
    EmbeddedStdFile {
        name: "opt.yu",
        source: include_str!("../std/opt.yu"),
    },
    EmbeddedStdFile {
        name: "prelude.yu",
        source: include_str!("../std/prelude.yu"),
    },
    EmbeddedStdFile {
        name: "range.yu",
        source: include_str!("../std/range.yu"),
    },
    EmbeddedStdFile {
        name: "result.yu",
        source: include_str!("../std/result.yu"),
    },
    EmbeddedStdFile {
        name: "str.yu",
        source: include_str!("../std/str.yu"),
    },
    EmbeddedStdFile {
        name: "undet.yu",
        source: include_str!("../std/undet.yu"),
    },
    EmbeddedStdFile {
        name: "var.yu",
        source: include_str!("../std/var.yu"),
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn installs_embedded_std_under_versioned_root() {
        let root = env::temp_dir().join(format!(
            "yulang-stdlib-test-{}",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let std = root.join("lib").join("yulang-0.1.0").join("std");
        install_embedded_std(&std).unwrap();

        assert!(is_std_root(&std));
        assert!(std.join("list.yu").is_file());

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn embedded_ops_uses_left_associative_arithmetic_bindings() {
        let ops = embedded_std_source("ops.yu");

        assert!(ops.contains("pub prefix (-) 8.0.0 = \\x -> std::int::sub 0 x"));
        assert!(ops.contains("pub infix (-) 5.0.0 5.0.1"));
        assert!(ops.contains("pub infix (/) 6.0.0 6.0.1"));
    }

    #[test]
    fn embedded_str_len_is_a_dot_member_not_recursive_wrapper() {
        let str_source = embedded_std_source("str.yu");

        assert!(str_source.contains("our s.len = std::str::len s"));
        assert!(!str_source.contains("pub len(s: str): int = std::str::len s"));
    }

    fn embedded_std_source(name: &str) -> &'static str {
        EMBEDDED_STD_FILES
            .iter()
            .find(|file| file.name == name)
            .map(|file| file.source)
            .unwrap()
    }
}
