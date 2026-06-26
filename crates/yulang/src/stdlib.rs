#[cfg(test)]
use std::cell::RefCell;
use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

pub const YULANG_STDLIB_VERSION: &str = "0.1.4";
pub const YULANG_STD_ENV: &str = "YULANG_STD";
pub const YULANG_LIB_DIR_ENV: &str = "YULANG_LIB_DIR";
pub const YULANG_CACHE_DIR_ENV: &str = "YULANG_CACHE_DIR";

pub fn install_embedded_std(root: impl AsRef<Path>) -> io::Result<()> {
    let root = root.as_ref();
    fs::create_dir_all(root)?;
    for file in embedded_std_files() {
        let path = root.join(file.relative_path);
        if fs::read_to_string(&path).ok().as_deref() == Some(file.source) {
            continue;
        }
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, file.source)?;
    }
    Ok(())
}

pub fn embedded_std_files() -> &'static [EmbeddedStdFile] {
    EMBEDDED_STD_FILES
}

pub fn default_versioned_std_root() -> PathBuf {
    default_user_lib_root().join(format!("yulang-{YULANG_STDLIB_VERSION}"))
}

pub fn installed_versioned_std_root() -> Option<PathBuf> {
    versioned_std_root_for_exe_path(&env::current_exe().ok()?)
}

pub fn default_user_lib_root() -> PathBuf {
    #[cfg(test)]
    if let Some(path) = test_user_lib_root() {
        return path;
    }
    if let Some(path) = env_path(YULANG_LIB_DIR_ENV) {
        return path;
    }
    if let Some(home) = env_path("HOME") {
        return home.join(".yulang").join("lib");
    }
    env::temp_dir().join("yulang").join("lib")
}

pub fn default_user_cache_root() -> PathBuf {
    if let Some(path) = env_path(YULANG_CACHE_DIR_ENV) {
        return path;
    }
    if let Some(path) = env_path("XDG_CACHE_HOME") {
        return path.join("yulang");
    }
    if let Some(home) = env_path("HOME") {
        return home.join(".cache").join("yulang");
    }
    env::temp_dir().join("yulang-cache")
}

pub fn env_std_root() -> Option<PathBuf> {
    env_path(YULANG_STD_ENV)
}

pub fn is_std_root(path: impl AsRef<Path>) -> bool {
    path.as_ref().join("std.yu").is_file()
}

pub fn env_path(key: &str) -> Option<PathBuf> {
    let value = env::var_os(key)?;
    if value.is_empty() {
        return None;
    }
    Some(PathBuf::from(value))
}

#[cfg(test)]
thread_local! {
    static TEST_USER_LIB_ROOT: RefCell<Option<PathBuf>> = const { RefCell::new(None) };
}

#[cfg(test)]
pub(crate) fn with_test_user_lib_root<T>(path: &Path, f: impl FnOnce() -> T) -> T {
    struct Guard {
        previous: Option<PathBuf>,
    }

    impl Drop for Guard {
        fn drop(&mut self) {
            TEST_USER_LIB_ROOT.with(|cell| {
                cell.replace(self.previous.take());
            });
        }
    }

    let previous = TEST_USER_LIB_ROOT.with(|cell| cell.replace(Some(path.to_path_buf())));
    let _guard = Guard { previous };
    f()
}

#[cfg(test)]
fn test_user_lib_root() -> Option<PathBuf> {
    TEST_USER_LIB_ROOT.with(|cell| cell.borrow().clone())
}

fn versioned_std_root_for_exe_path(exe: &Path) -> Option<PathBuf> {
    let bin_dir = exe.parent()?;
    if bin_dir.file_name()?.to_str()? != "bin" {
        return None;
    }
    Some(
        bin_dir
            .parent()?
            .join("lib")
            .join(format!("yulang-{YULANG_STDLIB_VERSION}")),
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EmbeddedStdFile {
    pub relative_path: &'static str,
    pub source: &'static str,
}

const EMBEDDED_STD_FILES: &[EmbeddedStdFile] = &[
    EmbeddedStdFile {
        relative_path: "std.yu",
        source: include_str!("../../../lib/std.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/bool.yu",
        source: include_str!("../../../lib/std/bool.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/control.yu",
        source: include_str!("../../../lib/std/control.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/control/flow.yu",
        source: include_str!("../../../lib/std/control/flow.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/control/junction.yu",
        source: include_str!("../../../lib/std/control/junction.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/control/nondet.yu",
        source: include_str!("../../../lib/std/control/nondet.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/control/throw.yu",
        source: include_str!("../../../lib/std/control/throw.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/control/var.yu",
        source: include_str!("../../../lib/std/control/var.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/core.yu",
        source: include_str!("../../../lib/std/core.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/core/cmp.yu",
        source: include_str!("../../../lib/std/core/cmp.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/core/convert.yu",
        source: include_str!("../../../lib/std/core/convert.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/core/fmt.yu",
        source: include_str!("../../../lib/std/core/fmt.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/core/ops.yu",
        source: include_str!("../../../lib/std/core/ops.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/core/seq.yu",
        source: include_str!("../../../lib/std/core/seq.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/data.yu",
        source: include_str!("../../../lib/std/data.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/data/fold.yu",
        source: include_str!("../../../lib/std/data/fold.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/data/index.yu",
        source: include_str!("../../../lib/std/data/index.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/data/list.yu",
        source: include_str!("../../../lib/std/data/list.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/data/opt.yu",
        source: include_str!("../../../lib/std/data/opt.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/data/range.yu",
        source: include_str!("../../../lib/std/data/range.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/data/result.yu",
        source: include_str!("../../../lib/std/data/result.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/float.yu",
        source: include_str!("../../../lib/std/float.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/int.yu",
        source: include_str!("../../../lib/std/int.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/io.yu",
        source: include_str!("../../../lib/std/io.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/io/console.yu",
        source: include_str!("../../../lib/std/io/console.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/io/file.yu",
        source: include_str!("../../../lib/std/io/file.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/num.yu",
        source: include_str!("../../../lib/std/num.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/num/frac.yu",
        source: include_str!("../../../lib/std/num/frac.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/prelude.yu",
        source: include_str!("../../../lib/std/prelude.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/text.yu",
        source: include_str!("../../../lib/std/text.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/text/bytes.yu",
        source: include_str!("../../../lib/std/text/bytes.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/text/char.yu",
        source: include_str!("../../../lib/std/text/char.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/text/parse.yu",
        source: include_str!("../../../lib/std/text/parse.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/text/path.yu",
        source: include_str!("../../../lib/std/text/path.yu"),
    },
    EmbeddedStdFile {
        relative_path: "std/text/str.yu",
        source: include_str!("../../../lib/std/text/str.yu"),
    },
];
