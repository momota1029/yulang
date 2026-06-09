use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

pub const YULANG_STDLIB_VERSION: &str = "0.1.4";
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
    default_user_lib_root().join(format!("yulang-{YULANG_STDLIB_VERSION}"))
}

pub fn find_std_root_near(base_dir: &Path) -> Option<PathBuf> {
    for ancestor in base_dir.ancestors() {
        let candidate = ancestor.join("lib");
        if is_std_root(&candidate) {
            return Some(candidate);
        }
    }
    None
}

pub fn is_std_root(path: impl AsRef<Path>) -> bool {
    path.as_ref().join("std.yu").is_file()
}

pub fn install_embedded_std(root: impl AsRef<Path>) -> io::Result<()> {
    let root = root.as_ref();
    fs::create_dir_all(root)?;
    for file in EMBEDDED_STD_FILES {
        let path = root.join(file.name);
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
        name: "std.yu",
        source: include_str!("../std.yu"),
    },
    EmbeddedStdFile {
        name: "std/control.yu",
        source: include_str!("../std/control.yu"),
    },
    EmbeddedStdFile {
        name: "std/control/flow.yu",
        source: include_str!("../std/control/flow.yu"),
    },
    EmbeddedStdFile {
        name: "std/control/junction.yu",
        source: include_str!("../std/control/junction.yu"),
    },
    EmbeddedStdFile {
        name: "std/control/throw.yu",
        source: include_str!("../std/control/throw.yu"),
    },
    EmbeddedStdFile {
        name: "std/control/nondet.yu",
        source: include_str!("../std/control/nondet.yu"),
    },
    EmbeddedStdFile {
        name: "std/control/var.yu",
        source: include_str!("../std/control/var.yu"),
    },
    EmbeddedStdFile {
        name: "std/core.yu",
        source: include_str!("../std/core.yu"),
    },
    EmbeddedStdFile {
        name: "std/core/cmp.yu",
        source: include_str!("../std/core/cmp.yu"),
    },
    EmbeddedStdFile {
        name: "std/core/convert.yu",
        source: include_str!("../std/core/convert.yu"),
    },
    EmbeddedStdFile {
        name: "std/core/fmt.yu",
        source: include_str!("../std/core/fmt.yu"),
    },
    EmbeddedStdFile {
        name: "std/core/ops.yu",
        source: include_str!("../std/core/ops.yu"),
    },
    EmbeddedStdFile {
        name: "std/core/seq.yu",
        source: include_str!("../std/core/seq.yu"),
    },
    EmbeddedStdFile {
        name: "std/data.yu",
        source: include_str!("../std/data.yu"),
    },
    EmbeddedStdFile {
        name: "std/data/fold.yu",
        source: include_str!("../std/data/fold.yu"),
    },
    EmbeddedStdFile {
        name: "std/data/index.yu",
        source: include_str!("../std/data/index.yu"),
    },
    EmbeddedStdFile {
        name: "std/data/list.yu",
        source: include_str!("../std/data/list.yu"),
    },
    EmbeddedStdFile {
        name: "std/data/opt.yu",
        source: include_str!("../std/data/opt.yu"),
    },
    EmbeddedStdFile {
        name: "std/data/range.yu",
        source: include_str!("../std/data/range.yu"),
    },
    EmbeddedStdFile {
        name: "std/data/result.yu",
        source: include_str!("../std/data/result.yu"),
    },
    EmbeddedStdFile {
        name: "std/io.yu",
        source: include_str!("../std/io.yu"),
    },
    EmbeddedStdFile {
        name: "std/io/console.yu",
        source: include_str!("../std/io/console.yu"),
    },
    EmbeddedStdFile {
        name: "std/io/file.yu",
        source: include_str!("../std/io/file.yu"),
    },
    EmbeddedStdFile {
        name: "std/num.yu",
        source: include_str!("../std/num.yu"),
    },
    EmbeddedStdFile {
        name: "std/num/frac.yu",
        source: include_str!("../std/num/frac.yu"),
    },
    EmbeddedStdFile {
        name: "std/prelude.yu",
        source: include_str!("../std/prelude.yu"),
    },
    EmbeddedStdFile {
        name: "std/text.yu",
        source: include_str!("../std/text.yu"),
    },
    EmbeddedStdFile {
        name: "std/text/bytes.yu",
        source: include_str!("../std/text/bytes.yu"),
    },
    EmbeddedStdFile {
        name: "std/text/char.yu",
        source: include_str!("../std/text/char.yu"),
    },
    EmbeddedStdFile {
        name: "std/text/parse.yu",
        source: include_str!("../std/text/parse.yu"),
    },
    EmbeddedStdFile {
        name: "std/text/path.yu",
        source: include_str!("../std/text/path.yu"),
    },
    EmbeddedStdFile {
        name: "std/text/str.yu",
        source: include_str!("../std/text/str.yu"),
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
        let std_root = root
            .join("lib")
            .join(format!("yulang-{YULANG_STDLIB_VERSION}"));
        install_embedded_std(&std_root).unwrap();

        assert!(is_std_root(&std_root));
        assert!(std_root.join("std.yu").is_file());
        assert!(std_root.join("std/data/list.yu").is_file());

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn embedded_ops_uses_left_associative_arithmetic_bindings() {
        let ops = embedded_std_source("std/core/ops.yu");

        assert!(ops.contains("pub prefix (-) 8.0.0 = \\x -> std::int::sub 0 x"));
        assert!(ops.contains("pub infix (-) 5.0.0 5.0.1"));
        assert!(ops.contains("pub infix (/) 6.0.0 6.0.1"));
        assert!(ops.contains("pub prefix(fail) 1.0.0 = \\e -> e.throw"));
    }

    #[test]
    fn embedded_str_len_is_a_dot_member_not_recursive_wrapper() {
        let str_source = embedded_std_source("std/text/str.yu");

        assert!(str_source.contains("our s.len = std::text::str::len s"));
        assert!(!str_source.contains("pub len(s: str): int = std::str::len s"));
    }

    #[test]
    fn embedded_list_exposes_common_companion_methods() {
        let list_source = embedded_std_source("std/data/list.yu");

        assert!(list_source.contains("our xs.map f = std::data::list::map xs f"));
        assert!(list_source.contains("our xs.filter pred = std::data::list::filter xs pred"));
        assert!(list_source.contains("our xs.first = std::data::list::first xs"));
        assert!(list_source.contains("our xs.rev = std::data::list::rev xs"));
        assert!(list_source.contains("our xs.sort = std::data::list::sort xs"));
    }

    #[test]
    fn embedded_result_exposes_common_companion_methods() {
        let result_source = embedded_std_source("std/data/result.yu");

        assert!(result_source.contains("our r.map f = std::data::result::map r f"));
        assert!(result_source.contains("our r.and_then f = std::data::result::and_then r f"));
        assert!(
            result_source
                .contains("our r.unwrap_or fallback = std::data::result::unwrap_or r fallback")
        );
    }

    #[test]
    fn embedded_io_groups_output_and_file_helpers() {
        let io_source = embedded_std_source("std/io.yu");
        let file_source = embedded_std_source("std/io/file.yu");

        assert!(io_source.contains("pub mod console;"));
        assert!(io_source.contains("pub mod file;"));
        assert!(file_source.contains("pub act file:"));
        assert!(file_source.contains("pub error io_err:"));
        assert!(file_source.contains("pub open(path: path): ref '[file] str = open_text path"));
    }

    #[test]
    fn embedded_control_uses_nondet_name() {
        let control_source = embedded_std_source("std/control.yu");
        let nondet_source = embedded_std_source("std/control/nondet.yu");

        assert!(control_source.contains("pub mod nondet;"));
        assert!(nondet_source.contains("pub act nondet:"));
        assert!(
            !EMBEDDED_STD_FILES
                .iter()
                .any(|file| file.name == "std/control/undet.yu")
        );
    }

    fn embedded_std_source(name: &str) -> &'static str {
        EMBEDDED_STD_FILES
            .iter()
            .find(|file| file.name == name)
            .map(|file| file.source)
            .unwrap()
    }
}
