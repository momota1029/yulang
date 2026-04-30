use yulang_core_ir as core_ir;

use crate::symbols::{Name, Path};

pub(crate) fn builtin_source_type_path(name: &str) -> Path {
    builtin_std_type_path(name).unwrap_or_else(|| Path {
        segments: vec![Name(name.to_string())],
    })
}

pub(crate) fn builtin_runtime_type_path(name: &str) -> core_ir::Path {
    builtin_std_type_path(name)
        .map(runtime_path)
        .unwrap_or_else(|| core_ir::Path::from_name(core_ir::Name(name.to_string())))
}

pub(crate) fn canonical_builtin_type_path(path: &Path) -> Option<Path> {
    let [name] = path.segments.as_slice() else {
        return None;
    };
    builtin_std_type_path(&name.0)
}

fn builtin_std_type_path(name: &str) -> Option<Path> {
    let (module, type_name) = match name {
        "list" => ("list", "list"),
        "str" | "string" => ("str", "str"),
        "range" => ("range", "range"),
        _ => return None,
    };
    Some(Path {
        segments: vec![
            Name("std".to_string()),
            Name(module.to_string()),
            Name(type_name.to_string()),
        ],
    })
}

fn runtime_path(path: Path) -> core_ir::Path {
    core_ir::Path {
        segments: path
            .segments
            .into_iter()
            .map(|segment| core_ir::Name(segment.0))
            .collect(),
    }
}
