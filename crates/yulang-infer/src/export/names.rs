use yulang_core_ir as core_ir;

use crate::symbols::{Name, Path};

pub fn export_name(name: &Name) -> core_ir::Name {
    core_ir::Name(name.0.clone())
}

pub fn export_path(path: &Path) -> core_ir::Path {
    core_ir::Path {
        segments: path.segments.iter().map(export_name).collect(),
    }
}

pub(crate) fn path_key(path: &Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
