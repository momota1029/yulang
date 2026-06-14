use yulang_typed_ir as typed_ir;

use crate::symbols::{Name, Path};

pub fn export_name(name: &Name) -> typed_ir::Name {
    typed_ir::Name(name.0.clone())
}

pub fn export_path(path: &Path) -> typed_ir::Path {
    typed_ir::Path {
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
