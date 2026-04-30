use crate::ids::DefId;
use crate::solve::ExtensionMethodInfo;
use crate::symbols::{ModuleId, Name, Visibility};

use super::Infer;

pub(crate) fn resolve_extension_method_def(infer: &Infer, name: &Name) -> Option<DefId> {
    let [info] = infer.extension_methods.get(name)?.as_slice() else {
        return None;
    };
    Some(info.def)
}

pub(super) fn resolve_extension_method_info_from(
    infer: &Infer,
    module: ModuleId,
    name: &Name,
) -> Option<ExtensionMethodInfo> {
    let candidates = infer
        .extension_methods
        .get(name)?
        .iter()
        .filter(|info| extension_method_is_accessible_from(module, info))
        .cloned()
        .collect::<Vec<_>>();
    let [info] = candidates.as_slice() else {
        return None;
    };
    Some(info.clone())
}

fn extension_method_is_accessible_from(module: ModuleId, info: &ExtensionMethodInfo) -> bool {
    match info.visibility {
        Visibility::My => module == info.module,
        Visibility::Our | Visibility::Pub => true,
    }
}
