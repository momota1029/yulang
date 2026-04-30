use yulang_core_ir as core_ir;

use crate::lower::LowerState;
use crate::lower::builtin_types::{builtin_runtime_type_path, builtin_source_type_path};
use crate::symbols::{ModuleId, Name, Path};

pub(super) fn ensure_child_module(
    state: &mut LowerState,
    parent: ModuleId,
    name: &str,
) -> ModuleId {
    let name = Name(name.to_string());
    if let Some(&child) = state.ctx.modules.node(parent).modules.get(&name) {
        child
    } else {
        let child = state.ctx.modules.new_module();
        state.ctx.modules.insert_module(parent, name, child);
        child
    }
}

pub(super) fn ensure_builtin_type(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
) -> crate::ids::DefId {
    let name = Name(name.to_string());
    if let Some(&def) = state.ctx.modules.node(module).types.get(&name) {
        return def;
    }
    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_type(module, name, def);
    def
}

pub(super) fn named_path(name: &str) -> Path {
    builtin_source_type_path(name)
}

pub(super) fn named_runtime_path(name: &str) -> core_ir::Path {
    builtin_runtime_type_path(name)
}
