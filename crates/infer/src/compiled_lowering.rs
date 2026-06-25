use serde::{Deserialize, Serialize};
use sources::{Name, Path};

use crate::{
    CompiledNamespaceSurface, CompiledNamespaceTypeKind, ModuleTable, ModuleTypeKind,
    namespace_path,
};

/// Lowering-time metadata exported by a compiled unit.
///
/// Namespace and typed surfaces are enough for name lookup and imported value
/// schemes. Some downstream lowering rules also need declaration metadata that
/// is not part of the final poly arena. This surface keeps that information
/// structured so cached dependencies do not have to expose source CST just to
/// recover it.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringSurface {
    pub act_type_vars: Vec<CompiledLoweringActTypeVars>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringActTypeVars {
    pub type_symbol: u32,
    pub type_path: Vec<String>,
    pub vars: Vec<String>,
}

impl CompiledLoweringSurface {
    pub fn from_module_table(modules: &ModuleTable, namespace: &CompiledNamespaceSurface) -> Self {
        let mut act_type_vars = namespace
            .types
            .iter()
            .filter(|ty| ty.kind == CompiledNamespaceTypeKind::Act)
            .filter_map(|ty| {
                let decl = type_decl_for_namespace_path(modules, &ty.path)?;
                if decl.kind != ModuleTypeKind::Act {
                    return None;
                }
                let vars = modules.act_type_vars(decl.id)?.to_vec();
                Some(CompiledLoweringActTypeVars {
                    type_symbol: ty.unit_id,
                    type_path: ty.path.clone(),
                    vars,
                })
            })
            .collect::<Vec<_>>();
        act_type_vars.sort_by_key(|entry| entry.type_symbol);
        Self { act_type_vars }
    }
}

fn type_decl_for_namespace_path(
    modules: &ModuleTable,
    path: &[String],
) -> Option<crate::ModuleTypeDecl> {
    let (name, module_path) = path.split_last()?;
    let module = modules.module_by_path(&Path {
        segments: module_path.iter().cloned().map(Name).collect(),
    })?;
    modules
        .type_decls(module, &Name(name.clone()))
        .into_iter()
        .find(|decl| namespace_path(&modules.type_decl_path(decl)) == path)
}
