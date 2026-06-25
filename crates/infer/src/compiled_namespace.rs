use std::collections::HashMap;

use poly::expr::Vis;
use serde::{Deserialize, Serialize};

use crate::{LoadedFilesError, ModuleId, ModuleTable, ModuleTypeKind, TypeDeclId};
use poly::expr::DefId;

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceSurface {
    pub modules: Vec<CompiledNamespaceModule>,
    pub values: Vec<CompiledNamespaceSymbol>,
    pub types: Vec<CompiledNamespaceTypeSymbol>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceModule {
    pub id: u32,
    pub path: Vec<String>,
    pub visibility: Option<CompiledNamespaceVisibility>,
    pub values: Vec<CompiledNamespaceModuleValue>,
    pub types: Vec<CompiledNamespaceModuleType>,
    pub modules: Vec<CompiledNamespaceModuleChild>,
    pub imported_values: Vec<CompiledNamespaceImportedValue>,
    pub imported_types: Vec<CompiledNamespaceImportedType>,
    pub imported_modules: Vec<CompiledNamespaceImportedModule>,
    pub aliases: Vec<CompiledNamespaceAlias>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceSymbol {
    pub unit_id: u32,
    pub path: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceTypeSymbol {
    pub unit_id: u32,
    pub path: Vec<String>,
    pub kind: CompiledNamespaceTypeKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceModuleValue {
    pub name: String,
    pub symbol: u32,
    pub visibility: CompiledNamespaceVisibility,
    pub order: u32,
    pub lazy: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceModuleType {
    pub name: String,
    pub symbol: u32,
    pub visibility: CompiledNamespaceVisibility,
    pub order: u32,
    pub kind: CompiledNamespaceTypeKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceModuleChild {
    pub name: String,
    pub module: u32,
    pub module_path: Vec<String>,
    pub visibility: CompiledNamespaceVisibility,
    pub order: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceImportedValue {
    pub name: String,
    pub symbol: u32,
    pub visibility: CompiledNamespaceVisibility,
    pub order: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceImportedType {
    pub name: String,
    pub symbol: u32,
    pub visibility: CompiledNamespaceVisibility,
    pub order: u32,
    pub kind: CompiledNamespaceTypeKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceImportedModule {
    pub name: String,
    pub module: u32,
    pub module_path: Vec<String>,
    pub visibility: CompiledNamespaceVisibility,
    pub order: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceAlias {
    pub visibility: CompiledNamespaceVisibility,
    pub order: u32,
    pub import: sources::UseImport,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompiledNamespaceVisibility {
    Pub,
    Our,
    My,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompiledNamespaceTypeKind {
    TypeAlias,
    Struct,
    Enum,
    Error,
    Role,
    Act,
}

impl CompiledNamespaceSurface {
    pub fn from_loaded_files(loaded: &[sources::LoadedFile]) -> Result<Self, LoadedFilesError> {
        let lower = crate::lower_loaded_files_module_map(loaded)?;
        Ok(Self::from_module_table(&lower.modules))
    }

    pub fn from_module_table(modules: &ModuleTable) -> Self {
        let mut builder = NamespaceSurfaceBuilder::new(modules);
        builder.visit_module(modules.root_id(), None);
        builder.fill_import_views();
        builder.finish()
    }
}

struct NamespaceSurfaceBuilder<'a> {
    modules: &'a ModuleTable,
    module_ids: HashMap<ModuleId, u32>,
    value_symbols: HashMap<DefId, u32>,
    type_symbols: HashMap<TypeDeclId, u32>,
    surface: CompiledNamespaceSurface,
}

impl<'a> NamespaceSurfaceBuilder<'a> {
    fn new(modules: &'a ModuleTable) -> Self {
        Self {
            modules,
            module_ids: HashMap::new(),
            value_symbols: HashMap::new(),
            type_symbols: HashMap::new(),
            surface: CompiledNamespaceSurface::default(),
        }
    }

    fn finish(self) -> CompiledNamespaceSurface {
        self.surface
    }

    fn visit_module(
        &mut self,
        module: ModuleId,
        visibility: Option<CompiledNamespaceVisibility>,
    ) -> u32 {
        if let Some(id) = self.module_ids.get(&module) {
            return *id;
        }

        let id = self.surface.modules.len() as u32;
        self.module_ids.insert(module, id);
        self.surface.modules.push(CompiledNamespaceModule {
            id,
            path: namespace_path(&self.modules.module_path(module)),
            visibility,
            values: Vec::new(),
            types: Vec::new(),
            modules: Vec::new(),
            imported_values: Vec::new(),
            imported_types: Vec::new(),
            imported_modules: Vec::new(),
            aliases: Vec::new(),
        });

        let values = self.module_value_entries(module);
        let types = self.module_type_entries(module);
        let modules = self.module_child_entries(module);
        let aliases = self.module_alias_entries(module);

        let slot = &mut self.surface.modules[id as usize];
        slot.values = values;
        slot.types = types;
        slot.modules = modules;
        slot.aliases = aliases;
        id
    }

    fn fill_import_views(&mut self) {
        let modules = self.module_ids.keys().copied().collect::<Vec<ModuleId>>();
        for module in modules {
            let id = self.module_ids[&module] as usize;
            self.surface.modules[id].imported_values = self.module_imported_value_entries(module);
            self.surface.modules[id].imported_types = self.module_imported_type_entries(module);
            self.surface.modules[id].imported_modules = self.module_imported_module_entries(module);
        }
    }

    fn module_value_entries(&mut self, module: ModuleId) -> Vec<CompiledNamespaceModuleValue> {
        self.modules
            .module_value_decls(module)
            .into_iter()
            .map(|decl| {
                let symbol = self.surface.values.len() as u32;
                let mut path = namespace_path(&self.modules.module_path(module));
                path.push(decl.name.0.clone());
                self.value_symbols.insert(decl.def, symbol);
                self.surface.values.push(CompiledNamespaceSymbol {
                    unit_id: symbol,
                    path,
                });
                CompiledNamespaceModuleValue {
                    name: decl.name.0,
                    symbol,
                    visibility: compiled_visibility(decl.vis),
                    order: decl.order.index(),
                    lazy: self.modules.is_lazy_op(decl.def),
                }
            })
            .collect()
    }

    fn module_type_entries(&mut self, module: ModuleId) -> Vec<CompiledNamespaceModuleType> {
        self.modules
            .module_type_decls(module)
            .into_iter()
            .map(|decl| {
                let kind = compiled_type_kind(decl.kind);
                let symbol = self.surface.types.len() as u32;
                let mut path = namespace_path(&self.modules.module_path(module));
                path.push(decl.name.0.clone());
                self.type_symbols.insert(decl.id, symbol);
                self.surface.types.push(CompiledNamespaceTypeSymbol {
                    unit_id: symbol,
                    path,
                    kind,
                });
                CompiledNamespaceModuleType {
                    name: decl.name.0,
                    symbol,
                    visibility: compiled_visibility(decl.vis),
                    order: decl.order.index(),
                    kind,
                }
            })
            .collect()
    }

    fn module_imported_value_entries(
        &self,
        module: ModuleId,
    ) -> Vec<CompiledNamespaceImportedValue> {
        let mut entries = self
            .modules
            .module_imported_value_decls(module)
            .into_iter()
            .filter_map(|decl| {
                let symbol = *self.value_symbols.get(&decl.def)?;
                Some(CompiledNamespaceImportedValue {
                    name: decl.name.0,
                    symbol,
                    visibility: compiled_visibility(decl.vis),
                    order: decl.order.index(),
                })
            })
            .collect::<Vec<_>>();
        entries.sort_by(|left, right| {
            (left.order, &left.name, left.symbol).cmp(&(right.order, &right.name, right.symbol))
        });
        entries
    }

    fn module_imported_type_entries(&self, module: ModuleId) -> Vec<CompiledNamespaceImportedType> {
        let mut entries = self
            .modules
            .module_imported_type_decls(module)
            .into_iter()
            .filter_map(|decl| {
                let symbol = *self.type_symbols.get(&decl.decl.id)?;
                let kind = compiled_type_kind(decl.decl.kind);
                Some(CompiledNamespaceImportedType {
                    name: decl.name.0,
                    symbol,
                    visibility: compiled_visibility(decl.vis),
                    order: decl.order.index(),
                    kind,
                })
            })
            .collect::<Vec<_>>();
        entries.sort_by(|left, right| {
            (left.order, &left.name, left.symbol).cmp(&(right.order, &right.name, right.symbol))
        });
        entries
    }

    fn module_imported_module_entries(
        &self,
        module: ModuleId,
    ) -> Vec<CompiledNamespaceImportedModule> {
        let mut entries = self
            .modules
            .module_imported_module_decls(module)
            .into_iter()
            .filter_map(|decl| {
                let module_id = *self.module_ids.get(&decl.module)?;
                Some(CompiledNamespaceImportedModule {
                    name: decl.name.0,
                    module: module_id,
                    module_path: namespace_path(&self.modules.module_path(decl.module)),
                    visibility: compiled_visibility(decl.vis),
                    order: decl.order.index(),
                })
            })
            .collect::<Vec<_>>();
        entries.sort_by(|left, right| {
            (left.order, &left.name, left.module).cmp(&(right.order, &right.name, right.module))
        });
        entries
    }

    fn module_child_entries(&mut self, module: ModuleId) -> Vec<CompiledNamespaceModuleChild> {
        self.modules
            .module_child_decls(module)
            .into_iter()
            .map(|decl| {
                let visibility = compiled_visibility(decl.vis);
                let child = self.visit_module(decl.module, Some(visibility));
                CompiledNamespaceModuleChild {
                    name: decl.name.0,
                    module: child,
                    module_path: namespace_path(&self.modules.module_path(decl.module)),
                    visibility,
                    order: decl.order.index(),
                }
            })
            .collect()
    }

    fn module_alias_entries(&self, module: ModuleId) -> Vec<CompiledNamespaceAlias> {
        self.modules
            .aliases(module)
            .iter()
            .map(|alias| CompiledNamespaceAlias {
                visibility: compiled_visibility(alias.vis),
                order: alias.order.index(),
                import: alias.import.clone(),
            })
            .collect()
    }
}

pub fn namespace_path(path: &sources::Path) -> Vec<String> {
    path.segments
        .iter()
        .map(|segment| segment.0.clone())
        .collect()
}

fn compiled_visibility(visibility: Vis) -> CompiledNamespaceVisibility {
    match visibility {
        Vis::Pub => CompiledNamespaceVisibility::Pub,
        Vis::Our => CompiledNamespaceVisibility::Our,
        Vis::My => CompiledNamespaceVisibility::My,
    }
}

fn compiled_type_kind(kind: ModuleTypeKind) -> CompiledNamespaceTypeKind {
    match kind {
        ModuleTypeKind::TypeAlias => CompiledNamespaceTypeKind::TypeAlias,
        ModuleTypeKind::Struct => CompiledNamespaceTypeKind::Struct,
        ModuleTypeKind::Enum => CompiledNamespaceTypeKind::Enum,
        ModuleTypeKind::Error => CompiledNamespaceTypeKind::Error,
        ModuleTypeKind::Role => CompiledNamespaceTypeKind::Role,
        ModuleTypeKind::Act => CompiledNamespaceTypeKind::Act,
    }
}

#[cfg(test)]
mod tests {
    use sources::{Name, Path, SourceFile};

    use super::*;

    #[test]
    fn namespace_surface_records_resolved_import_view() {
        let loaded = sources::load(vec![
            source(&[], "mod ops;\npub use ops::*\n"),
            source(&["ops"], "pub x = 42\n"),
        ]);
        let surface = CompiledNamespaceSurface::from_loaded_files(&loaded).unwrap();
        let root = surface
            .modules
            .iter()
            .find(|module| module.path.is_empty())
            .unwrap();
        let ops_path = vec!["ops".to_string()];
        let ops = surface
            .modules
            .iter()
            .find(|module| module.path == ops_path)
            .unwrap();
        let x = ops.values.iter().find(|value| value.name == "x").unwrap();

        assert!(root.imported_values.iter().any(|value| {
            value.name == "x"
                && value.symbol == x.symbol
                && value.visibility == CompiledNamespaceVisibility::Pub
        }));
    }

    fn source(module: &[&str], text: &str) -> SourceFile {
        SourceFile {
            module_path: Path {
                segments: module
                    .iter()
                    .map(|segment| Name((*segment).to_string()))
                    .collect(),
            },
            source: text.to_string(),
        }
    }
}
