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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompiledNamespaceValueVisibility {
    Pub,
    Our,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledNamespaceMergeError {
    ConflictingValue {
        module_path: Vec<String>,
        name: String,
    },
    ConflictingType {
        module_path: Vec<String>,
        name: String,
    },
    ConflictingModule {
        module_path: Vec<String>,
        name: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledNamespaceMergeOutput {
    pub surface: CompiledNamespaceSurface,
    module_remap: HashMap<(usize, u32), u32>,
    value_remap: HashMap<(usize, u32), u32>,
    type_remap: HashMap<(usize, u32), u32>,
}

impl CompiledNamespaceMergeOutput {
    pub fn map_module(&self, prefix: usize, module: u32) -> Option<u32> {
        self.module_remap.get(&(prefix, module)).copied()
    }

    pub fn map_value(&self, prefix: usize, symbol: u32) -> Option<u32> {
        self.value_remap.get(&(prefix, symbol)).copied()
    }

    pub fn map_type(&self, prefix: usize, symbol: u32) -> Option<u32> {
        self.type_remap.get(&(prefix, symbol)).copied()
    }
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

    pub fn merge_prefixes<'a>(
        prefixes: impl IntoIterator<Item = &'a CompiledNamespaceSurface>,
    ) -> Result<Self, CompiledNamespaceMergeError> {
        Ok(Self::merge_prefixes_with_remap(prefixes)?.surface)
    }

    pub fn merge_prefixes_with_remap<'a>(
        prefixes: impl IntoIterator<Item = &'a CompiledNamespaceSurface>,
    ) -> Result<CompiledNamespaceMergeOutput, CompiledNamespaceMergeError> {
        CompiledNamespaceMergeBuilder::merge(prefixes.into_iter().collect())
    }

    pub fn value_visibility(&self, symbol: u32) -> Option<CompiledNamespaceValueVisibility> {
        for module in &self.modules {
            let Some(value) = module.values.iter().find(|value| value.symbol == symbol) else {
                continue;
            };
            return match value.visibility {
                CompiledNamespaceVisibility::Pub => Some(CompiledNamespaceValueVisibility::Pub),
                CompiledNamespaceVisibility::Our => Some(CompiledNamespaceValueVisibility::Our),
                CompiledNamespaceVisibility::My => None,
            };
        }
        None
    }
}

struct CompiledNamespaceMergeBuilder<'a> {
    prefixes: Vec<&'a CompiledNamespaceSurface>,
    merged: CompiledNamespaceSurface,
    module_by_path: HashMap<Vec<String>, u32>,
    module_remap: HashMap<(usize, u32), u32>,
    value_remap: HashMap<(usize, u32), u32>,
    type_remap: HashMap<(usize, u32), u32>,
}

impl<'a> CompiledNamespaceMergeBuilder<'a> {
    fn merge(
        prefixes: Vec<&'a CompiledNamespaceSurface>,
    ) -> Result<CompiledNamespaceMergeOutput, CompiledNamespaceMergeError> {
        let mut builder = Self {
            prefixes,
            merged: CompiledNamespaceSurface::default(),
            module_by_path: HashMap::new(),
            module_remap: HashMap::new(),
            value_remap: HashMap::new(),
            type_remap: HashMap::new(),
        };
        builder.merge_modules();
        builder.merge_symbols();
        builder.merge_module_entries()?;
        Ok(CompiledNamespaceMergeOutput {
            surface: builder.merged,
            module_remap: builder.module_remap,
            value_remap: builder.value_remap,
            type_remap: builder.type_remap,
        })
    }

    fn merge_modules(&mut self) {
        for (prefix, surface) in self.prefixes.iter().enumerate() {
            let mut modules = surface.modules.iter().collect::<Vec<_>>();
            modules.sort_by_key(|module| (module.path.len(), module.path.clone()));
            for module in modules {
                let id = self
                    .module_by_path
                    .get(&module.path)
                    .copied()
                    .unwrap_or_else(|| {
                        let id = self.merged.modules.len() as u32;
                        self.module_by_path.insert(module.path.clone(), id);
                        self.merged.modules.push(CompiledNamespaceModule {
                            id,
                            path: module.path.clone(),
                            visibility: module.visibility,
                            values: Vec::new(),
                            types: Vec::new(),
                            modules: Vec::new(),
                            imported_values: Vec::new(),
                            imported_types: Vec::new(),
                            imported_modules: Vec::new(),
                            aliases: Vec::new(),
                        });
                        id
                    });
                self.module_remap.insert((prefix, module.id), id);
            }
        }
    }

    fn merge_symbols(&mut self) {
        for (prefix, surface) in self.prefixes.iter().enumerate() {
            for value in &surface.values {
                let symbol = self.merged.values.len() as u32;
                self.value_remap.insert((prefix, value.unit_id), symbol);
                self.merged.values.push(CompiledNamespaceSymbol {
                    unit_id: symbol,
                    path: value.path.clone(),
                });
            }
            for ty in &surface.types {
                let symbol = self.merged.types.len() as u32;
                self.type_remap.insert((prefix, ty.unit_id), symbol);
                self.merged.types.push(CompiledNamespaceTypeSymbol {
                    unit_id: symbol,
                    path: ty.path.clone(),
                    kind: ty.kind,
                });
            }
        }
    }

    fn merge_module_entries(&mut self) -> Result<(), CompiledNamespaceMergeError> {
        for prefix in 0..self.prefixes.len() {
            let modules = self.prefixes[prefix].modules.clone();
            for module in &modules {
                let target = self.module_remap[&(prefix, module.id)] as usize;
                self.merge_module_values(prefix, target, module)?;
                self.merge_module_types(prefix, target, module)?;
                self.merge_module_children(prefix, target, module)?;
                self.merge_imported_values(prefix, target, module)?;
                self.merge_imported_types(prefix, target, module)?;
                self.merge_imported_modules(prefix, target, module)?;
                self.merge_aliases(target, module);
            }
        }
        Ok(())
    }

    fn merge_module_values(
        &mut self,
        prefix: usize,
        target: usize,
        module: &CompiledNamespaceModule,
    ) -> Result<(), CompiledNamespaceMergeError> {
        for value in &module.values {
            let mut value = value.clone();
            value.symbol = self.value_remap[&(prefix, value.symbol)];
            let target_module = &mut self.merged.modules[target];
            reject_duplicate_value(target_module, &value)?;
            value.order = next_namespace_order(target_module);
            target_module.values.push(value);
        }
        Ok(())
    }

    fn merge_module_types(
        &mut self,
        prefix: usize,
        target: usize,
        module: &CompiledNamespaceModule,
    ) -> Result<(), CompiledNamespaceMergeError> {
        for ty in &module.types {
            let mut ty = ty.clone();
            ty.symbol = self.type_remap[&(prefix, ty.symbol)];
            let target_module = &mut self.merged.modules[target];
            reject_duplicate_type(target_module, &ty)?;
            ty.order = next_namespace_order(target_module);
            target_module.types.push(ty);
        }
        Ok(())
    }

    fn merge_module_children(
        &mut self,
        prefix: usize,
        target: usize,
        module: &CompiledNamespaceModule,
    ) -> Result<(), CompiledNamespaceMergeError> {
        for child in &module.modules {
            let mut child = child.clone();
            child.module = self.module_remap[&(prefix, child.module)];
            let target_module = &mut self.merged.modules[target];
            if target_module
                .modules
                .iter()
                .any(|existing| existing.name == child.name && existing.module == child.module)
            {
                continue;
            }
            reject_duplicate_module(target_module, &child)?;
            child.order = next_namespace_order(target_module);
            target_module.modules.push(child);
        }
        Ok(())
    }

    fn merge_imported_values(
        &mut self,
        prefix: usize,
        target: usize,
        module: &CompiledNamespaceModule,
    ) -> Result<(), CompiledNamespaceMergeError> {
        for value in &module.imported_values {
            let mut value = value.clone();
            value.symbol = self.value_remap[&(prefix, value.symbol)];
            let target_module = &mut self.merged.modules[target];
            reject_duplicate_imported_value(target_module, &value)?;
            value.order = next_namespace_order(target_module);
            target_module.imported_values.push(value);
        }
        Ok(())
    }

    fn merge_imported_types(
        &mut self,
        prefix: usize,
        target: usize,
        module: &CompiledNamespaceModule,
    ) -> Result<(), CompiledNamespaceMergeError> {
        for ty in &module.imported_types {
            let mut ty = ty.clone();
            ty.symbol = self.type_remap[&(prefix, ty.symbol)];
            let target_module = &mut self.merged.modules[target];
            reject_duplicate_imported_type(target_module, &ty)?;
            ty.order = next_namespace_order(target_module);
            target_module.imported_types.push(ty);
        }
        Ok(())
    }

    fn merge_imported_modules(
        &mut self,
        prefix: usize,
        target: usize,
        module: &CompiledNamespaceModule,
    ) -> Result<(), CompiledNamespaceMergeError> {
        for child in &module.imported_modules {
            let mut child = child.clone();
            child.module = self.module_remap[&(prefix, child.module)];
            let target_module = &mut self.merged.modules[target];
            if target_module
                .imported_modules
                .iter()
                .any(|existing| existing.name == child.name && existing.module == child.module)
            {
                continue;
            }
            reject_duplicate_imported_module(target_module, &child)?;
            child.order = next_namespace_order(target_module);
            target_module.imported_modules.push(child);
        }
        Ok(())
    }

    fn merge_aliases(&mut self, target: usize, module: &CompiledNamespaceModule) {
        for alias in &module.aliases {
            if self.merged.modules[target].aliases.contains(alias) {
                continue;
            }
            let mut alias = alias.clone();
            alias.order = next_namespace_order(&self.merged.modules[target]);
            self.merged.modules[target].aliases.push(alias);
        }
    }
}

fn reject_duplicate_value(
    module: &CompiledNamespaceModule,
    value: &CompiledNamespaceModuleValue,
) -> Result<(), CompiledNamespaceMergeError> {
    if module
        .values
        .iter()
        .any(|existing| existing.name == value.name)
    {
        return Err(CompiledNamespaceMergeError::ConflictingValue {
            module_path: module.path.clone(),
            name: value.name.clone(),
        });
    }
    Ok(())
}

fn reject_duplicate_type(
    module: &CompiledNamespaceModule,
    ty: &CompiledNamespaceModuleType,
) -> Result<(), CompiledNamespaceMergeError> {
    if module.types.iter().any(|existing| existing.name == ty.name) {
        return Err(CompiledNamespaceMergeError::ConflictingType {
            module_path: module.path.clone(),
            name: ty.name.clone(),
        });
    }
    Ok(())
}

fn reject_duplicate_module(
    module: &CompiledNamespaceModule,
    child: &CompiledNamespaceModuleChild,
) -> Result<(), CompiledNamespaceMergeError> {
    if module
        .modules
        .iter()
        .any(|existing| existing.name == child.name)
    {
        return Err(CompiledNamespaceMergeError::ConflictingModule {
            module_path: module.path.clone(),
            name: child.name.clone(),
        });
    }
    Ok(())
}

fn reject_duplicate_imported_value(
    module: &CompiledNamespaceModule,
    value: &CompiledNamespaceImportedValue,
) -> Result<(), CompiledNamespaceMergeError> {
    if module
        .imported_values
        .iter()
        .any(|existing| existing.name == value.name)
    {
        return Err(CompiledNamespaceMergeError::ConflictingValue {
            module_path: module.path.clone(),
            name: value.name.clone(),
        });
    }
    Ok(())
}

fn reject_duplicate_imported_type(
    module: &CompiledNamespaceModule,
    ty: &CompiledNamespaceImportedType,
) -> Result<(), CompiledNamespaceMergeError> {
    if module
        .imported_types
        .iter()
        .any(|existing| existing.name == ty.name)
    {
        return Err(CompiledNamespaceMergeError::ConflictingType {
            module_path: module.path.clone(),
            name: ty.name.clone(),
        });
    }
    Ok(())
}

fn reject_duplicate_imported_module(
    module: &CompiledNamespaceModule,
    child: &CompiledNamespaceImportedModule,
) -> Result<(), CompiledNamespaceMergeError> {
    if module
        .imported_modules
        .iter()
        .any(|existing| existing.name == child.name)
    {
        return Err(CompiledNamespaceMergeError::ConflictingModule {
            module_path: module.path.clone(),
            name: child.name.clone(),
        });
    }
    Ok(())
}

fn next_namespace_order(module: &CompiledNamespaceModule) -> u32 {
    module
        .values
        .iter()
        .map(|value| value.order)
        .chain(module.types.iter().map(|ty| ty.order))
        .chain(module.modules.iter().map(|child| child.order))
        .chain(module.imported_values.iter().map(|value| value.order))
        .chain(module.imported_types.iter().map(|ty| ty.order))
        .chain(module.imported_modules.iter().map(|child| child.order))
        .chain(module.aliases.iter().map(|alias| alias.order))
        .max()
        .map_or(0, |order| order + 1)
}

pub struct CompiledNamespaceIndex<'a> {
    surface: &'a CompiledNamespaceSurface,
    modules_by_path: HashMap<Vec<String>, u32>,
}

impl<'a> CompiledNamespaceIndex<'a> {
    pub fn new(surface: &'a CompiledNamespaceSurface) -> Self {
        let modules_by_path = surface
            .modules
            .iter()
            .map(|module| (module.path.clone(), module.id))
            .collect();
        Self {
            surface,
            modules_by_path,
        }
    }

    pub fn module_by_path(&self, path: &[String]) -> Option<&'a CompiledNamespaceModule> {
        self.modules_by_path
            .get(path)
            .and_then(|id| self.module_by_id(*id))
    }

    pub fn module_by_id(&self, id: u32) -> Option<&'a CompiledNamespaceModule> {
        self.surface
            .modules
            .get(id as usize)
            .filter(|module| module.id == id)
    }

    pub fn exported_value_symbol(&self, path: &[String], name: &str) -> Option<u32> {
        let module = self.module_by_path(path)?;
        module
            .values
            .iter()
            .find(|value| value.name == name && value.visibility != CompiledNamespaceVisibility::My)
            .map(|value| value.symbol)
            .or_else(|| {
                module
                    .imported_values
                    .iter()
                    .find(|value| {
                        value.name == name && value.visibility != CompiledNamespaceVisibility::My
                    })
                    .map(|value| value.symbol)
            })
    }

    pub fn exported_type_symbol(&self, path: &[String], name: &str) -> Option<u32> {
        let module = self.module_by_path(path)?;
        module
            .types
            .iter()
            .find(|ty| ty.name == name && ty.visibility != CompiledNamespaceVisibility::My)
            .map(|ty| ty.symbol)
            .or_else(|| {
                module
                    .imported_types
                    .iter()
                    .find(|ty| ty.name == name && ty.visibility != CompiledNamespaceVisibility::My)
                    .map(|ty| ty.symbol)
            })
    }

    pub fn exported_module_id(&self, path: &[String], name: &str) -> Option<u32> {
        let module = self.module_by_path(path)?;
        module
            .modules
            .iter()
            .find(|child| child.name == name && child.visibility != CompiledNamespaceVisibility::My)
            .map(|child| child.module)
            .or_else(|| {
                module
                    .imported_modules
                    .iter()
                    .find(|child| {
                        child.name == name && child.visibility != CompiledNamespaceVisibility::My
                    })
                    .map(|child| child.module)
            })
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

        let index = CompiledNamespaceIndex::new(&surface);
        assert_eq!(index.exported_value_symbol(&[], "x"), Some(x.symbol));
        assert_eq!(index.exported_value_symbol(&ops_path, "x"), Some(x.symbol));
    }

    #[test]
    fn namespace_surface_merge_remaps_independent_modules() {
        let a = CompiledNamespaceSurface::from_loaded_files(&sources::load(vec![
            source(&[], "mod a;\n"),
            source(&["a"], "pub x = 10\n"),
        ]))
        .unwrap();
        let b = CompiledNamespaceSurface::from_loaded_files(&sources::load(vec![
            source(&[], "mod b;\n"),
            source(&["b"], "pub y = 2\n"),
        ]))
        .unwrap();

        let output = CompiledNamespaceSurface::merge_prefixes_with_remap([&a, &b]).unwrap();
        let index = CompiledNamespaceIndex::new(&output.surface);
        let root = index.module_by_path(&[]).unwrap();
        let a_symbol = index.exported_value_symbol(&["a".to_string()], "x");
        let b_symbol = index.exported_value_symbol(&["b".to_string()], "y");

        assert!(root.modules.iter().any(|child| child.name == "a"));
        assert!(root.modules.iter().any(|child| child.name == "b"));
        assert_ne!(a_symbol, b_symbol);
        assert!(a_symbol.is_some());
        assert!(b_symbol.is_some());
        assert_eq!(output.map_module(0, 0), Some(0));
        assert_eq!(output.map_module(1, 0), Some(0));
        assert_eq!(output.map_value(0, 0), a_symbol);
        assert_eq!(output.map_value(1, 0), b_symbol);
    }

    #[test]
    fn namespace_surface_merge_rejects_value_conflict() {
        let lhs = CompiledNamespaceSurface::from_loaded_files(&sources::load(vec![
            source(&[], "mod a;\n"),
            source(&["a"], "pub x = 10\n"),
        ]))
        .unwrap();
        let rhs = CompiledNamespaceSurface::from_loaded_files(&sources::load(vec![
            source(&[], "mod a;\n"),
            source(&["a"], "pub x = 20\n"),
        ]))
        .unwrap();

        let error = CompiledNamespaceSurface::merge_prefixes([&lhs, &rhs]).unwrap_err();

        assert_eq!(
            error,
            CompiledNamespaceMergeError::ConflictingValue {
                module_path: vec!["a".to_string()],
                name: "x".to_string(),
            }
        );
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
