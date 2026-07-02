use rustc_hash::FxHashMap;

use super::*;
use crate::{
    CompiledLoweringSurface, CompiledNamespaceModule, CompiledNamespaceModuleChild,
    CompiledNamespaceModuleType, CompiledNamespaceModuleValue, CompiledNamespaceSurface,
    CompiledNamespaceVisibility, CompiledRuntimeImport, restore_compiled_act_template,
    restore_compiled_constructor_payload, restore_compiled_optional_stored_signature,
};

impl ModuleTable {
    pub(crate) fn from_compiled_surfaces(
        namespace: &CompiledNamespaceSurface,
        lowering: &CompiledLoweringSurface,
        runtime_import: &CompiledRuntimeImport,
    ) -> Option<Self> {
        let mut builder = CompiledModuleTableBuilder::new(namespace, lowering, runtime_import)?;
        builder.build_namespace();
        builder.build_import_views();
        builder.build_companions();
        builder.apply_lowering_surface();
        Some(builder.modules)
    }
}

struct CompiledModuleTableBuilder<'a> {
    namespace: &'a CompiledNamespaceSurface,
    lowering: &'a CompiledLoweringSurface,
    runtime_import: &'a CompiledRuntimeImport,
    modules: ModuleTable,
    module_ids: FxHashMap<u32, ModuleId>,
    type_ids: FxHashMap<u32, TypeDeclId>,
    value_defs: FxHashMap<u32, DefId>,
    module_defs: FxHashMap<u32, DefId>,
}

impl<'a> CompiledModuleTableBuilder<'a> {
    fn new(
        namespace: &'a CompiledNamespaceSurface,
        lowering: &'a CompiledLoweringSurface,
        runtime_import: &'a CompiledRuntimeImport,
    ) -> Option<Self> {
        let mut modules = ModuleTable::new();
        let mut module_ids = FxHashMap::default();
        module_ids.insert(0, modules.root_id());

        let mut surface_modules = namespace.modules.iter().collect::<Vec<_>>();
        surface_modules.sort_by_key(|module| module.id);
        for module in surface_modules {
            if module.id == 0 {
                continue;
            }
            module_ids.insert(module.id, modules.new_module());
        }

        let value_defs = runtime_import
            .values
            .iter()
            .map(|value| (value.symbol, value.def))
            .collect::<FxHashMap<_, _>>();
        let module_defs = runtime_import
            .modules
            .iter()
            .map(|module| (module.module, module.def))
            .collect::<FxHashMap<_, _>>();

        Some(Self {
            namespace,
            lowering,
            runtime_import,
            modules,
            module_ids,
            type_ids: FxHashMap::default(),
            value_defs,
            module_defs,
        })
    }

    fn build_namespace(&mut self) {
        let mut surface_modules = self.namespace.modules.iter().collect::<Vec<_>>();
        surface_modules.sort_by_key(|module| module.id);
        for module in surface_modules {
            self.build_module_decls(module);
        }
    }

    fn build_module_decls(&mut self, module: &CompiledNamespaceModule) {
        let Some(module_id) = self.module_ids.get(&module.id).copied() else {
            return;
        };
        self.modules
            .set_module_band_path(module_id, module_path(&module.band_path));
        let mut entries = Vec::new();
        entries.extend(
            module
                .values
                .iter()
                .enumerate()
                .map(|(index, value)| CompiledDeclEntry {
                    order: value.order,
                    kind: CompiledDeclEntryKind::Value(index),
                }),
        );
        entries.extend(
            module
                .types
                .iter()
                .enumerate()
                .map(|(index, ty)| CompiledDeclEntry {
                    order: ty.order,
                    kind: CompiledDeclEntryKind::Type(index),
                }),
        );
        entries.extend(
            module
                .modules
                .iter()
                .enumerate()
                .map(|(index, child)| CompiledDeclEntry {
                    order: child.order,
                    kind: CompiledDeclEntryKind::Module(index),
                }),
        );
        entries.sort_by_key(|entry| (entry.order, entry.kind.discriminant()));

        for entry in entries {
            match entry.kind {
                CompiledDeclEntryKind::Value(index) => {
                    self.insert_value(module_id, &module.values[index]);
                }
                CompiledDeclEntryKind::Type(index) => {
                    self.insert_type(module_id, &module.types[index]);
                }
                CompiledDeclEntryKind::Module(index) => {
                    self.insert_module(module_id, &module.modules[index]);
                }
            }
        }
    }

    fn insert_value(&mut self, module: ModuleId, value: &CompiledNamespaceModuleValue) {
        let Some(def) = self.value_defs.get(&value.symbol).copied() else {
            return;
        };
        self.modules.insert_value_with_span(
            module,
            Name(value.name.clone()),
            def,
            visibility(value.visibility),
            None,
        );
        if value.lazy {
            self.modules.mark_lazy_op(def);
        }
    }

    fn insert_type(&mut self, module: ModuleId, ty: &CompiledNamespaceModuleType) {
        let id = self.modules.insert_type(
            module,
            Name(ty.name.clone()),
            module_type_kind(ty.kind),
            visibility(ty.visibility),
        );
        if ty.host {
            self.modules.set_host_act(id);
        }
        self.type_ids.insert(ty.symbol, id);
    }

    fn insert_module(&mut self, module: ModuleId, child: &CompiledNamespaceModuleChild) {
        let Some(child_module) = self.module_ids.get(&child.module).copied() else {
            return;
        };
        let Some(def) = self.module_defs.get(&child.module).copied() else {
            return;
        };
        self.modules.insert_module(
            module,
            Name(child.name.clone()),
            child_module,
            def,
            visibility(child.visibility),
        );
    }

    fn build_import_views(&mut self) {
        for module in &self.namespace.modules {
            let Some(module_id) = self.module_ids.get(&module.id).copied() else {
                continue;
            };
            for value in &module.imported_values {
                let Some(def) = self.value_defs.get(&value.symbol).copied() else {
                    continue;
                };
                self.modules.nodes[module_id.0]
                    .import_values
                    .entry(Name(value.name.clone()))
                    .or_default()
                    .push(ImportedValueDecl {
                        order: ModuleOrder::from_index(value.order),
                        def,
                        vis: visibility(value.visibility),
                    });
            }
            for ty in &module.imported_types {
                let Some(id) = self.type_ids.get(&ty.symbol).copied() else {
                    continue;
                };
                let Some(decl) = self.modules.type_decl_by_id(id) else {
                    continue;
                };
                self.modules.nodes[module_id.0]
                    .import_types
                    .entry(Name(ty.name.clone()))
                    .or_default()
                    .push(ImportedTypeDecl {
                        order: ModuleOrder::from_index(ty.order),
                        decl,
                        vis: visibility(ty.visibility),
                    });
            }
            for child in &module.imported_modules {
                let Some(child_module) = self.module_ids.get(&child.module).copied() else {
                    continue;
                };
                self.modules.nodes[module_id.0]
                    .import_modules
                    .entry(Name(child.name.clone()))
                    .or_default()
                    .push(ImportedModuleDecl {
                        order: ModuleOrder::from_index(child.order),
                        module: child_module,
                        vis: visibility(child.visibility),
                    });
            }
        }
    }

    fn build_companions(&mut self) {
        let modules_by_path = self
            .namespace
            .modules
            .iter()
            .filter_map(|module| Some((module.path.clone(), *self.module_ids.get(&module.id)?)))
            .collect::<FxHashMap<_, _>>();
        for ty in &self.namespace.types {
            let Some(id) = self.type_ids.get(&ty.unit_id).copied() else {
                continue;
            };
            if let Some(module) = modules_by_path.get(&ty.path).copied() {
                self.modules.set_type_companion(id, module);
            }
        }
    }

    fn apply_lowering_surface(&mut self) {
        self.apply_act_type_vars();
        self.apply_act_templates();
        self.apply_role_shapes();
        self.apply_constructor_payloads();
        self.apply_act_operations();
        self.apply_type_methods();
        self.apply_type_field_methods();
        self.apply_act_methods();
        self.apply_role_methods();
    }

    fn apply_act_type_vars(&mut self) {
        for entry in &self.lowering.act_type_vars {
            if let Some(id) = self.type_ids.get(&entry.type_symbol).copied() {
                self.modules.set_act_type_vars(id, entry.vars.clone());
            }
        }
    }

    fn apply_act_templates(&mut self) {
        for entry in &self.lowering.act_templates {
            let Some(id) = self.type_ids.get(&entry.type_symbol).copied() else {
                continue;
            };
            let Some(template) = restore_compiled_act_template(&entry.source) else {
                continue;
            };
            self.modules.set_act_template(id, template);
        }
    }

    fn apply_role_shapes(&mut self) {
        for entry in &self.lowering.role_shapes {
            let Some(id) = self.type_ids.get(&entry.type_symbol).copied() else {
                continue;
            };
            self.modules.set_role_inputs(id, entry.inputs.clone());
            self.modules
                .set_role_associated(id, entry.associated.clone());
        }
    }

    fn apply_constructor_payloads(&mut self) {
        for entry in &self.lowering.constructor_payloads {
            let Some(def) = self.value_defs.get(&entry.value_symbol).copied() else {
                continue;
            };
            let Some(owner) = self.type_ids.get(&entry.owner_type_symbol).copied() else {
                continue;
            };
            let Some(module) = self.value_module(entry.value_symbol) else {
                continue;
            };
            let Some(payload) = restore_compiled_constructor_payload(&self.modules, &entry.payload)
            else {
                continue;
            };
            self.modules.insert_constructor(
                def,
                ConstructorDecl {
                    owner,
                    module,
                    type_vars: entry.owner_type_vars.clone(),
                    payload,
                },
            );
        }
    }

    fn apply_act_operations(&mut self) {
        let mut ops_by_owner = FxHashMap::<TypeDeclId, Vec<ActOperationSig>>::default();
        for entry in &self.lowering.act_operations {
            let Some(owner) = self.type_ids.get(&entry.type_symbol).copied() else {
                continue;
            };
            ops_by_owner
                .entry(owner)
                .or_default()
                .push(ActOperationSig {
                    name: Name(entry.name.clone()),
                    signature: restore_compiled_optional_stored_signature(
                        &self.modules,
                        &entry.signature,
                    ),
                });
            if let Some(source_def) = entry.source_def {
                let def = self.runtime_import.map_def(source_def);
                self.modules
                    .insert_act_operation_def(owner, Name(entry.name.clone()), def);
            } else if let Some(symbol) = entry.value_symbol
                && let Some(def) = self.value_defs.get(&symbol).copied()
            {
                self.modules
                    .insert_act_operation_def(owner, Name(entry.name.clone()), def);
            }
        }
        for (owner, ops) in ops_by_owner {
            self.modules.set_act_ops(owner, ops);
        }
    }

    fn apply_type_methods(&mut self) {
        for entry in &self.lowering.type_methods {
            let Some(owner) = self.type_ids.get(&entry.owner_type_symbol).copied() else {
                continue;
            };
            self.modules.insert_type_method(TypeMethodDecl {
                owner,
                name: Name(entry.name.clone()),
                receiver: Name(entry.receiver.clone()),
                receiver_kind: entry.receiver_kind,
                def: self.runtime_import.map_def(entry.source_def),
                vis: visibility(entry.visibility),
                order: ModuleOrder::from_index(entry.order),
            });
        }
    }

    fn apply_type_field_methods(&mut self) {
        for entry in &self.lowering.type_field_methods {
            let Some(owner) = self.type_ids.get(&entry.owner_type_symbol).copied() else {
                continue;
            };
            self.modules.insert_type_field_method(TypeFieldMethodDecl {
                owner,
                name: Name(entry.name.clone()),
                receiver_kind: entry.receiver_kind,
                def: self.runtime_import.map_def(entry.source_def),
                vis: visibility(entry.visibility),
            });
        }
    }

    fn apply_act_methods(&mut self) {
        for entry in &self.lowering.act_methods {
            let Some(owner) = self.type_ids.get(&entry.owner_type_symbol).copied() else {
                continue;
            };
            self.modules.insert_act_method(ActMethodDecl {
                owner,
                name: Name(entry.name.clone()),
                receiver: Name(entry.receiver.clone()),
                def: self.runtime_import.map_def(entry.source_def),
                vis: visibility(entry.visibility),
                order: ModuleOrder::from_index(entry.order),
            });
        }
    }

    fn apply_role_methods(&mut self) {
        for entry in &self.lowering.role_methods {
            let Some(owner) = self.type_ids.get(&entry.type_symbol).copied() else {
                continue;
            };
            self.modules.insert_role_method(RoleMethodDecl {
                owner,
                name: Name(entry.name.clone()),
                receiver: entry.receiver.as_ref().map(|name| Name(name.clone())),
                def: self.runtime_import.map_def(entry.source_def),
                vis: visibility(entry.visibility),
                order: ModuleOrder::from_index(entry.order),
                signature: restore_compiled_optional_stored_signature(
                    &self.modules,
                    &entry.signature,
                ),
            });
        }
    }

    fn value_module(&self, symbol: u32) -> Option<ModuleId> {
        for module in &self.namespace.modules {
            if module.values.iter().any(|value| value.symbol == symbol) {
                return self.module_ids.get(&module.id).copied();
            }
        }
        None
    }
}

#[derive(Clone, Copy)]
struct CompiledDeclEntry {
    order: u32,
    kind: CompiledDeclEntryKind,
}

#[derive(Clone, Copy)]
enum CompiledDeclEntryKind {
    Value(usize),
    Type(usize),
    Module(usize),
}

impl CompiledDeclEntryKind {
    fn discriminant(self) -> u8 {
        match self {
            CompiledDeclEntryKind::Value(_) => 0,
            CompiledDeclEntryKind::Type(_) => 1,
            CompiledDeclEntryKind::Module(_) => 2,
        }
    }
}

fn visibility(visibility: CompiledNamespaceVisibility) -> Vis {
    match visibility {
        CompiledNamespaceVisibility::Pub => Vis::Pub,
        CompiledNamespaceVisibility::Our => Vis::Our,
        CompiledNamespaceVisibility::My => Vis::My,
    }
}

fn module_type_kind(kind: crate::CompiledNamespaceTypeKind) -> ModuleTypeKind {
    match kind {
        crate::CompiledNamespaceTypeKind::TypeAlias => ModuleTypeKind::TypeAlias,
        crate::CompiledNamespaceTypeKind::Struct => ModuleTypeKind::Struct,
        crate::CompiledNamespaceTypeKind::Enum => ModuleTypeKind::Enum,
        crate::CompiledNamespaceTypeKind::Error => ModuleTypeKind::Error,
        crate::CompiledNamespaceTypeKind::Role => ModuleTypeKind::Role,
        crate::CompiledNamespaceTypeKind::Act => ModuleTypeKind::Act,
    }
}

fn module_path(path: &[String]) -> sources::Path {
    sources::Path {
        segments: path.iter().map(|segment| Name(segment.clone())).collect(),
    }
}
