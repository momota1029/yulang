use super::*;

impl ModuleTable {
    pub fn type_decl_by_id(&self, id: TypeDeclId) -> Option<ModuleTypeDecl> {
        for module_index in 0..self.nodes.len() {
            let module = ModuleId(module_index);
            for decl in &self.nodes[module_index].decls {
                if let ModuleDeclKind::Type { id: decl_id, kind } = decl.kind
                    && decl_id == id
                {
                    return Some(ModuleTypeDecl {
                        name: decl.name.clone(),
                        vis: decl.vis,
                        order: decl.order,
                        module,
                        id: decl_id,
                        kind,
                    });
                }
            }
        }
        None
    }
    pub(super) fn import_alias(&mut self, module: ModuleId, alias: &AliasDecl) {
        match &alias.import {
            UseImport::Alias { name, path } => {
                self.import_op_aliases(module, name, path, alias);
                let Some(target) = self.import_path_target(module, path, alias.order) else {
                    return;
                };
                if let Some(def) = target.value {
                    self.push_import_value(
                        module,
                        name.clone(),
                        ImportedValueDecl {
                            order: alias.order,
                            def,
                            vis: alias.vis,
                        },
                    );
                }
                if let Some(decl) = target.ty {
                    self.push_import_type(
                        module,
                        name.clone(),
                        ImportedTypeDecl {
                            order: alias.order,
                            decl,
                            vis: alias.vis,
                        },
                    );
                }
                if let Some(found) = target.module {
                    self.push_import_module(
                        module,
                        name.clone(),
                        ImportedModuleDecl {
                            order: alias.order,
                            module: found,
                            vis: alias.vis,
                        },
                    );
                }
            }
            UseImport::Glob { prefix } => {
                let Some(target) = self.raw_module_path_from(module, &prefix.segments, alias.order)
                else {
                    return;
                };
                for decl in self.module_value_imports(target) {
                    self.push_import_value(
                        module,
                        decl.name.clone(),
                        ImportedValueDecl {
                            order: alias.order,
                            def: decl.def,
                            vis: alias.vis,
                        },
                    );
                }
                for decl in self.module_type_imports(target) {
                    self.push_import_type(
                        module,
                        decl.name.clone(),
                        ImportedTypeDecl {
                            order: alias.order,
                            decl,
                            vis: alias.vis,
                        },
                    );
                }
                for decl in self.module_module_imports(target) {
                    self.push_import_module(
                        module,
                        decl.name.clone(),
                        ImportedModuleDecl {
                            order: alias.order,
                            module: decl.module,
                            vis: alias.vis,
                        },
                    );
                }
                // target が再エクスポートしている import も運ぶ（`my use` だけはファイル内
                // private。our は band 内可視、pub は band 境界用）。prelude のような
                // 「再エクスポートしか持たない module」の連鎖は `build_import_views` の
                // 不動点で閉じる。
                let reexported_values = self.nodes[target.0]
                    .import_values
                    .iter()
                    .map(|(name, entries)| {
                        let defs = entries
                            .iter()
                            .filter(|entry| entry.vis != Vis::My)
                            .map(|entry| entry.def)
                            .collect::<Vec<_>>();
                        (name.clone(), defs)
                    })
                    .collect::<Vec<_>>();
                for (name, defs) in reexported_values {
                    for def in defs {
                        self.push_import_value(
                            module,
                            name.clone(),
                            ImportedValueDecl {
                                order: alias.order,
                                def,
                                vis: alias.vis,
                            },
                        );
                    }
                }
                let reexported_types = self.nodes[target.0]
                    .import_types
                    .iter()
                    .map(|(name, entries)| {
                        let decls = entries
                            .iter()
                            .filter(|entry| entry.vis != Vis::My)
                            .map(|entry| entry.decl.clone())
                            .collect::<Vec<_>>();
                        (name.clone(), decls)
                    })
                    .collect::<Vec<_>>();
                for (name, decls) in reexported_types {
                    for decl in decls {
                        self.push_import_type(
                            module,
                            name.clone(),
                            ImportedTypeDecl {
                                order: alias.order,
                                decl,
                                vis: alias.vis,
                            },
                        );
                    }
                }
                let reexported_modules = self.nodes[target.0]
                    .import_modules
                    .iter()
                    .map(|(name, entries)| {
                        let modules = entries
                            .iter()
                            .filter(|entry| entry.vis != Vis::My)
                            .map(|entry| entry.module)
                            .collect::<Vec<_>>();
                        (name.clone(), modules)
                    })
                    .collect::<Vec<_>>();
                for (name, modules) in reexported_modules {
                    for found in modules {
                        self.push_import_module(
                            module,
                            name.clone(),
                            ImportedModuleDecl {
                                order: alias.order,
                                module: found,
                                vis: alias.vis,
                            },
                        );
                    }
                }
            }
        }
    }
    /// import entry の追加。同一 entry の重複 push を弾くので、`build_import_views` の
    /// 不動点繰り返しに対して冪等になる。
    pub(super) fn push_import_value(
        &mut self,
        module: ModuleId,
        name: Name,
        decl: ImportedValueDecl,
    ) {
        let entries = self.nodes[module.0].import_values.entry(name).or_default();
        if !entries.contains(&decl) {
            entries.push(decl);
        }
    }
    pub(super) fn push_import_type(
        &mut self,
        module: ModuleId,
        name: Name,
        decl: ImportedTypeDecl,
    ) {
        let entries = self.nodes[module.0].import_types.entry(name).or_default();
        if !entries.contains(&decl) {
            entries.push(decl);
        }
    }
    pub(super) fn push_import_module(
        &mut self,
        module: ModuleId,
        name: Name,
        decl: ImportedModuleDecl,
    ) {
        let entries = self.nodes[module.0].import_modules.entry(name).or_default();
        if !entries.contains(&decl) {
            entries.push(decl);
        }
    }
    /// 名前指定 import の op symbol 展開。`use foo::(+)` は plain name `+` として届くので、
    /// 各 fixity の mangled 名（`#op:infix:+` 等）でも値を引き、見つかったものを全部運ぶ。
    pub(super) fn import_op_aliases(
        &mut self,
        module: ModuleId,
        name: &Name,
        path: &ModulePath,
        alias: &AliasDecl,
    ) {
        let Some(last) = path.segments.last().cloned() else {
            return;
        };
        for fixity in OP_FIXITY_TAGS {
            let mut op_path = path.clone();
            *op_path
                .segments
                .last_mut()
                .expect("op import path should be non-empty") = op_value_name(fixity, &last.0);
            let Some(target) = self.import_path_target(module, &op_path, alias.order) else {
                continue;
            };
            let Some(def) = target.value else {
                continue;
            };
            self.push_import_value(
                module,
                op_value_name(fixity, &name.0),
                ImportedValueDecl {
                    order: alias.order,
                    def,
                    vis: alias.vis,
                },
            );
        }
    }
    pub(super) fn import_path_target(
        &self,
        module: ModuleId,
        path: &ModulePath,
        site: ModuleOrder,
    ) -> Option<ImportPathTarget> {
        let Some((last, prefix)) = path.segments.split_last() else {
            return None;
        };
        if prefix.is_empty() {
            return Some(ImportPathTarget {
                value: self.raw_lexical_value_at(module, last, site),
                ty: self.raw_lexical_type_at(module, last, site),
                module: self.raw_lexical_module_at(module, last, site),
            });
        }

        let target = self.raw_module_path_from(module, prefix, site)?;
        Some(ImportPathTarget {
            value: self
                .value_at(target, last, module_path_site())
                .or_else(|| self.exported_value_at(target, last)),
            ty: self
                .type_at(target, last, module_path_site())
                .or_else(|| self.exported_type_at(target, last)),
            module: self
                .module_at(target, last, module_path_site())
                .or_else(|| self.exported_module_at(target, last)),
        })
    }
    pub(super) fn raw_module_path_from(
        &self,
        module: ModuleId,
        path: &[Name],
        site: ModuleOrder,
    ) -> Option<ModuleId> {
        let Some((first, rest)) = path.split_first() else {
            return Some(module);
        };
        let mut current = self.raw_lexical_module_at(module, first, site)?;
        for segment in rest {
            current = self.module_at(current, segment, module_path_site())?;
        }
        Some(current)
    }
    /// `value_path_at` / `type_path_at` 用の prefix 降下。再エクスポート（import view）も辿る。
    /// alias 展開で使う `raw_module_path_from` は import view 構築順に依存しないよう
    /// 意図的に raw のままにしてあるので、こちらと混ぜない。
    pub(super) fn module_path_with_imports_from(
        &self,
        module: ModuleId,
        path: &[Name],
        site: ModuleOrder,
    ) -> Option<ModuleId> {
        let Some((first, rest)) = path.split_first() else {
            return Some(module);
        };
        let mut current = self.lexical_module_with_imports_at(module, first, site)?;
        for segment in rest {
            current = self
                .module_at(current, segment, module_path_site())
                .or_else(|| self.exported_module_at(current, segment))?;
        }
        Some(current)
    }
    pub(super) fn lexical_module_with_imports_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<ModuleId> {
        loop {
            if let Some(found) = self.module_at(module, name, site) {
                return Some(found);
            }
            if let Some(found) = self.imported_module_at(module, name, site) {
                return Some(found);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    pub(super) fn raw_lexical_value_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<DefId> {
        loop {
            if let Some(def) = self.value_at(module, name, site) {
                return Some(def);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    pub(super) fn raw_lexical_type_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        loop {
            if let Some(found) = self.type_at(module, name, site) {
                return Some(found);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    pub(super) fn raw_lexical_module_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<ModuleId> {
        loop {
            if let Some(found) = self.module_at(module, name, site) {
                return Some(found);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    pub(super) fn imported_value_at(
        &self,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Option<DefId> {
        self.select_import(self.nodes[module.0].import_values.get(name)?, site)
            .map(|decl| decl.def)
    }
    pub(super) fn imported_type_at(
        &self,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        self.select_import(self.nodes[module.0].import_types.get(name)?, site)
            .map(|decl| decl.decl.clone())
    }
    pub(super) fn imported_module_at(
        &self,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Option<ModuleId> {
        self.select_import(self.nodes[module.0].import_modules.get(name)?, site)
            .map(|decl| decl.module)
    }
    /// 外の module から見える import entry（再エクスポート）。`my use` だけはファイル内
    /// private なので外からは見えない。our は band 内可視、pub は band 境界用（band は未実装）。
    pub(super) fn exported_value_at(&self, module: ModuleId, name: &Name) -> Option<DefId> {
        self.nodes[module.0]
            .import_values
            .get(name)?
            .iter()
            .find(|entry| entry.vis != Vis::My)
            .map(|entry| entry.def)
    }
    pub(super) fn exported_type_at(&self, module: ModuleId, name: &Name) -> Option<ModuleTypeDecl> {
        self.nodes[module.0]
            .import_types
            .get(name)?
            .iter()
            .find(|entry| entry.vis != Vis::My)
            .map(|entry| entry.decl.clone())
    }
    pub(super) fn exported_module_at(&self, module: ModuleId, name: &Name) -> Option<ModuleId> {
        self.nodes[module.0]
            .import_modules
            .get(name)?
            .iter()
            .find(|entry| entry.vis != Vis::My)
            .map(|entry| entry.module)
    }
    pub(super) fn module_value_imports(&self, module: ModuleId) -> Vec<ModuleValueDecl> {
        self.nodes[module.0]
            .values
            .keys()
            .flat_map(|name| self.value_decls(module, name))
            .collect()
    }
    pub fn module_value_decls(&self, module: ModuleId) -> Vec<ModuleValueDecl> {
        self.nodes[module.0]
            .decls
            .iter()
            .filter_map(|decl| match decl.kind {
                ModuleDeclKind::Value { def } => Some(ModuleValueDecl {
                    name: decl.name.clone(),
                    vis: decl.vis,
                    order: decl.order,
                    def,
                }),
                ModuleDeclKind::Type { .. } | ModuleDeclKind::Module { .. } => None,
            })
            .collect()
    }
    pub(super) fn module_type_imports(&self, module: ModuleId) -> Vec<ModuleTypeDecl> {
        self.nodes[module.0]
            .types
            .keys()
            .flat_map(|name| self.type_decls(module, name))
            .collect()
    }
    pub fn module_type_decls(&self, module: ModuleId) -> Vec<ModuleTypeDecl> {
        self.nodes[module.0]
            .decls
            .iter()
            .filter_map(|decl| match decl.kind {
                ModuleDeclKind::Type { id, kind } => Some(ModuleTypeDecl {
                    name: decl.name.clone(),
                    vis: decl.vis,
                    order: decl.order,
                    module,
                    id,
                    kind,
                }),
                ModuleDeclKind::Value { .. } | ModuleDeclKind::Module { .. } => None,
            })
            .collect()
    }
    pub(super) fn module_module_imports(&self, module: ModuleId) -> Vec<ModuleChildDecl> {
        self.nodes[module.0]
            .modules
            .keys()
            .flat_map(|name| self.module_decls(module, name))
            .collect()
    }
    pub fn module_child_decls(&self, module: ModuleId) -> Vec<ModuleChildDecl> {
        self.nodes[module.0]
            .decls
            .iter()
            .filter_map(|decl| match decl.kind {
                ModuleDeclKind::Module { module, def } => Some(ModuleChildDecl {
                    name: decl.name.clone(),
                    vis: decl.vis,
                    order: decl.order,
                    module,
                    def,
                }),
                ModuleDeclKind::Value { .. } | ModuleDeclKind::Type { .. } => None,
            })
            .collect()
    }
    pub fn module_imported_value_decls(&self, module: ModuleId) -> Vec<ModuleImportedValueDecl> {
        self.nodes[module.0]
            .import_values
            .iter()
            .flat_map(|(name, entries)| {
                entries.iter().map(|entry| ModuleImportedValueDecl {
                    name: name.clone(),
                    vis: entry.vis,
                    order: entry.order,
                    def: entry.def,
                })
            })
            .collect()
    }
    pub fn module_imported_type_decls(&self, module: ModuleId) -> Vec<ModuleImportedTypeDecl> {
        self.nodes[module.0]
            .import_types
            .iter()
            .flat_map(|(name, entries)| {
                entries.iter().map(|entry| ModuleImportedTypeDecl {
                    name: name.clone(),
                    vis: entry.vis,
                    order: entry.order,
                    decl: entry.decl.clone(),
                })
            })
            .collect()
    }
    pub fn module_imported_module_decls(&self, module: ModuleId) -> Vec<ModuleImportedModuleDecl> {
        self.nodes[module.0]
            .import_modules
            .iter()
            .flat_map(|(name, entries)| {
                entries.iter().map(|entry| ModuleImportedModuleDecl {
                    name: name.clone(),
                    vis: entry.vis,
                    order: entry.order,
                    module: entry.module,
                })
            })
            .collect()
    }
    pub fn value_decls(&self, module: ModuleId, name: &Name) -> Vec<ModuleValueDecl> {
        self.nodes[module.0]
            .values
            .get(name)
            .into_iter()
            .flat_map(|decls| decls.iter())
            .filter_map(|decl| {
                let decl = &self.nodes[module.0].decls[decl.0];
                match decl.kind {
                    ModuleDeclKind::Value { def } => Some(ModuleValueDecl {
                        name: decl.name.clone(),
                        vis: decl.vis,
                        order: decl.order,
                        def,
                    }),
                    ModuleDeclKind::Type { .. } | ModuleDeclKind::Module { .. } => None,
                }
            })
            .collect()
    }
    pub fn type_decls(&self, module: ModuleId, name: &Name) -> Vec<ModuleTypeDecl> {
        self.nodes[module.0]
            .types
            .get(name)
            .into_iter()
            .flat_map(|decls| decls.iter())
            .filter_map(|decl| {
                let decl = &self.nodes[module.0].decls[decl.0];
                match decl.kind {
                    ModuleDeclKind::Type { id, kind } => Some(ModuleTypeDecl {
                        name: decl.name.clone(),
                        vis: decl.vis,
                        order: decl.order,
                        module,
                        id,
                        kind,
                    }),
                    ModuleDeclKind::Value { .. } | ModuleDeclKind::Module { .. } => None,
                }
            })
            .collect()
    }
    pub fn module_decls(&self, module: ModuleId, name: &Name) -> Vec<ModuleChildDecl> {
        self.nodes[module.0]
            .modules
            .get(name)
            .into_iter()
            .flat_map(|decls| decls.iter())
            .filter_map(|decl| {
                let decl = &self.nodes[module.0].decls[decl.0];
                match decl.kind {
                    ModuleDeclKind::Module { module, def } => Some(ModuleChildDecl {
                        name: decl.name.clone(),
                        vis: decl.vis,
                        order: decl.order,
                        module,
                        def,
                    }),
                    ModuleDeclKind::Value { .. } | ModuleDeclKind::Type { .. } => None,
                }
            })
            .collect()
    }
    pub(crate) fn first_module_decl(
        &self,
        module: ModuleId,
        name: &Name,
    ) -> Option<ModuleChildDecl> {
        self.module_decls(module, name).into_iter().next()
    }
    /// dump 用の source label table を作る。
    ///
    /// `poly` は source 名を本体に持たないため、名前を読める dump が必要な時だけ
    /// infer-local の module table から `DefId -> source path` を投影する。
    pub fn dump_labels(&self) -> DumpLabels {
        let mut labels = DumpLabels::new();
        self.add_dump_labels(self.root_id(), &mut Vec::new(), &mut labels);
        labels
    }
    pub(super) fn push_decl(
        &mut self,
        module: ModuleId,
        name: Name,
        vis: Vis,
        kind: ModuleDeclKind,
    ) -> ModuleDeclId {
        let order = self.next_order(module);
        let node = &mut self.nodes[module.0];
        let id = ModuleDeclId(node.decls.len());
        node.decls.push(ModuleDecl {
            name,
            vis,
            order,
            kind,
        });
        id
    }
    pub(crate) fn next_order(&mut self, module: ModuleId) -> ModuleOrder {
        let node = &mut self.nodes[module.0];
        let order = ModuleOrder(node.next_order);
        node.next_order += 1;
        order
    }
    pub(super) fn next_type_decl_id(&mut self) -> TypeDeclId {
        let id = TypeDeclId(self.next_type_id);
        self.next_type_id += 1;
        id
    }
    pub(super) fn select_decl(
        &self,
        module: ModuleId,
        decls: &[ModuleDeclId],
        site: ModuleOrder,
    ) -> Option<&ModuleDecl> {
        let node = &self.nodes[module.0];
        decls
            .iter()
            .map(|decl| &node.decls[decl.0])
            .filter(|decl| decl.order <= site)
            .max_by_key(|decl| decl.order)
            .or_else(|| {
                decls
                    .iter()
                    .map(|decl| &node.decls[decl.0])
                    .filter(|decl| decl.order > site)
                    .min_by_key(|decl| decl.order)
            })
    }
    fn select_import<'a, T>(&self, imports: &'a [T], site: ModuleOrder) -> Option<&'a T>
    where
        T: ImportOrder,
    {
        imports
            .iter()
            .filter(|decl| decl.order() <= site)
            .max_by_key(|decl| decl.order())
            .or_else(|| {
                imports
                    .iter()
                    .filter(|decl| decl.order() > site)
                    .min_by_key(|decl| decl.order())
            })
    }
    pub(super) fn add_dump_labels(
        &self,
        module: ModuleId,
        prefix: &mut Vec<String>,
        labels: &mut DumpLabels,
    ) {
        for decl in &self.nodes[module.0].decls {
            let label = qualified_label(prefix, &decl.name);
            match decl.kind {
                ModuleDeclKind::Value { def } => {
                    labels.set_def_label(def, label);
                }
                ModuleDeclKind::Module { module, def } => {
                    labels.set_def_label(def, label);
                    prefix.push(decl.name.0.clone());
                    self.add_dump_labels(module, prefix, labels);
                    prefix.pop();
                }
                ModuleDeclKind::Type { .. } => {}
            }
        }
    }
}
