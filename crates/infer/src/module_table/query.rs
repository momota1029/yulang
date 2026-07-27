use super::*;

type ImportVisibility = VisibilityRoute;

impl ModuleTable {
    pub fn test_module_decls(&self) -> &[TestModuleDecl] {
        &self.test_modules
    }

    pub fn is_test_module(&self, module: ModuleId) -> bool {
        self.test_modules.iter().any(|test| test.module == module)
    }

    pub fn module_root_expr_owners(&self, module: ModuleId) -> &[Option<DefId>] {
        self.root_expr_owners
            .get(&module)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub(crate) fn unnamed_test_module_decl(
        &self,
        parent: ModuleId,
        index: usize,
    ) -> Option<TestModuleDecl> {
        self.test_modules
            .iter()
            .filter(|test| test.parent == parent && test.name.is_none())
            .nth(index)
            .cloned()
    }

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
                        private_origin: decl.private_origin,
                    });
                }
            }
        }
        None
    }
    pub(super) fn import_alias(&mut self, module: ModuleId, alias: &AliasDecl) {
        match &alias.import {
            UseImport::Alias {
                name, path, route, ..
            } => {
                self.import_op_aliases(module, name, path, *route, alias);
                let Some(target) =
                    self.import_path_target_from_route(module, path, *route, alias.order)
                else {
                    self.record_private_import_access(module, path, *route, alias.order, alias);
                    return;
                };
                if target.value.is_none() && target.ty.is_none() && target.module.is_none() {
                    self.record_private_import_access(module, path, *route, alias.order, alias);
                    return;
                }
                if let Some(target) = target.value {
                    self.push_import_value(
                        module,
                        name.clone(),
                        ImportedValueDecl {
                            order: alias.order,
                            def: target.def,
                            vis: alias.vis,
                            private_origin: alias.private_origin.or(target.private_origin),
                        },
                    );
                }
                if let Some(target) = target.ty {
                    self.push_import_type(
                        module,
                        name.clone(),
                        ImportedTypeDecl {
                            order: alias.order,
                            decl: target.decl,
                            vis: alias.vis,
                            private_origin: alias.private_origin.or(target.private_origin),
                        },
                    );
                }
                if let Some(target) = target.module {
                    self.push_import_module(
                        module,
                        name.clone(),
                        ImportedModuleDecl {
                            order: alias.order,
                            module: target.module,
                            vis: alias.vis,
                            private_origin: alias.private_origin.or(target.private_origin),
                        },
                    );
                }
            }
            UseImport::Glob { prefix, route, .. } => {
                let visibility = import_visibility(*route);
                let (base, prefix) = self.import_base_and_path_segments(module, prefix, *route);
                let Some(target) = self.module_path_from_for_import(
                    module,
                    base,
                    &prefix.segments,
                    alias.order,
                    visibility,
                ) else {
                    self.record_private_import_access(module, &prefix, *route, alias.order, alias);
                    return;
                };
                for decl in self.module_value_imports_for_import(module, target, visibility) {
                    self.push_import_value(
                        module,
                        decl.name.clone(),
                        ImportedValueDecl {
                            order: alias.order,
                            def: decl.def,
                            vis: alias.vis,
                            private_origin: alias.private_origin.or(decl.private_origin),
                        },
                    );
                }
                for decl in self.module_type_imports_for_import(module, target, visibility) {
                    self.push_import_type(
                        module,
                        decl.name.clone(),
                        ImportedTypeDecl {
                            order: alias.order,
                            private_origin: alias.private_origin.or(decl.private_origin),
                            decl,
                            vis: alias.vis,
                        },
                    );
                }
                let direct_modules =
                    self.module_module_imports_for_import(module, target, visibility);
                let direct_module_names = direct_modules
                    .iter()
                    .map(|decl| decl.name.clone())
                    .collect::<FxHashSet<_>>();
                for decl in direct_modules {
                    self.push_import_module(
                        module,
                        decl.name.clone(),
                        ImportedModuleDecl {
                            order: alias.order,
                            module: decl.module,
                            vis: alias.vis,
                            private_origin: alias.private_origin.or(decl.private_origin),
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
                        let entries = entries
                            .iter()
                            .filter(|entry| {
                                self.import_entry_allows(
                                    module,
                                    target,
                                    entry.vis,
                                    entry.private_origin,
                                    visibility,
                                )
                            })
                            .cloned()
                            .collect::<Vec<_>>();
                        (name.clone(), entries)
                    })
                    .collect::<Vec<_>>();
                for (name, entries) in reexported_values {
                    for entry in entries {
                        self.push_import_value(
                            module,
                            name.clone(),
                            ImportedValueDecl {
                                order: alias.order,
                                def: entry.def,
                                vis: alias.vis,
                                private_origin: alias.private_origin.or(entry.private_origin),
                            },
                        );
                    }
                }
                let reexported_types = self.nodes[target.0]
                    .import_types
                    .iter()
                    .map(|(name, entries)| {
                        let entries = entries
                            .iter()
                            .filter(|entry| {
                                self.import_entry_allows(
                                    module,
                                    target,
                                    entry.vis,
                                    entry.private_origin,
                                    visibility,
                                )
                            })
                            .cloned()
                            .collect::<Vec<_>>();
                        (name.clone(), entries)
                    })
                    .collect::<Vec<_>>();
                for (name, entries) in reexported_types {
                    for entry in entries {
                        self.push_import_type(
                            module,
                            name.clone(),
                            ImportedTypeDecl {
                                order: alias.order,
                                decl: entry.decl,
                                vis: alias.vis,
                                private_origin: alias.private_origin.or(entry.private_origin),
                            },
                        );
                    }
                }
                let reexported_modules = self.nodes[target.0]
                    .import_modules
                    .iter()
                    .map(|(name, entries)| {
                        let entries = entries
                            .iter()
                            .filter(|entry| {
                                self.import_entry_allows(
                                    module,
                                    target,
                                    entry.vis,
                                    entry.private_origin,
                                    visibility,
                                )
                            })
                            .cloned()
                            .collect::<Vec<_>>();
                        (name.clone(), entries)
                    })
                    .collect::<Vec<_>>();
                for (name, entries) in reexported_modules {
                    // A glob's declared child module is its path-prefix surface. Same-named
                    // companion modules re-exported from that child must not replace it.
                    if direct_module_names.contains(&name) {
                        continue;
                    }
                    for entry in entries {
                        self.push_import_module(
                            module,
                            name.clone(),
                            ImportedModuleDecl {
                                order: alias.order,
                                module: entry.module,
                                vis: alias.vis,
                                private_origin: alias.private_origin.or(entry.private_origin),
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
        route: sources::UsePathRoute,
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
            let Some(target) =
                self.import_path_target_from_route(module, &op_path, route, alias.order)
            else {
                continue;
            };
            let Some(target) = target.value else {
                continue;
            };
            self.push_import_value(
                module,
                op_value_name(fixity, &name.0),
                ImportedValueDecl {
                    order: alias.order,
                    def: target.def,
                    vis: alias.vis,
                    private_origin: alias.private_origin.or(target.private_origin),
                },
            );
        }
    }
    fn import_path_target_from_route(
        &self,
        module: ModuleId,
        path: &ModulePath,
        route: sources::UsePathRoute,
        site: ModuleOrder,
    ) -> Option<ImportPathTarget> {
        let (base, path) = self.import_base_and_path_segments(module, path, route);
        self.import_path_target_for_import(module, base, &path, site, import_visibility(route))
    }
    fn record_private_import_access(
        &mut self,
        requester: ModuleId,
        path: &ModulePath,
        route: sources::UsePathRoute,
        site: ModuleOrder,
        alias: &AliasDecl,
    ) {
        let Some(source_span) = alias.source_span.clone() else {
            return;
        };
        let (base, path) = self.import_base_and_path_segments(requester, path, route);
        let Some((last, prefix)) = path.segments.split_last() else {
            return;
        };
        let access = if prefix.is_empty() {
            match self.lexical_value_at(requester, last, site) {
                Lookup::Private(access) => Some(access),
                Lookup::Found(_) | Lookup::Missing => {
                    match self.lexical_type_at(requester, last, site) {
                        Lookup::Private(access) => Some(access),
                        Lookup::Found(_) | Lookup::Missing => None,
                    }
                }
            }
        } else {
            match self.module_path_with_imports_from(base, prefix, site) {
                Lookup::Private(access) => Some(access),
                Lookup::Missing => None,
                Lookup::Found(target) => self
                    .value_at(requester, target, last, module_path_site())
                    .or_else(|| self.exported_value_at(requester, target, last))
                    .private_access()
                    .or_else(|| {
                        self.type_at(requester, target, last, module_path_site())
                            .or_else(|| self.exported_type_at(requester, target, last))
                            .private_access()
                    })
                    .or_else(|| {
                        self.module_at(requester, target, last, module_path_site())
                            .or_else(|| self.exported_module_at(requester, target, last))
                            .private_access()
                    }),
            }
        };
        if let Some(access) = access {
            self.push_import_privacy_diagnostic(ImportPrivacyDiagnostic {
                access,
                source_span,
            });
        }
    }
    fn import_base_module(&self, module: ModuleId, route: sources::UsePathRoute) -> ModuleId {
        match route {
            sources::UsePathRoute::Relative => module,
            sources::UsePathRoute::CurrentBand => {
                let band = self.module_band_path(module);
                if band == self.module_band_path(self.root_id()) {
                    return self.root_id();
                }
                self.module_by_path(band).unwrap_or_else(|| self.root_id())
            }
            sources::UsePathRoute::CurrentRealm { .. }
            | sources::UsePathRoute::SlashQualified { .. } => self.root_id(),
        }
    }
    fn import_base_and_path_segments(
        &self,
        module: ModuleId,
        path: &ModulePath,
        route: sources::UsePathRoute,
    ) -> (ModuleId, ModulePath) {
        if let Some(rest) = self.current_realm_root_alias_segments(route, &path.segments) {
            return (
                self.root_id(),
                ModulePath {
                    segments: rest.to_vec(),
                },
            );
        }
        (
            self.import_base_module(module, route),
            ModulePath {
                segments: path.segments.clone(),
            },
        )
    }
    fn current_realm_root_alias_segments<'a>(
        &self,
        route: sources::UsePathRoute,
        path: &'a [Name],
    ) -> Option<&'a [Name]> {
        let sources::UsePathRoute::CurrentRealm { band_segments } = route else {
            return None;
        };
        let root_band = self.module_band_path(self.root_id());
        if root_band.segments.is_empty() || band_segments != root_band.segments.len() {
            return None;
        }
        path.strip_prefix(root_band.segments.as_slice())
    }
    fn import_path_target_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        path: &ModulePath,
        site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ImportPathTarget> {
        let Some((last, prefix)) = path.segments.split_last() else {
            return Some(ImportPathTarget {
                value: None,
                ty: None,
                module: Some(ImportModuleTarget {
                    module,
                    private_origin: None,
                }),
            });
        };
        if prefix.is_empty() {
            return Some(ImportPathTarget {
                value: self
                    .raw_lexical_value_target_for_import(requester, module, last, site, visibility),
                ty: self
                    .raw_lexical_type_target_for_import(requester, module, last, site, visibility),
                module: self.raw_lexical_module_target_for_import(
                    requester, module, last, site, visibility,
                ),
            });
        }

        let target =
            self.module_path_from_for_import(requester, module, prefix, site, visibility)?;
        Some(ImportPathTarget {
            value: self
                .value_target_at_for_import(requester, target, last, module_path_site(), visibility)
                .or_else(|| {
                    self.exported_value_target_at_for_import(requester, target, last, visibility)
                }),
            ty: self
                .type_target_at_for_import(requester, target, last, module_path_site(), visibility)
                .or_else(|| {
                    self.exported_type_target_at_for_import(requester, target, last, visibility)
                }),
            module: self
                .module_target_at_for_import(
                    requester,
                    target,
                    last,
                    module_path_site(),
                    visibility,
                )
                .or_else(|| {
                    self.exported_module_target_at_for_import(requester, target, last, visibility)
                }),
        })
    }
    fn module_path_from_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        path: &[Name],
        site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ModuleId> {
        let Some((first, rest)) = path.split_first() else {
            return Some(module);
        };
        let mut current =
            self.raw_lexical_module_at_for_import(requester, module, first, site, visibility)?;
        for segment in rest {
            current = self.module_at_for_import(
                requester,
                current,
                segment,
                module_path_site(),
                visibility,
            )?;
        }
        Some(current)
    }
    /// `value_path_at` / `type_path_at` 用の prefix 降下。再エクスポート（import view）も辿る。
    /// alias 展開で使う `raw_module_path_from` は import view 構築順に依存しないよう
    /// 意図的に raw のままにしてあるので、こちらと混ぜない。
    pub fn module_path_with_imports_from(
        &self,
        module: ModuleId,
        path: &[Name],
        site: ModuleOrder,
    ) -> Lookup<ModuleId> {
        let Some((first, rest)) = path.split_first() else {
            return Lookup::Found(module);
        };
        let mut current = match self.lexical_module_with_imports_at(module, first, site) {
            Lookup::Found(module) => module,
            Lookup::Private(access) => return Lookup::Private(access),
            Lookup::Missing => return Lookup::Missing,
        };
        for segment in rest {
            current = match self.module_at(module, current, segment, module_path_site()) {
                Lookup::Found(module) => module,
                Lookup::Private(access) => return Lookup::Private(access),
                Lookup::Missing => match self.exported_module_at(module, current, segment) {
                    Lookup::Found(module) => module,
                    Lookup::Private(access) => return Lookup::Private(access),
                    Lookup::Missing => return Lookup::Missing,
                },
            };
        }
        Lookup::Found(current)
    }
    pub(super) fn lexical_module_with_imports_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Lookup<ModuleId> {
        let requester = module;
        loop {
            match self.module_at(requester, module, name, site) {
                Lookup::Found(found) => return Lookup::Found(found),
                Lookup::Private(access) => return Lookup::Private(access),
                Lookup::Missing => {}
            }
            match self.imported_module_at(requester, module, name, site) {
                Lookup::Found(found) => return Lookup::Found(found),
                Lookup::Private(access) => return Lookup::Private(access),
                Lookup::Missing => {}
            }
            let Some(parent) = self.nodes[module.0].parent else {
                return Lookup::Missing;
            };
            module = parent.module;
            site = parent.order;
        }
    }
    fn raw_lexical_value_target_for_import(
        &self,
        requester: ModuleId,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ImportValueTarget> {
        loop {
            if let Some(target) =
                self.value_target_at_for_import(requester, module, name, site, visibility)
            {
                return Some(target);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    fn raw_lexical_type_target_for_import(
        &self,
        requester: ModuleId,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ImportTypeTarget> {
        loop {
            if let Some(target) =
                self.type_target_at_for_import(requester, module, name, site, visibility)
            {
                return Some(target);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    fn raw_lexical_module_at_for_import(
        &self,
        requester: ModuleId,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ModuleId> {
        loop {
            if let Some(found) =
                self.module_at_for_import(requester, module, name, site, visibility)
            {
                return Some(found);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    fn raw_lexical_module_target_for_import(
        &self,
        requester: ModuleId,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ImportModuleTarget> {
        loop {
            if let Some(target) =
                self.module_target_at_for_import(requester, module, name, site, visibility)
            {
                return Some(target);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    fn value_target_at_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ImportValueTarget> {
        let decl = self.select_decl_for_import(
            requester,
            module,
            self.nodes[module.0].values.get(name)?,
            site,
            visibility,
        )?;
        let ModuleDeclKind::Value { def } = decl.kind else {
            return None;
        };
        Some(ImportValueTarget {
            def,
            private_origin: decl.private_origin,
        })
    }
    fn type_target_at_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ImportTypeTarget> {
        let decl = self.select_decl_for_import(
            requester,
            module,
            self.nodes[module.0].types.get(name)?,
            site,
            visibility,
        )?;
        let ModuleDeclKind::Type { id, kind } = decl.kind else {
            return None;
        };
        Some(ImportTypeTarget {
            decl: ModuleTypeDecl {
                name: decl.name.clone(),
                vis: decl.vis,
                order: decl.order,
                module,
                id,
                kind,
                private_origin: decl.private_origin,
            },
            private_origin: decl.private_origin,
        })
    }
    fn module_at_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ModuleId> {
        let decl = self.select_decl_for_import(
            requester,
            module,
            self.nodes[module.0].modules.get(name)?,
            site,
            visibility,
        )?;
        let ModuleDeclKind::Module { module: child, .. } = decl.kind else {
            return None;
        };
        if matches!(visibility, ImportVisibility::SameBand)
            && !same_band_allows_module_step(
                self.module_band_path(module),
                self.module_band_path(child),
            )
        {
            return None;
        }
        Some(child)
    }
    fn module_target_at_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<ImportModuleTarget> {
        let decl = self.select_decl_for_import(
            requester,
            module,
            self.nodes[module.0].modules.get(name)?,
            site,
            visibility,
        )?;
        let ModuleDeclKind::Module { module: child, .. } = decl.kind else {
            return None;
        };
        if matches!(visibility, ImportVisibility::SameBand)
            && !same_band_allows_module_step(
                self.module_band_path(module),
                self.module_band_path(child),
            )
        {
            return None;
        }
        Some(ImportModuleTarget {
            module: child,
            private_origin: decl.private_origin,
        })
    }
    pub(super) fn imported_value_at(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Lookup<DefId> {
        match self.select_import(
            requester,
            module,
            self.nodes[module.0]
                .import_values
                .get(name)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            site,
            NamespaceKind::Value,
        ) {
            Lookup::Found(decl) => Lookup::Found(decl.def),
            Lookup::Private(access) => Lookup::Private(access),
            Lookup::Missing => Lookup::Missing,
        }
    }

    pub(super) fn imported_type_at(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Lookup<ModuleTypeDecl> {
        match self.select_import(
            requester,
            module,
            self.nodes[module.0]
                .import_types
                .get(name)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            site,
            NamespaceKind::Type,
        ) {
            Lookup::Found(decl) => Lookup::Found(decl.decl.clone()),
            Lookup::Private(access) => Lookup::Private(access),
            Lookup::Missing => Lookup::Missing,
        }
    }
    pub(super) fn imported_module_at(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Lookup<ModuleId> {
        match self.select_import(
            requester,
            module,
            self.nodes[module.0]
                .import_modules
                .get(name)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            site,
            NamespaceKind::Module,
        ) {
            Lookup::Found(decl) => Lookup::Found(decl.module),
            Lookup::Private(access) => Lookup::Private(access),
            Lookup::Missing => Lookup::Missing,
        }
    }
    /// 外の module から見える import entry（再エクスポート）。`my use` だけはファイル内
    /// private なので外からは見えない。our は band 内可視、pub は band 境界用（band は未実装）。
    pub(super) fn exported_value_at(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
    ) -> Lookup<DefId> {
        match self.select_import(
            requester,
            module,
            self.nodes[module.0]
                .import_values
                .get(name)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            module_path_site(),
            NamespaceKind::Value,
        ) {
            Lookup::Found(entry) if entry.vis != Vis::My => Lookup::Found(entry.def),
            Lookup::Found(_) | Lookup::Missing => Lookup::Missing,
            Lookup::Private(access) => Lookup::Private(access),
        }
    }
    pub(super) fn exported_type_at(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
    ) -> Lookup<ModuleTypeDecl> {
        match self.select_import(
            requester,
            module,
            self.nodes[module.0]
                .import_types
                .get(name)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            module_path_site(),
            NamespaceKind::Type,
        ) {
            Lookup::Found(entry) if entry.vis != Vis::My => Lookup::Found(entry.decl.clone()),
            Lookup::Found(_) | Lookup::Missing => Lookup::Missing,
            Lookup::Private(access) => Lookup::Private(access),
        }
    }
    pub(super) fn exported_module_at(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
    ) -> Lookup<ModuleId> {
        match self.select_import(
            requester,
            module,
            self.nodes[module.0]
                .import_modules
                .get(name)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            module_path_site(),
            NamespaceKind::Module,
        ) {
            Lookup::Found(entry) if entry.vis != Vis::My => Lookup::Found(entry.module),
            Lookup::Found(_) | Lookup::Missing => Lookup::Missing,
            Lookup::Private(access) => Lookup::Private(access),
        }
    }
    fn exported_value_target_at_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        visibility: ImportVisibility,
    ) -> Option<ImportValueTarget> {
        self.nodes[module.0]
            .import_values
            .get(name)?
            .iter()
            .find(|entry| {
                self.import_entry_allows(
                    requester,
                    module,
                    entry.vis,
                    entry.private_origin,
                    visibility,
                )
            })
            .map(|entry| ImportValueTarget {
                def: entry.def,
                private_origin: entry.private_origin,
            })
    }
    fn exported_type_target_at_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        visibility: ImportVisibility,
    ) -> Option<ImportTypeTarget> {
        self.nodes[module.0]
            .import_types
            .get(name)?
            .iter()
            .find(|entry| {
                self.import_entry_allows(
                    requester,
                    module,
                    entry.vis,
                    entry.private_origin,
                    visibility,
                )
            })
            .map(|entry| ImportTypeTarget {
                decl: entry.decl.clone(),
                private_origin: entry.private_origin,
            })
    }
    fn exported_module_target_at_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        name: &Name,
        visibility: ImportVisibility,
    ) -> Option<ImportModuleTarget> {
        self.nodes[module.0]
            .import_modules
            .get(name)?
            .iter()
            .find(|entry| {
                self.import_entry_allows(
                    requester,
                    module,
                    entry.vis,
                    entry.private_origin,
                    visibility,
                )
            })
            .map(|entry| ImportModuleTarget {
                module: entry.module,
                private_origin: entry.private_origin,
            })
    }
    fn module_value_imports_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        visibility: ImportVisibility,
    ) -> Vec<ModuleValueDecl> {
        self.module_value_decls(module)
            .into_iter()
            .filter(|decl| self.import_vis_allows(requester, module, decl.vis, visibility))
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
                    private_origin: decl.private_origin,
                }),
                ModuleDeclKind::Type { .. } | ModuleDeclKind::Module { .. } => None,
            })
            .collect()
    }
    fn module_type_imports_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        visibility: ImportVisibility,
    ) -> Vec<ModuleTypeDecl> {
        self.module_type_decls(module)
            .into_iter()
            .filter(|decl| self.import_vis_allows(requester, module, decl.vis, visibility))
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
                    private_origin: decl.private_origin,
                }),
                ModuleDeclKind::Value { .. } | ModuleDeclKind::Module { .. } => None,
            })
            .collect()
    }
    fn module_module_imports_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        visibility: ImportVisibility,
    ) -> Vec<ModuleChildDecl> {
        self.module_child_decls(module)
            .into_iter()
            .filter(|decl| self.import_vis_allows(requester, module, decl.vis, visibility))
            .filter(|decl| {
                !matches!(visibility, ImportVisibility::SameBand)
                    || same_band_allows_module_step(
                        self.module_band_path(module),
                        self.module_band_path(decl.module),
                    )
            })
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
                    private_origin: decl.private_origin,
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
                    private_origin: entry.private_origin,
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
                    private_origin: entry.private_origin,
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
                    private_origin: entry.private_origin,
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
                        private_origin: decl.private_origin,
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
                        private_origin: decl.private_origin,
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
                        private_origin: decl.private_origin,
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
        source_span: Option<SourceSpan>,
    ) -> ModuleDeclId {
        let order = self.next_order(module);
        let private_origin = self.private_origin_for(module, vis, source_span);
        let node = &mut self.nodes[module.0];
        let id = ModuleDeclId(node.decls.len());
        node.decls.push(ModuleDecl {
            name,
            vis,
            order,
            kind,
            private_origin,
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
        requester: ModuleId,
        module: ModuleId,
        decls: &[ModuleDeclId],
        site: ModuleOrder,
        kind: NamespaceKind,
        route: VisibilityRoute,
    ) -> Lookup<&ModuleDecl> {
        let node = &self.nodes[module.0];
        let mut candidates = decls
            .iter()
            .map(|decl| &node.decls[decl.0])
            .collect::<Vec<_>>();
        candidates.sort_by(
            |left, right| match (left.order <= site, right.order <= site) {
                (true, true) => right.order.cmp(&left.order),
                (false, false) => left.order.cmp(&right.order),
                (true, false) => std::cmp::Ordering::Less,
                (false, true) => std::cmp::Ordering::Greater,
            },
        );
        let mut private = None;
        for decl in candidates {
            if self.visibility_allows(requester, module, decl.vis, route) {
                return Lookup::Found(decl);
            }
            if decl.vis == Vis::My {
                private.get_or_insert_with(|| PrivateAccess {
                    kind,
                    name: decl.name.clone(),
                    origin: decl
                        .private_origin
                        .expect("my declaration has private origin"),
                });
            }
        }
        private.map_or(Lookup::Missing, Lookup::Private)
    }

    fn select_decl_for_import(
        &self,
        requester: ModuleId,
        module: ModuleId,
        decls: &[ModuleDeclId],
        site: ModuleOrder,
        visibility: ImportVisibility,
    ) -> Option<&ModuleDecl> {
        let node = &self.nodes[module.0];
        decls
            .iter()
            .map(|decl| &node.decls[decl.0])
            .filter(|decl| decl.order <= site)
            .filter(|decl| self.import_vis_allows(requester, module, decl.vis, visibility))
            .max_by_key(|decl| decl.order)
            .or_else(|| {
                decls
                    .iter()
                    .map(|decl| &node.decls[decl.0])
                    .filter(|decl| decl.order > site)
                    .filter(|decl| self.import_vis_allows(requester, module, decl.vis, visibility))
                    .min_by_key(|decl| decl.order)
            })
    }
    fn select_import<'a, T>(
        &self,
        requester: ModuleId,
        module: ModuleId,
        imports: &'a [T],
        site: ModuleOrder,
        kind: NamespaceKind,
    ) -> Lookup<&'a T>
    where
        T: ImportOrder,
    {
        let mut candidates = imports.iter().collect::<Vec<_>>();
        candidates.sort_by(
            |left, right| match (left.order() <= site, right.order() <= site) {
                (true, true) => right.order().cmp(&left.order()),
                (false, false) => left.order().cmp(&right.order()),
                (true, false) => std::cmp::Ordering::Less,
                (false, true) => std::cmp::Ordering::Greater,
            },
        );
        let mut private = None;
        for entry in candidates {
            let allowed =
                self.visibility_allows(requester, module, entry.vis(), VisibilityRoute::SameBand)
                    && entry.private_origin().is_none_or(|origin| {
                        self.is_descendant_or_same(requester, self.private_origin(origin).scope)
                    });
            if allowed {
                return Lookup::Found(entry);
            }
            if let Some(origin) = entry.private_origin() {
                private.get_or_insert_with(|| PrivateAccess {
                    kind,
                    name: Name("<import>".to_string()),
                    origin,
                });
            }
        }
        private.map_or(Lookup::Missing, Lookup::Private)
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

fn import_visibility(route: sources::UsePathRoute) -> ImportVisibility {
    match route {
        sources::UsePathRoute::Relative | sources::UsePathRoute::CurrentBand => {
            ImportVisibility::SameBand
        }
        sources::UsePathRoute::CurrentRealm { .. }
        | sources::UsePathRoute::SlashQualified { .. } => ImportVisibility::CrossBand,
    }
}

impl ModuleTable {
    fn import_vis_allows(
        &self,
        requester: ModuleId,
        declaring_module: ModuleId,
        vis: Vis,
        route: ImportVisibility,
    ) -> bool {
        self.visibility_allows(requester, declaring_module, vis, route)
    }

    fn import_entry_allows(
        &self,
        requester: ModuleId,
        declaring_module: ModuleId,
        vis: Vis,
        private_origin: Option<PrivateOriginId>,
        route: ImportVisibility,
    ) -> bool {
        private_origin.map_or_else(
            || self.import_vis_allows(requester, declaring_module, vis, route),
            |origin| self.is_descendant_or_same(requester, self.private_origin(origin).scope),
        )
    }
}
