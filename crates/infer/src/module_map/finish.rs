use super::*;

impl Lower {
    pub(super) fn register_type_companion(
        &mut self,
        node: &Cst,
        module: ModuleId,
        name: Name,
        owner: TypeDeclId,
        vis: Vis,
        children: &mut Vec<DefId>,
    ) {
        let Some(body) = type_with_body(node) else {
            return;
        };
        let (def, companion, created) = self.ensure_child_module(module, name, vis);
        self.modules.set_type_companion(owner, companion);
        let companion_children = self.register_type_companion_block(&body, companion, owner);
        self.append_module_children(def, companion_children);
        if created {
            children.push(def);
        }
    }

    pub(super) fn register_type_companion_block(
        &mut self,
        block: &Cst,
        module: ModuleId,
        owner: TypeDeclId,
    ) -> Vec<DefId> {
        let mut children = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => {
                    if let Some(method) = type_method_binding(&child) {
                        let vis = binding_vis(&child);
                        let def = self.arena.defs.fresh();
                        self.arena.defs.set(
                            def,
                            Def::Let {
                                vis,
                                scheme: None,
                                body: None,
                                children: Vec::new(),
                            },
                        );
                        let value_name = type_method_value_name(&method.name, method.receiver_kind);
                        let order = self.modules.insert_value(module, value_name, def, vis);
                        self.modules.insert_type_method(TypeMethodDecl {
                            owner,
                            name: method.name,
                            receiver: method.receiver,
                            receiver_kind: method.receiver_kind,
                            def,
                            vis,
                            order,
                        });
                        children.push(def);
                        self.register_local_var_act_copies_in_binding(&child, module, def);
                    } else if let Some(name) = binding_name(&child) {
                        let vis = binding_vis(&child);
                        let def = self.arena.defs.fresh();
                        self.arena.defs.set(
                            def,
                            Def::Let {
                                vis,
                                scheme: None,
                                body: None,
                                children: Vec::new(),
                            },
                        );
                        self.modules.insert_value(module, name, def, vis);
                        children.push(def);
                        self.register_local_var_act_copies_in_binding(&child, module, def);
                    }
                }
                SyntaxKind::CastDecl => {
                    self.register_cast_decl(&child, module);
                }
                SyntaxKind::ModDecl => {
                    if let Some(name) = mod_name(&child) {
                        let vis = vis_of(&child);
                        let (def, sub, created) = self.ensure_child_module(module, name, vis);
                        let sub_children = self.register_mod_body(&child, sub);
                        self.append_module_children(def, sub_children);
                        if created {
                            children.push(def);
                        }
                    }
                }
                SyntaxKind::UseDecl => {
                    let vis = vis_of(&child);
                    if let Some(name) = use_mod_name(&child) {
                        let (def, _, created) = self.ensure_child_module(module, name, vis);
                        if created {
                            children.push(def);
                        }
                    }
                    for import in sources::use_imports(&child) {
                        self.modules.add_alias(module, import, vis);
                    }
                }
                SyntaxKind::StructDecl
                    if type_decl_name(&child).is_some_and(|name| name.0 == "self") => {}
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl
                | SyntaxKind::RoleDecl
                | SyntaxKind::ActDecl => {
                    self.register_type_namespace_decl(&child, module, &mut children);
                }
                _ => {}
            }
        }
        children
    }

    /// ModDecl の body（BraceGroup / IndentBlock）に降りて定義を採番する。
    /// 外部 mod（Semicolon）や body 無しでは空を返す。
    pub(super) fn register_mod_body(&mut self, mod_decl: &Cst, sub: ModuleId) -> Vec<DefId> {
        for child in mod_decl.children() {
            if matches!(
                child.kind(),
                SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
            ) {
                return self.register_block(&child, sub);
            }
        }
        Vec::new()
    }

    pub(super) fn ensure_child_module(
        &mut self,
        module: ModuleId,
        name: Name,
        vis: Vis,
    ) -> (DefId, ModuleId, bool) {
        if let Some(existing) = self.modules.first_module_decl(module, &name) {
            return (existing.def, existing.module, false);
        }

        let def = self.arena.defs.fresh();
        let sub = self.modules.new_module();
        self.arena.defs.set(
            def,
            Def::Mod {
                vis,
                children: Vec::new(),
            },
        );
        self.modules.insert_module(module, name, sub, def, vis);
        (def, sub, true)
    }

    pub(super) fn set_module_children(&mut self, def: DefId, children: Vec<DefId>) {
        let Some(Def::Mod { children: slot, .. }) = self.arena.defs.get_mut(def) else {
            return;
        };
        *slot = children;
    }

    pub(super) fn append_module_children(&mut self, def: DefId, children: Vec<DefId>) {
        let Some(Def::Mod { children: slot, .. }) = self.arena.defs.get_mut(def) else {
            return;
        };
        slot.extend(children);
    }

    pub(super) fn append_created_module_to_parent(&mut self, module: ModuleId, def: DefId) {
        if module == self.modules.root_id() {
            self.arena.roots.push(def);
            return;
        }
        let Some(parent_def) = self.modules.module_def(module) else {
            return;
        };
        self.append_module_children(parent_def, vec![def]);
    }

    pub(super) fn finalize_act_copies(&mut self) {
        let ids = self.modules.act_copies.keys().copied().collect::<Vec<_>>();
        for id in ids {
            self.finalize_act_copy(id);
        }
        let synthetic_ids = self.modules.synthetic_var_act_copy_ids();
        for id in synthetic_ids {
            self.finalize_synthetic_var_act_copy(id);
        }
        let synthetic_sub_label_ids = self.modules.synthetic_sub_label_act_copy_ids();
        for id in synthetic_sub_label_ids {
            self.finalize_synthetic_sub_label_act_copy(id);
        }
    }

    pub(super) fn finalize_act_copy(&mut self, id: TypeDeclId) {
        let Some(dest) = self.modules.type_decl_by_id(id) else {
            return;
        };
        let Some(resolved) = self.resolve_act_copy(&dest) else {
            return;
        };
        let own_body = self.modules.act_template(id).and_then(act_decl_body);
        self.materialize_act_copy(id, &dest, resolved, own_body, true);
    }

    pub(super) fn finalize_synthetic_var_act_copy(&mut self, id: TypeDeclId) {
        let Some(dest) = self.modules.type_decl_by_id(id) else {
            return;
        };
        let Some(source) = self.std_var_act_decl() else {
            return;
        };
        let source_type_vars = self
            .modules
            .act_template(source.id)
            .map(act_type_var_names)
            .unwrap_or_default();
        let type_var_aliases = source_type_vars
            .into_iter()
            .map(|name| (name.clone(), name))
            .collect();
        self.materialize_act_copy(
            id,
            &dest,
            ResolvedActCopyDecl {
                source: source.id,
                type_var_aliases,
            },
            None,
            false,
        );
    }

    pub(super) fn finalize_synthetic_sub_label_act_copy(&mut self, id: TypeDeclId) {
        let Some(dest) = self.modules.type_decl_by_id(id) else {
            return;
        };
        let Some(source) = self.std_label_sub_act_decl() else {
            return;
        };
        let source_type_vars = self
            .modules
            .act_template(source.id)
            .map(act_type_var_names)
            .unwrap_or_default();
        let type_var_aliases = source_type_vars
            .into_iter()
            .map(|name| (name.clone(), name))
            .collect();
        self.materialize_act_copy(
            id,
            &dest,
            ResolvedActCopyDecl {
                source: source.id,
                type_var_aliases,
            },
            None,
            false,
        );
    }

    pub(super) fn materialize_act_copy(
        &mut self,
        id: TypeDeclId,
        dest: &ModuleTypeDecl,
        resolved: ResolvedActCopyDecl,
        own_body: Option<Cst>,
        attach_to_parent: bool,
    ) {
        let Some(source_body) = self
            .modules
            .act_template(resolved.source)
            .and_then(act_decl_body)
        else {
            return;
        };
        self.modules.set_resolved_act_copy(id, resolved);

        let mut ops = act_operation_signatures_from_body(&source_body);
        push_unique_act_ops(
            &mut ops,
            self.modules.act_ops.get(&id).cloned().unwrap_or_default(),
        );
        self.modules.set_act_ops(id, ops);

        let (def, companion, created) =
            self.ensure_child_module(dest.module, dest.name.clone(), dest.vis);
        self.modules.set_type_companion(id, companion);
        let mut companion_children = self.register_act_companion_block(&source_body, companion, id);
        if let Some(own_body) = own_body {
            companion_children.extend(self.register_act_companion_block(&own_body, companion, id));
        }
        self.append_module_children(def, companion_children);
        if created && attach_to_parent {
            self.append_created_module_to_parent(dest.module, def);
        }
    }

    pub(super) fn std_var_act_decl(&self) -> Option<ModuleTypeDecl> {
        let path = crate::std_paths::control_var_var_act()
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        self.modules
            .type_path_at(self.modules.root_id(), &path, module_path_site())
            .filter(|decl| decl.kind == ModuleTypeKind::Act)
    }

    pub(super) fn std_label_sub_act_decl(&self) -> Option<ModuleTypeDecl> {
        let path = crate::std_paths::control_flow_label_sub_act()
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        self.modules
            .type_path_at(self.modules.root_id(), &path, module_path_site())
            .filter(|decl| decl.kind == ModuleTypeKind::Act)
    }

    pub(super) fn resolve_act_copy(&self, dest: &ModuleTypeDecl) -> Option<ResolvedActCopyDecl> {
        let copy = self.modules.act_copy(dest.id)?;
        let resolver = ActTypeResolver::new(&self.modules, dest.module, dest.order);
        let source_use = resolver.resolve_act_use(&copy.source).ok()?;
        let source_decl = source_use.decl;
        let source_type_vars = self
            .modules
            .act_template(source_decl.id)
            .map(act_type_var_names)
            .unwrap_or_default();
        let type_var_aliases = source_type_vars
            .into_iter()
            .zip(source_use.args.iter())
            .filter_map(|(source, arg)| act_type_var_arg_name(arg).map(|target| (source, target)))
            .collect();
        Some(ResolvedActCopyDecl {
            source: source_decl.id,
            type_var_aliases,
        })
    }

    pub(crate) fn module_path_target(&self, path: &ModulePath) -> Option<ModulePathTarget> {
        let mut target = ModulePathTarget {
            module: self.modules.root_id(),
            def: None,
        };
        for segment in &path.segments {
            let decl = self.modules.first_module_decl(target.module, segment)?;
            target = ModulePathTarget {
                module: decl.module,
                def: Some(decl.def),
            };
        }
        Some(target)
    }
}
