use super::*;

mod finish;

impl Lower {
    fn new() -> Self {
        Self {
            arena: PolyArena::new(),
            modules: ModuleTable::new(),
            source_file: ModulePath::default(),
        }
    }

    fn source_span(&self, range: Option<SourceRange>) -> Option<SourceSpan> {
        range.map(|range| SourceSpan {
            file: self.source_file.clone(),
            range,
        })
    }

    fn set_def_source_range(&mut self, def: DefId, range: SourceRange) {
        self.modules.set_def_source_span(
            def,
            SourceSpan {
                file: self.source_file.clone(),
                range,
            },
        );
    }

    /// ブロック（root / IndentBlock / BraceGroup）の直下を走査して定義を採番する。
    /// 採番した DefId の並びを返す（呼び出し側が roots / Mod.children に入れる）。
    fn register_block(&mut self, block: &Cst, module: ModuleId) -> Vec<DefId> {
        let mut children = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => {
                    self.register_binding_values(&child, module, &mut children);
                }
                SyntaxKind::Expr => {
                    self.register_root_expr(&child, module);
                }
                SyntaxKind::ModDecl => {
                    if let Some(name) = mod_name(&child) {
                        let vis = vis_of(&child);
                        let (def, sub, created) = self.ensure_child_module(module, name, vis);
                        let sub_children = self.register_mod_body(&child, sub);
                        self.set_module_children(def, sub_children);
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
                SyntaxKind::OpDef => {
                    if let Some(info) = op_def_info(&child) {
                        let def = self.arena.defs.fresh();
                        self.arena.defs.set(
                            def,
                            Def::Let {
                                vis: info.vis,
                                scheme: None,
                                body: None,
                                children: Vec::new(),
                            },
                        );
                        let source_span = self.source_span(Some(info.source_range));
                        self.modules.insert_value_with_span(
                            module,
                            info.name,
                            def,
                            info.vis,
                            source_span,
                        );
                        if info.lazy {
                            self.modules.mark_lazy_op(def);
                        }
                        children.push(def);
                    }
                }
                SyntaxKind::CastDecl => {
                    self.register_cast_decl(&child, module);
                }
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl
                | SyntaxKind::RoleDecl
                | SyntaxKind::ActDecl => {
                    self.register_type_namespace_decl(&child, module, &mut children);
                }
                // 型定義系の本体、Cast は後で。
                SyntaxKind::ImplDecl => {
                    if let Some(def) = self.register_role_impl_decl(&child, module) {
                        children.push(def);
                    }
                }
                _ => {}
            }
        }
        children
    }

    fn register_binding_values(
        &mut self,
        binding: &Cst,
        module: ModuleId,
        children: &mut Vec<DefId>,
    ) {
        let vis = binding_vis(binding);
        for name in binding_value_names(binding) {
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
            let source_span = self.source_span(source_range_for_name(binding, &name));
            self.modules
                .insert_value_with_span(module, name, def, vis, source_span);
            children.push(def);
            self.register_local_var_act_copies_in_binding(binding, module, def);
        }
    }

    fn register_root_expr(&mut self, expr: &Cst, module: ModuleId) {
        if !expr_needs_synthetic_owner(expr) {
            self.modules.push_root_expr_owner(module, None);
            return;
        }
        let owner = self.arena.defs.fresh();
        self.set_def_source_range(owner, node_source_range(expr));
        self.register_local_var_act_copies_in_expr(expr, module, owner);
        self.modules.push_root_expr_owner(module, Some(owner));
    }

    fn register_cast_decl(&mut self, node: &Cst, module: ModuleId) -> DefId {
        let def = self.register_synthetic_let(Vis::My);
        self.set_def_source_range(def, node_source_range(node));
        let order = self.modules.next_order(module);
        self.modules
            .insert_cast_decl(CastDecl { def, module, order });
        if let Some(body) = cast_body_expr(node) {
            self.register_local_var_act_copies_in_expr(&body, module, def);
        }
        def
    }

    fn register_role_impl_decl(&mut self, node: &Cst, module: ModuleId) -> Option<DefId> {
        let order = self.modules.next_order(module);
        let def = self.arena.defs.fresh();
        self.arena.defs.set(
            def,
            Def::Mod {
                vis: Vis::My,
                children: Vec::new(),
            },
        );
        let body_module = self.modules.new_anonymous_child_module(module, order);
        let (children, methods) = role_impl_body(node)
            .map(|body| self.register_role_impl_block(&body, body_module))
            .unwrap_or_default();
        self.set_module_children(def, children);
        self.modules.insert_role_impl(RoleImplDecl {
            def,
            module,
            body_module,
            order,
            methods,
        });
        Some(def)
    }

    fn register_role_impl_block(
        &mut self,
        block: &Cst,
        module: ModuleId,
    ) -> (Vec<DefId>, Vec<RoleImplMethodDecl>) {
        let mut children = Vec::new();
        let mut methods = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => {
                    if let Some(method) = role_method_binding(&child) {
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
                        let source_span =
                            self.source_span(source_range_for_name(&child, &method.name));
                        let order = self.modules.insert_value_with_span(
                            module,
                            method.name.clone(),
                            def,
                            vis,
                            source_span,
                        );
                        children.push(def);
                        if vis != Vis::My {
                            methods.push(RoleImplMethodDecl {
                                name: method.name,
                                receiver: method.receiver,
                                def,
                                vis,
                                order,
                            });
                        }
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
                        let source_span = self.source_span(source_range_for_name(&child, &name));
                        self.modules
                            .insert_value_with_span(module, name, def, vis, source_span);
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
        (children, methods)
    }

    fn register_type_namespace_decl(
        &mut self,
        node: &Cst,
        module: ModuleId,
        children: &mut Vec<DefId>,
    ) {
        let (Some(name), Some(kind)) = (type_decl_name(node), module_type_kind(node.kind())) else {
            return;
        };
        let vis = vis_of(node);
        let id = self.modules.insert_type(module, name.clone(), kind, vis);
        if kind == ModuleTypeKind::Act {
            self.modules.set_act_template(id, node.clone());
            let copy = act_copy_decl(node);
            if let Some(copy) = copy {
                self.modules.set_act_copy(id, copy);
                self.modules.set_act_ops(id, act_operation_signatures(node));
            } else {
                self.modules.set_act_ops(id, act_operation_signatures(node));
                self.register_act_companion(node, module, name.clone(), id, vis, children);
            }
        }
        if kind == ModuleTypeKind::Role {
            self.modules.set_role_inputs(id, role_input_names(node));
            self.modules
                .set_role_associated(id, role_associated_names(node));
            self.register_role_companion(node, module, name.clone(), id, vis, children);
        }
        if matches!(
            kind,
            ModuleTypeKind::TypeAlias
                | ModuleTypeKind::Struct
                | ModuleTypeKind::Enum
                | ModuleTypeKind::Error
        ) {
            self.register_type_constructors(node, module, kind, id, name.clone(), vis, children);
            self.register_type_companion(node, module, name, id, vis, children);
        }
    }

    fn register_local_var_act_copies_in_binding(
        &mut self,
        binding: &Cst,
        module: ModuleId,
        owner: DefId,
    ) {
        let Some(body) = binding_body_expr(binding) else {
            return;
        };
        self.register_local_var_act_copies_in_expr(&body, module, owner);
    }

    fn register_local_var_act_copies_in_expr(
        &mut self,
        body: &Cst,
        module: ModuleId,
        owner: DefId,
    ) {
        let mut local_var_index = 0;
        for local in body
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Binding)
        {
            for name in local_var_act_names(&local) {
                self.register_synthetic_var_act_copy(module, owner, name, local_var_index);
                local_var_index += 1;
            }
        }
        for (index, label) in body
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Expr)
            .filter_map(|node| sub_syntax_label(&node))
            .enumerate()
        {
            self.register_synthetic_sub_label_act_copy(module, owner, label, index);
        }
    }

    fn register_synthetic_var_act_copy(
        &mut self,
        module: ModuleId,
        owner: DefId,
        source: Name,
        index: usize,
    ) {
        let internal_name = synthetic_var_act_internal_name(&source, owner, index);
        let id = self
            .modules
            .insert_type(module, internal_name, ModuleTypeKind::Act, Vis::My);
        self.modules.set_synthetic_var_act_copy(id);
        self.modules
            .push_synthetic_var_act_use(owner, SyntheticVarActUse { source, act: id });
    }

    fn register_synthetic_sub_label_act_copy(
        &mut self,
        module: ModuleId,
        owner: DefId,
        label: Name,
        index: usize,
    ) {
        let internal_name = synthetic_sub_label_act_internal_name(&label, owner, index);
        let id = self
            .modules
            .insert_type(module, internal_name, ModuleTypeKind::Act, Vis::My);
        self.modules.set_synthetic_sub_label_act_copy(id);
        self.modules
            .push_synthetic_sub_label_act_use(owner, SyntheticSubLabelActUse { label, act: id });
    }

    fn register_type_constructors(
        &mut self,
        node: &Cst,
        module: ModuleId,
        kind: ModuleTypeKind,
        owner: TypeDeclId,
        name: Name,
        vis: Vis,
        children: &mut Vec<DefId>,
    ) {
        let type_vars = type_var_names(node);
        match kind {
            ModuleTypeKind::TypeAlias if type_self_struct_node(node).is_some() => {
                let def = self.register_synthetic_value(module, name, vis);
                children.push(def);
                if let Some(self_struct) = type_self_struct_node(node) {
                    let payload = ConstructorPayload::from_struct(&self_struct);
                    self.modules.insert_constructor(
                        def,
                        ConstructorDecl {
                            owner,
                            module,
                            type_vars: type_vars.clone(),
                            payload,
                        },
                    );
                    self.register_struct_field_methods(&self_struct, owner, vis);
                }
            }
            ModuleTypeKind::Struct => {
                let def = self.register_synthetic_value(module, name, vis);
                children.push(def);
                self.modules.insert_constructor(
                    def,
                    ConstructorDecl {
                        owner,
                        module,
                        type_vars: type_vars.clone(),
                        payload: ConstructorPayload::from_struct(node),
                    },
                );
                self.register_struct_field_methods(node, owner, vis);
            }
            ModuleTypeKind::Enum | ModuleTypeKind::Error => {
                // constructor は型 companion module（型と同名の子 module）に住む。
                // ファイルスコープへは `pub use foo::foo::*` の明示再エクスポートで
                // 持ち込む（std の流儀）。
                let (def, companion, created) = self.ensure_child_module(module, name, vis);
                self.modules.set_type_companion(owner, companion);
                let mut companion_children = Vec::new();
                for variant in enum_variant_nodes(node) {
                    let Some(variant_name) = enum_variant_name(&variant) else {
                        continue;
                    };
                    let source_span =
                        self.source_span(source_range_for_name(&variant, &variant_name));
                    let variant_def = self.register_synthetic_value_with_span(
                        companion,
                        variant_name,
                        vis,
                        source_span,
                    );
                    self.modules.insert_constructor(
                        variant_def,
                        ConstructorDecl {
                            owner,
                            module: companion,
                            type_vars: type_vars.clone(),
                            payload: ConstructorPayload::from_enum_variant(&variant),
                        },
                    );
                    companion_children.push(variant_def);
                }
                self.append_module_children(def, companion_children);
                if created {
                    children.push(def);
                }
            }
            ModuleTypeKind::TypeAlias | ModuleTypeKind::Role | ModuleTypeKind::Act => {}
        }
    }

    fn register_struct_field_methods(&mut self, node: &Cst, owner: TypeDeclId, vis: Vis) {
        for field in struct_field_nodes(node) {
            let Some(name) = struct_field_name(&field) else {
                continue;
            };
            for receiver_kind in [TypeMethodReceiver::Value, TypeMethodReceiver::Ref] {
                let def = self.register_synthetic_let(vis);
                if let Some(source_range) = source_range_for_name(&field, &name) {
                    self.set_def_source_range(def, source_range);
                }
                if receiver_kind == TypeMethodReceiver::Value {
                    self.arena.field_projections.insert(def);
                }
                self.modules.insert_type_field_method(TypeFieldMethodDecl {
                    owner,
                    name: name.clone(),
                    receiver_kind,
                    def,
                    vis,
                });
            }
        }
    }

    fn register_synthetic_value(&mut self, module: ModuleId, name: Name, vis: Vis) -> DefId {
        self.register_synthetic_value_with_span(module, name, vis, None)
    }

    fn register_synthetic_value_with_span(
        &mut self,
        module: ModuleId,
        name: Name,
        vis: Vis,
        source_span: Option<SourceSpan>,
    ) -> DefId {
        let def = self.register_synthetic_let(vis);
        self.modules
            .insert_value_with_span(module, name, def, vis, source_span);
        def
    }

    fn register_synthetic_let(&mut self, vis: Vis) -> DefId {
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
        def
    }

    fn register_role_companion(
        &mut self,
        node: &Cst,
        module: ModuleId,
        name: Name,
        owner: TypeDeclId,
        vis: Vis,
        children: &mut Vec<DefId>,
    ) {
        let Some(body) = role_decl_body(node) else {
            return;
        };
        let (def, companion, created) = self.ensure_child_module(module, name, vis);
        self.modules.set_type_companion(owner, companion);
        let companion_children = self.register_role_companion_block(&body, companion, owner);
        self.append_module_children(def, companion_children);
        if created {
            children.push(def);
        }
    }

    fn register_role_companion_block(
        &mut self,
        block: &Cst,
        module: ModuleId,
        owner: TypeDeclId,
    ) -> Vec<DefId> {
        let mut children = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => {
                    if let Some(method) = role_method_binding(&child) {
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
                        let source_span =
                            self.source_span(source_range_for_name(&child, &method.name));
                        let order = self.modules.insert_value_with_span(
                            module,
                            method.name.clone(),
                            def,
                            vis,
                            source_span,
                        );
                        self.modules.insert_role_method(RoleMethodDecl {
                            owner,
                            name: method.name,
                            receiver: method.receiver,
                            def,
                            vis,
                            order,
                            signature: binding_type_expr(&child),
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
                        let source_span = self.source_span(source_range_for_name(&child, &name));
                        self.modules
                            .insert_value_with_span(module, name, def, vis, source_span);
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
                SyntaxKind::TypeDecl => {}
                _ => {}
            }
        }
        children
    }

    fn register_act_companion(
        &mut self,
        node: &Cst,
        module: ModuleId,
        name: Name,
        owner: TypeDeclId,
        vis: Vis,
        children: &mut Vec<DefId>,
    ) {
        let Some(body) = act_decl_body(node) else {
            return;
        };
        let (def, companion, created) = self.ensure_child_module(module, name, vis);
        self.modules.set_type_companion(owner, companion);
        let companion_children = self.register_act_companion_block(&body, companion, owner);
        self.append_module_children(def, companion_children);
        if created {
            children.push(def);
        }
    }

    fn register_act_companion_block(
        &mut self,
        block: &Cst,
        module: ModuleId,
        owner: TypeDeclId,
    ) -> Vec<DefId> {
        let mut children = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding if act_operation_binding(&child) => {
                    let Some(name) = binding_name(&child) else {
                        continue;
                    };
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
                    let source_span = self.source_span(source_range_for_name(&child, &name));
                    self.modules.insert_value_with_span(
                        module,
                        name.clone(),
                        def,
                        vis,
                        source_span,
                    );
                    self.modules.insert_act_operation_def(owner, name, def);
                }
                SyntaxKind::Binding if type_method_binding(&child).is_some() => {
                    let Some(method) = type_method_binding(&child) else {
                        continue;
                    };
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
                    let value_name = act_method_value_name(&method.name, def);
                    let source_span = self.source_span(source_range_for_name(&child, &method.name));
                    let order = self.modules.insert_value_with_span(
                        module,
                        value_name,
                        def,
                        vis,
                        source_span,
                    );
                    self.modules.insert_act_method(ActMethodDecl {
                        owner,
                        name: method.name,
                        receiver: method.receiver,
                        def,
                        vis,
                        order,
                    });
                    children.push(def);
                    self.register_local_var_act_copies_in_binding(&child, module, def);
                }
                SyntaxKind::Binding => {
                    let Some(name) = binding_name(&child) else {
                        continue;
                    };
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
                    let source_span = self.source_span(source_range_for_name(&child, &name));
                    self.modules
                        .insert_value_with_span(module, name, def, vis, source_span);
                    children.push(def);
                    self.register_local_var_act_copies_in_binding(&child, module, def);
                }
                SyntaxKind::CastDecl => {
                    self.register_cast_decl(&child, module);
                }
                SyntaxKind::ModDecl => {
                    if let Some(name) = mod_name(&child) {
                        let (def, sub, created) =
                            self.ensure_child_module(module, name, vis_of(&child));
                        let sub_children = self.register_mod_body(&child, sub);
                        self.set_module_children(def, sub_children);
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
}

/// pass1 の入口。フルパース済み CST のモジュールマップを作る。
pub fn lower_module_map(root: &Cst) -> Lower {
    let mut lower = Lower::new();
    let root_module = lower.modules.root_id();
    let roots = lower.register_block(root, root_module);
    lower.arena.roots = roots;
    lower.modules.build_import_views();
    lower.finalize_act_copies();
    lower
}

/// 複数 `LoadedFile` から1つの module map を作る。
///
/// root file を先に登録し、`mod foo;` / `use mod foo::*` が作った module skeleton に
/// child file の block を差し込む。file path 解決や op table 確定は `sources` 側の責務。
pub fn lower_loaded_files_module_map(files: &[LoadedFile]) -> Result<Lower, LoadedFilesError> {
    let loaded = LoadedFileCsts::new(files)?;
    lower_loaded_file_csts_module_map(&loaded)
}

pub(crate) fn lower_loaded_file_csts_module_map(
    loaded: &LoadedFileCsts,
) -> Result<Lower, LoadedFilesError> {
    let mut lower = Lower::new();

    let root = loaded.root().ok_or(LoadedFilesError::MissingRoot)?;
    let roots = lower.register_block(&root.cst, lower.modules.root_id());
    lower.arena.roots = roots;

    for file in loaded.non_root_by_depth() {
        let Some(target) = lower.module_path_target(&file.module_path) else {
            return Err(LoadedFilesError::MissingModulePath {
                module_path: file.module_path.clone(),
            });
        };
        let Some(def) = target.def else {
            continue;
        };
        let previous_source_file =
            std::mem::replace(&mut lower.source_file, file.module_path.clone());
        let children = lower.register_block(&file.cst, target.module);
        lower.source_file = previous_source_file;
        lower.set_module_children(def, children);
    }

    lower.modules.build_import_views();
    lower.finalize_act_copies();
    Ok(lower)
}

pub(crate) struct RootFileAppend {
    pub lower: Lower,
    pub root: Cst,
    pub synthetic_var_act_copy_ids: Vec<TypeDeclId>,
    pub synthetic_sub_label_act_copy_ids: Vec<TypeDeclId>,
}

pub(crate) fn append_root_loaded_file_to_lower(
    mut lower: Lower,
    file: &LoadedFile,
) -> Result<RootFileAppend, LoadedFilesError> {
    if !file.module_path.segments.is_empty() {
        return Err(LoadedFilesError::MissingRoot);
    }

    let previous_act_copies = lower
        .modules
        .act_copies
        .keys()
        .copied()
        .collect::<FxHashSet<_>>();
    let previous_synthetic_var_act_copies = lower
        .modules
        .synthetic_var_act_copy_ids()
        .into_iter()
        .collect::<FxHashSet<_>>();
    let previous_synthetic_sub_label_act_copies = lower
        .modules
        .synthetic_sub_label_act_copy_ids()
        .into_iter()
        .collect::<FxHashSet<_>>();

    let loaded = LoadedFileCsts::new(std::slice::from_ref(file))?;
    let root = loaded.root().ok_or(LoadedFilesError::MissingRoot)?;
    let roots = lower.register_block(&root.cst, lower.modules.root_id());
    lower.arena.roots.extend(roots);

    lower.modules.build_import_views();
    lower.finalize_act_copies_added_after(
        &previous_act_copies,
        &previous_synthetic_var_act_copies,
        &previous_synthetic_sub_label_act_copies,
    );

    let synthetic_var_act_copy_ids = lower
        .modules
        .synthetic_var_act_copy_ids()
        .into_iter()
        .filter(|id| !previous_synthetic_var_act_copies.contains(id))
        .collect();
    let synthetic_sub_label_act_copy_ids = lower
        .modules
        .synthetic_sub_label_act_copy_ids()
        .into_iter()
        .filter(|id| !previous_synthetic_sub_label_act_copies.contains(id))
        .collect();

    Ok(RootFileAppend {
        lower,
        root: root.cst.clone(),
        synthetic_var_act_copy_ids,
        synthetic_sub_label_act_copy_ids,
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoadedFilesError {
    MissingRoot,
    DuplicateModulePath { module_path: ModulePath },
    MissingModulePath { module_path: ModulePath },
}

impl fmt::Display for LoadedFilesError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingRoot => write!(f, "loaded files do not contain a root module"),
            Self::DuplicateModulePath { module_path } => write!(
                f,
                "loaded files contain duplicate module `{}`",
                format_module_path(module_path)
            ),
            Self::MissingModulePath { module_path } => write!(
                f,
                "loaded module `{}` has no module declaration in its parent",
                format_module_path(module_path)
            ),
        }
    }
}

impl std::error::Error for LoadedFilesError {}

pub(crate) struct LoadedFileCsts {
    files: Vec<LoadedFileCst>,
}

pub(crate) struct LoadedFileCst {
    pub module_path: ModulePath,
    pub cst: Cst,
}

impl LoadedFileCsts {
    pub(crate) fn new(files: &[LoadedFile]) -> Result<Self, LoadedFilesError> {
        let mut seen = FxHashMap::default();
        let mut indexed = Vec::with_capacity(files.len());
        for file in files {
            if seen.insert(file.module_path.clone(), ()).is_some() {
                return Err(LoadedFilesError::DuplicateModulePath {
                    module_path: file.module_path.clone(),
                });
            }
            indexed.push(LoadedFileCst {
                module_path: file.module_path.clone(),
                cst: SyntaxNode::<YulangLanguage>::new_root(file.cst.clone()),
            });
        }
        indexed.sort_by_key(|file| {
            (
                file.module_path.segments.len(),
                module_path_sort_key(&file.module_path),
            )
        });
        Ok(Self { files: indexed })
    }

    pub(crate) fn root(&self) -> Option<&LoadedFileCst> {
        self.files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
    }

    pub(crate) fn by_depth(&self) -> impl Iterator<Item = &LoadedFileCst> {
        self.files.iter()
    }

    fn non_root_by_depth(&self) -> impl Iterator<Item = &LoadedFileCst> {
        self.files
            .iter()
            .filter(|file| !file.module_path.segments.is_empty())
    }
}

fn module_path_sort_key(path: &ModulePath) -> String {
    path.segments
        .iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("\0")
}

fn format_module_path(path: &ModulePath) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
