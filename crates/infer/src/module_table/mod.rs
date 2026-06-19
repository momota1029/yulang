use super::*;

mod query;

impl ModuleTable {
    pub(super) fn new() -> Self {
        Self {
            nodes: vec![ModuleNode {
                parent: None,
                decls: Vec::new(),
                values: FxHashMap::default(),
                types: FxHashMap::default(),
                modules: FxHashMap::default(),
                aliases: Vec::new(),
                import_values: FxHashMap::default(),
                import_types: FxHashMap::default(),
                import_modules: FxHashMap::default(),
                next_order: 0,
            }],
            act_templates: FxHashMap::default(),
            act_copies: FxHashMap::default(),
            resolved_act_copies: FxHashMap::default(),
            synthetic_var_act_copies: FxHashSet::default(),
            synthetic_var_act_uses: FxHashMap::default(),
            synthetic_sub_label_act_copies: FxHashSet::default(),
            synthetic_sub_label_act_uses: FxHashMap::default(),
            root_expr_owners: FxHashMap::default(),
            act_ops: FxHashMap::default(),
            act_op_defs: FxHashMap::default(),
            lazy_ops: FxHashSet::default(),
            act_methods: FxHashMap::default(),
            constructors: FxHashMap::default(),
            casts: FxHashMap::default(),
            role_inputs: FxHashMap::default(),
            role_associated: FxHashMap::default(),
            role_impls: FxHashMap::default(),
            role_methods: FxHashMap::default(),
            type_companions: FxHashMap::default(),
            type_methods: FxHashMap::default(),
            type_field_methods: FxHashMap::default(),
            def_source_ranges: FxHashMap::default(),
            next_type_id: 0,
        }
    }
    pub fn root_id(&self) -> ModuleId {
        ModuleId(0)
    }
    pub(super) fn new_module(&mut self) -> ModuleId {
        let id = ModuleId(self.nodes.len());
        self.nodes.push(ModuleNode {
            parent: None,
            decls: Vec::new(),
            values: FxHashMap::default(),
            types: FxHashMap::default(),
            modules: FxHashMap::default(),
            aliases: Vec::new(),
            import_values: FxHashMap::default(),
            import_types: FxHashMap::default(),
            import_modules: FxHashMap::default(),
            next_order: 0,
        });
        id
    }
    pub(super) fn new_anonymous_child_module(
        &mut self,
        parent: ModuleId,
        order: ModuleOrder,
    ) -> ModuleId {
        let module = self.new_module();
        self.nodes[module.0].parent = Some(ModuleParent {
            module: parent,
            order,
        });
        module
    }
    pub(super) fn insert_value_with_range(
        &mut self,
        module: ModuleId,
        name: Name,
        def: DefId,
        vis: Vis,
        source_range: Option<SourceRange>,
    ) -> ModuleOrder {
        if let Some(source_range) = source_range {
            self.def_source_ranges.insert(def, source_range);
        }
        let decl = self.push_decl(module, name.clone(), vis, ModuleDeclKind::Value { def });
        let order = self.nodes[module.0].decls[decl.0].order;
        self.nodes[module.0]
            .values
            .entry(name)
            .or_default()
            .push(decl);
        order
    }
    pub(super) fn insert_type(
        &mut self,
        module: ModuleId,
        name: Name,
        kind: ModuleTypeKind,
        vis: Vis,
    ) -> TypeDeclId {
        let id = self.next_type_decl_id();
        let decl = self.push_decl(module, name.clone(), vis, ModuleDeclKind::Type { id, kind });
        self.nodes[module.0]
            .types
            .entry(name)
            .or_default()
            .push(decl);
        id
    }
    pub(super) fn set_act_ops(&mut self, id: TypeDeclId, ops: Vec<ActOperationSig>) {
        self.act_ops.insert(id, ops);
    }
    pub(super) fn insert_act_operation_def(&mut self, owner: TypeDeclId, name: Name, def: DefId) {
        self.act_op_defs.insert(
            def,
            ActOperationDef {
                effect: owner,
                name,
            },
        );
    }
    pub(crate) fn is_act_operation_def(&self, def: DefId) -> bool {
        self.act_op_defs.contains_key(&def)
    }
    pub(super) fn mark_lazy_op(&mut self, def: DefId) {
        self.lazy_ops.insert(def);
    }
    pub(crate) fn is_lazy_op(&self, def: DefId) -> bool {
        self.lazy_ops.contains(&def)
    }
    pub(super) fn set_def_source_range(&mut self, def: DefId, source_range: SourceRange) {
        self.def_source_ranges.insert(def, source_range);
    }
    pub fn def_source_range(&self, def: DefId) -> Option<SourceRange> {
        self.def_source_ranges.get(&def).copied()
    }
    pub(super) fn set_act_template(&mut self, id: TypeDeclId, node: Cst) {
        self.act_templates.insert(id, node);
    }
    pub(crate) fn act_template(&self, id: TypeDeclId) -> Option<&Cst> {
        self.act_templates.get(&id)
    }
    pub(super) fn set_act_copy(&mut self, id: TypeDeclId, copy: ActCopyDecl) {
        self.act_copies.insert(id, copy);
    }
    pub(crate) fn act_copy(&self, id: TypeDeclId) -> Option<&ActCopyDecl> {
        self.act_copies.get(&id)
    }
    pub(super) fn set_resolved_act_copy(&mut self, id: TypeDeclId, copy: ResolvedActCopyDecl) {
        self.resolved_act_copies.insert(id, copy);
    }
    pub(crate) fn resolved_act_copy(&self, id: TypeDeclId) -> Option<&ResolvedActCopyDecl> {
        self.resolved_act_copies.get(&id)
    }
    pub(super) fn set_synthetic_var_act_copy(&mut self, id: TypeDeclId) {
        self.synthetic_var_act_copies.insert(id);
    }
    pub(crate) fn synthetic_var_act_copy_ids(&self) -> Vec<TypeDeclId> {
        self.synthetic_var_act_copies.iter().copied().collect()
    }
    pub(super) fn push_synthetic_var_act_use(&mut self, owner: DefId, usage: SyntheticVarActUse) {
        self.synthetic_var_act_uses
            .entry(owner)
            .or_default()
            .push(usage);
    }
    pub(crate) fn synthetic_var_act_uses(&self, owner: DefId) -> &[SyntheticVarActUse] {
        self.synthetic_var_act_uses
            .get(&owner)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
    pub(super) fn set_synthetic_sub_label_act_copy(&mut self, id: TypeDeclId) {
        self.synthetic_sub_label_act_copies.insert(id);
    }
    pub(crate) fn synthetic_sub_label_act_copy_ids(&self) -> Vec<TypeDeclId> {
        self.synthetic_sub_label_act_copies
            .iter()
            .copied()
            .collect()
    }
    pub(super) fn push_synthetic_sub_label_act_use(
        &mut self,
        owner: DefId,
        usage: SyntheticSubLabelActUse,
    ) {
        self.synthetic_sub_label_act_uses
            .entry(owner)
            .or_default()
            .push(usage);
    }
    pub(crate) fn synthetic_sub_label_act_uses(&self, owner: DefId) -> &[SyntheticSubLabelActUse] {
        self.synthetic_sub_label_act_uses
            .get(&owner)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
    pub(super) fn push_root_expr_owner(&mut self, module: ModuleId, owner: Option<DefId>) {
        self.root_expr_owners.entry(module).or_default().push(owner);
    }
    pub(crate) fn root_expr_owner(&self, module: ModuleId, index: usize) -> Option<Option<DefId>> {
        self.root_expr_owners
            .get(&module)
            .and_then(|owners| owners.get(index))
            .copied()
    }
    pub(super) fn insert_act_method(&mut self, method: ActMethodDecl) {
        self.act_methods
            .entry(method.owner)
            .or_default()
            .push(method);
    }
    pub fn act_methods(&self, id: TypeDeclId) -> &[ActMethodDecl] {
        self.act_methods.get(&id).map(Vec::as_slice).unwrap_or(&[])
    }
    pub fn all_act_methods(&self) -> impl Iterator<Item = &ActMethodDecl> {
        self.act_methods.values().flat_map(|methods| methods.iter())
    }
    pub(super) fn insert_constructor(&mut self, def: DefId, constructor: ConstructorDecl) {
        self.constructors.insert(def, constructor);
    }
    pub(crate) fn constructor_by_def(&self, def: DefId) -> Option<&ConstructorDecl> {
        self.constructors.get(&def)
    }
    pub(super) fn insert_cast_decl(&mut self, decl: CastDecl) {
        self.casts.entry(decl.module).or_default().push(decl);
    }
    pub(crate) fn cast_decls(&self, module: ModuleId) -> &[CastDecl] {
        self.casts.get(&module).map(Vec::as_slice).unwrap_or(&[])
    }
    pub(super) fn set_role_inputs(&mut self, id: TypeDeclId, inputs: Vec<String>) {
        self.role_inputs.insert(id, inputs);
    }
    pub fn role_inputs(&self, id: TypeDeclId) -> &[String] {
        self.role_inputs.get(&id).map(Vec::as_slice).unwrap_or(&[])
    }
    pub(super) fn set_role_associated(&mut self, id: TypeDeclId, associated: Vec<String>) {
        self.role_associated.insert(id, associated);
    }
    pub fn role_associated(&self, id: TypeDeclId) -> &[String] {
        self.role_associated
            .get(&id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
    pub(super) fn insert_role_impl(&mut self, impl_decl: RoleImplDecl) {
        self.role_impls
            .entry(impl_decl.module)
            .or_default()
            .push(impl_decl);
    }
    pub fn role_impls(&self, module: ModuleId) -> &[RoleImplDecl] {
        self.role_impls
            .get(&module)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
    pub(super) fn insert_role_method(&mut self, method: RoleMethodDecl) {
        self.role_methods
            .entry(method.owner)
            .or_default()
            .push(method);
    }
    pub fn role_methods(&self, id: TypeDeclId) -> &[RoleMethodDecl] {
        self.role_methods.get(&id).map(Vec::as_slice).unwrap_or(&[])
    }
    pub fn all_role_methods(&self) -> impl Iterator<Item = &RoleMethodDecl> {
        self.role_methods
            .values()
            .flat_map(|methods| methods.iter())
    }
    pub(super) fn set_type_companion(&mut self, id: TypeDeclId, module: ModuleId) {
        self.type_companions.insert(id, module);
    }
    pub fn type_companion(&self, id: TypeDeclId) -> Option<ModuleId> {
        self.type_companions.get(&id).copied()
    }
    pub(super) fn insert_type_method(&mut self, method: TypeMethodDecl) {
        self.type_methods
            .entry(method.owner)
            .or_default()
            .push(method);
    }
    pub fn type_methods(&self, id: TypeDeclId) -> &[TypeMethodDecl] {
        self.type_methods.get(&id).map(Vec::as_slice).unwrap_or(&[])
    }
    pub fn all_type_methods(&self) -> impl Iterator<Item = &TypeMethodDecl> {
        self.type_methods
            .values()
            .flat_map(|methods| methods.iter())
    }
    pub(super) fn insert_type_field_method(&mut self, method: TypeFieldMethodDecl) {
        self.type_field_methods
            .entry(method.owner)
            .or_default()
            .push(method);
    }
    pub fn type_field_methods(&self, id: TypeDeclId) -> &[TypeFieldMethodDecl] {
        self.type_field_methods
            .get(&id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
    pub fn all_type_field_methods(&self) -> impl Iterator<Item = &TypeFieldMethodDecl> {
        self.type_field_methods
            .values()
            .flat_map(|methods| methods.iter())
    }
    pub(super) fn insert_module(
        &mut self,
        module: ModuleId,
        name: Name,
        sub: ModuleId,
        def: DefId,
        vis: Vis,
    ) {
        let decl = self.push_decl(
            module,
            name.clone(),
            vis,
            ModuleDeclKind::Module { module: sub, def },
        );
        let order = self.nodes[module.0].decls[decl.0].order;
        self.nodes[module.0]
            .modules
            .entry(name)
            .or_default()
            .push(decl);
        self.nodes[sub.0].parent = Some(ModuleParent { module, order });
    }
    pub(super) fn add_alias(&mut self, module: ModuleId, import: UseImport, vis: Vis) {
        let order = self.next_order(module);
        self.nodes[module.0]
            .aliases
            .push(AliasDecl { import, vis, order });
    }
    pub fn aliases(&self, module: ModuleId) -> &[AliasDecl] {
        &self.nodes[module.0].aliases
    }
    pub(super) fn build_import_views(&mut self) {
        // 再エクスポートの連鎖（prelude → ops → …）を運びきるまで繰り返す。
        // entry は重複 push しない（push_import_* が冪等）ので単調増加・有限で収束する。
        loop {
            let before = self.import_entry_count();
            for module_index in 0..self.nodes.len() {
                let module = ModuleId(module_index);
                let aliases = self.nodes[module_index].aliases.clone();
                for alias in aliases {
                    self.import_alias(module, &alias);
                }
            }
            if self.import_entry_count() == before {
                break;
            }
        }
    }
    pub(super) fn import_entry_count(&self) -> usize {
        self.nodes
            .iter()
            .map(|node| {
                node.import_values.values().map(Vec::len).sum::<usize>()
                    + node.import_types.values().map(Vec::len).sum::<usize>()
                    + node.import_modules.values().map(Vec::len).sum::<usize>()
            })
            .sum()
    }
    pub fn value_at(&self, module: ModuleId, name: &Name, site: ModuleOrder) -> Option<DefId> {
        let decl = self.select_decl(module, self.nodes[module.0].values.get(name)?, site)?;
        match decl.kind {
            ModuleDeclKind::Value { def } => Some(def),
            ModuleDeclKind::Type { .. } | ModuleDeclKind::Module { .. } => None,
        }
    }
    pub fn type_at(
        &self,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        let decl = self.select_decl(module, self.nodes[module.0].types.get(name)?, site)?;
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
    }
    pub fn module_at(&self, module: ModuleId, name: &Name, site: ModuleOrder) -> Option<ModuleId> {
        let decl = self.select_decl(module, self.nodes[module.0].modules.get(name)?, site)?;
        match decl.kind {
            ModuleDeclKind::Module { module, .. } => Some(module),
            ModuleDeclKind::Value { .. } | ModuleDeclKind::Type { .. } => None,
        }
    }
    pub fn lexical_value_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<DefId> {
        loop {
            if let Some(def) = self.value_at(module, name, site) {
                return Some(def);
            }
            if let Some(def) = self.imported_value_at(module, name, site) {
                return Some(def);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    pub fn value_path_at(
        &self,
        module: ModuleId,
        path: &[Name],
        site: ModuleOrder,
    ) -> Option<DefId> {
        let Some((last, prefix)) = path.split_last() else {
            return None;
        };
        if prefix.is_empty() {
            return self.lexical_value_at(module, last, site);
        }

        let target = self.module_path_with_imports_from(module, prefix, site)?;
        self.value_at(target, last, module_path_site())
            .or_else(|| self.exported_value_at(target, last))
    }
    pub fn type_path_at(
        &self,
        module: ModuleId,
        path: &[Name],
        site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        let Some((last, prefix)) = path.split_last() else {
            return None;
        };
        if prefix.is_empty() {
            return self.lexical_type_at(module, last, site);
        }

        let target = self.module_path_with_imports_from(module, prefix, site)?;
        self.type_at(target, last, module_path_site())
            .or_else(|| self.exported_type_at(target, last))
    }
    pub fn act_operation_decls_at(
        &self,
        module: ModuleId,
        effect_path: &[Name],
        site: ModuleOrder,
    ) -> Vec<ActOperationDecl> {
        let Some(effect) = self
            .type_path_at(module, effect_path, site)
            .filter(|decl| decl.kind == ModuleTypeKind::Act)
        else {
            return Vec::new();
        };

        self.act_ops
            .get(&effect.id)
            .into_iter()
            .flat_map(|ops| ops.iter())
            .cloned()
            .map(|op| ActOperationDecl {
                def: self
                    .type_companion(effect.id)
                    .and_then(|companion| self.value_at(companion, &op.name, module_path_site()))
                    .filter(|def| {
                        self.act_op_defs
                            .get(def)
                            .is_some_and(|found| found.effect == effect.id && found.name == op.name)
                    }),
                effect: effect.clone(),
                name: op.name,
                signature: op.signature,
            })
            .collect()
    }
    pub fn act_operation_decl_by_def(&self, def: DefId) -> Option<ActOperationDecl> {
        let op = self.act_op_defs.get(&def)?;
        let effect = self.type_decl_by_id(op.effect)?;
        let signature = self
            .act_ops
            .get(&op.effect)
            .and_then(|ops| ops.iter().find(|sig| sig.name == op.name))
            .and_then(|sig| sig.signature.clone());
        Some(ActOperationDecl {
            effect,
            name: op.name.clone(),
            def: Some(def),
            signature,
        })
    }
    pub fn lexical_type_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        loop {
            if let Some(found) = self.type_at(module, name, site) {
                return Some(found);
            }
            if let Some(found) = self.imported_type_at(module, name, site) {
                return Some(found);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    pub fn lexical_module_at(
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
    pub fn module_by_path(&self, path: &ModulePath) -> Option<ModuleId> {
        let mut module = self.root_id();
        for segment in &path.segments {
            module = self.first_module_decl(module, segment)?.module;
        }
        Some(module)
    }
    pub fn module_path(&self, mut module: ModuleId) -> ModulePath {
        let mut segments = Vec::new();
        while let Some(parent) = self.nodes[module.0].parent {
            let parent_node = &self.nodes[parent.module.0];
            let Some(decl) = parent_node.decls.iter().find(|decl| {
                decl.order == parent.order
                    && matches!(
                        decl.kind,
                        ModuleDeclKind::Module { module: child, .. } if child == module
                    )
            }) else {
                break;
            };
            segments.push(decl.name.clone());
            module = parent.module;
        }
        segments.reverse();
        ModulePath { segments }
    }
    pub(super) fn module_def(&self, module: ModuleId) -> Option<DefId> {
        let parent = self.nodes[module.0].parent?;
        let parent_node = &self.nodes[parent.module.0];
        parent_node.decls.iter().find_map(|decl| {
            (decl.order == parent.order)
                .then_some(decl)
                .and_then(|decl| match decl.kind {
                    ModuleDeclKind::Module { module: child, def } if child == module => Some(def),
                    ModuleDeclKind::Value { .. }
                    | ModuleDeclKind::Type { .. }
                    | ModuleDeclKind::Module { .. } => None,
                })
        })
    }
    pub fn type_decl_path(&self, decl: &ModuleTypeDecl) -> ModulePath {
        let mut path = self.module_path(decl.module);
        path.segments.push(decl.name.clone());
        path
    }
}

trait ImportOrder {
    fn order(&self) -> ModuleOrder;
}

impl ImportOrder for ImportedValueDecl {
    fn order(&self) -> ModuleOrder {
        self.order
    }
}

impl ImportOrder for ImportedTypeDecl {
    fn order(&self) -> ModuleOrder {
        self.order
    }
}

impl ImportOrder for ImportedModuleDecl {
    fn order(&self) -> ModuleOrder {
        self.order
    }
}

pub(super) fn qualified_label(prefix: &[String], name: &Name) -> String {
    if prefix.is_empty() {
        return name.0.clone();
    }

    let mut label = prefix.join(".");
    label.push('.');
    label.push_str(&name.0);
    label
}

// ── pass1 ────────────────────────────────────────────────────────────────
