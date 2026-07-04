use super::*;

mod compiled;
mod query;

impl ModuleTable {
    pub(super) fn new() -> Self {
        Self {
            nodes: vec![ModuleNode {
                parent: None,
                band_path: ModulePath::default(),
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
            act_type_vars: FxHashMap::default(),
            act_copies: FxHashMap::default(),
            resolved_act_copies: FxHashMap::default(),
            synthetic_var_act_copies: FxHashSet::default(),
            synthetic_var_act_uses: FxHashMap::default(),
            synthetic_sub_label_act_copies: FxHashSet::default(),
            synthetic_sub_label_act_uses: FxHashMap::default(),
            root_expr_owners: FxHashMap::default(),
            act_ops: FxHashMap::default(),
            host_acts: FxHashSet::default(),
            act_op_defs: FxHashMap::default(),
            lazy_ops: FxHashSet::default(),
            act_methods: FxHashMap::default(),
            constructors: FxHashMap::default(),
            error_decls: FxHashMap::default(),
            error_constructor_ops: FxHashMap::default(),
            error_op_constructors: FxHashMap::default(),
            casts: FxHashMap::default(),
            role_inputs: FxHashMap::default(),
            role_associated: FxHashMap::default(),
            role_impls: FxHashMap::default(),
            role_methods: FxHashMap::default(),
            type_companions: FxHashMap::default(),
            type_methods: FxHashMap::default(),
            type_field_methods: FxHashMap::default(),
            def_source_spans: FxHashMap::default(),
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
            band_path: ModulePath::default(),
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
    pub(super) fn insert_value_with_span(
        &mut self,
        module: ModuleId,
        name: Name,
        def: DefId,
        vis: Vis,
        source_span: Option<SourceSpan>,
    ) -> ModuleOrder {
        if let Some(source_span) = source_span {
            self.def_source_spans.insert(def, source_span);
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
    pub(super) fn set_host_act(&mut self, id: TypeDeclId) {
        self.host_acts.insert(id);
    }
    pub fn is_host_act(&self, id: TypeDeclId) -> bool {
        self.host_acts.contains(&id)
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
    pub fn is_lazy_op(&self, def: DefId) -> bool {
        self.lazy_ops.contains(&def)
    }
    pub(super) fn set_def_source_span(&mut self, def: DefId, source_span: SourceSpan) {
        self.def_source_spans.insert(def, source_span);
    }
    pub fn def_source_range(&self, def: DefId) -> Option<SourceRange> {
        self.def_source_spans.get(&def).map(|span| span.range)
    }
    pub fn def_source_span(&self, def: DefId) -> Option<&SourceSpan> {
        self.def_source_spans.get(&def)
    }
    pub fn def_source_spans(&self) -> impl Iterator<Item = (DefId, &SourceSpan)> {
        self.def_source_spans.iter().map(|(def, span)| (*def, span))
    }
    pub(super) fn set_act_template(&mut self, id: TypeDeclId, node: Cst) {
        self.act_templates.insert(id, node);
    }
    pub(crate) fn act_template(&self, id: TypeDeclId) -> Option<&Cst> {
        self.act_templates.get(&id)
    }
    pub(crate) fn set_act_type_vars(&mut self, id: TypeDeclId, type_vars: Vec<String>) {
        self.act_type_vars.insert(id, type_vars);
    }
    pub(crate) fn act_type_vars(&self, id: TypeDeclId) -> Option<&[String]> {
        self.act_type_vars.get(&id).map(Vec::as_slice)
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
    pub(super) fn insert_error_decl(&mut self, decl: ErrorDecl) {
        for variant in &decl.variants {
            self.error_constructor_ops
                .insert(variant.constructor_def, variant.operation_def);
            self.error_op_constructors
                .insert(variant.operation_def, variant.constructor_def);
        }
        self.error_decls.insert(decl.owner, decl);
    }
    pub(super) fn set_error_helpers(
        &mut self,
        owner: TypeDeclId,
        wrap_def: Option<DefId>,
        up_def: Option<DefId>,
    ) {
        if let Some(decl) = self.error_decls.get_mut(&owner) {
            decl.wrap_def = wrap_def;
            decl.up_def = up_def;
        }
    }
    pub(crate) fn error_decl(&self, owner: TypeDeclId) -> Option<&ErrorDecl> {
        self.error_decls.get(&owner)
    }
    pub(crate) fn error_operation_for_constructor(&self, def: DefId) -> Option<DefId> {
        self.error_constructor_ops.get(&def).copied()
    }
    pub(crate) fn error_variant_for_operation(
        &self,
        def: DefId,
    ) -> Option<(&ErrorDecl, &ErrorVariantDecl)> {
        let constructor = self.error_op_constructors.get(&def)?;
        let owner = self.constructor_by_def(*constructor)?.owner;
        let decl = self.error_decls.get(&owner)?;
        let variant = decl
            .variants
            .iter()
            .find(|variant| variant.operation_def == def)?;
        Some((decl, variant))
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
        self.nodes[sub.0].band_path = self.nodes[module.0].band_path.clone();
        self.nodes[module.0]
            .modules
            .entry(name)
            .or_default()
            .push(decl);
        self.nodes[sub.0].parent = Some(ModuleParent { module, order });
    }
    pub(super) fn set_module_band_path(&mut self, module: ModuleId, band_path: ModulePath) {
        self.nodes[module.0].band_path = band_path;
    }
    pub(super) fn module_band_path(&self, module: ModuleId) -> &ModulePath {
        &self.nodes[module.0].band_path
    }
    pub(crate) fn remap_runtime_defs(&mut self, import: &CompiledRuntimeImport) {
        for node in &mut self.nodes {
            for decl in &mut node.decls {
                remap_module_decl_kind(&mut decl.kind, import);
            }
            for entries in node.import_values.values_mut() {
                for entry in entries {
                    entry.def = import.map_def(entry.def);
                }
            }
        }

        self.synthetic_var_act_uses =
            remap_def_keyed_vec(std::mem::take(&mut self.synthetic_var_act_uses), import);
        self.synthetic_sub_label_act_uses = remap_def_keyed_vec(
            std::mem::take(&mut self.synthetic_sub_label_act_uses),
            import,
        );
        for owners in self.root_expr_owners.values_mut() {
            for owner in owners {
                remap_optional_def(owner, import);
            }
        }

        self.act_op_defs = std::mem::take(&mut self.act_op_defs)
            .into_iter()
            .map(|(def, op)| (import.map_def(def), op))
            .collect();
        self.lazy_ops = std::mem::take(&mut self.lazy_ops)
            .into_iter()
            .map(|def| import.map_def(def))
            .collect();
        for methods in self.act_methods.values_mut() {
            for method in methods {
                method.def = import.map_def(method.def);
            }
        }
        self.constructors = std::mem::take(&mut self.constructors)
            .into_iter()
            .map(|(def, constructor)| (import.map_def(def), constructor))
            .collect();
        for error in self.error_decls.values_mut() {
            remap_error_decl(error, import);
        }
        self.rebuild_error_operation_maps();
        for casts in self.casts.values_mut() {
            for cast in casts {
                cast.def = import.map_def(cast.def);
            }
        }
        for impls in self.role_impls.values_mut() {
            for impl_decl in impls {
                impl_decl.def = import.map_def(impl_decl.def);
                for method in &mut impl_decl.methods {
                    method.def = import.map_def(method.def);
                }
            }
        }
        for methods in self.role_methods.values_mut() {
            for method in methods {
                method.def = import.map_def(method.def);
            }
        }
        for methods in self.type_methods.values_mut() {
            for method in methods {
                method.def = import.map_def(method.def);
            }
        }
        for methods in self.type_field_methods.values_mut() {
            for method in methods {
                method.def = import.map_def(method.def);
            }
        }
        self.def_source_spans = std::mem::take(&mut self.def_source_spans)
            .into_iter()
            .map(|(def, span)| (import.map_def(def), span))
            .collect();
    }

    fn rebuild_error_operation_maps(&mut self) {
        self.error_constructor_ops.clear();
        self.error_op_constructors.clear();
        for decl in self.error_decls.values() {
            for variant in &decl.variants {
                self.error_constructor_ops
                    .insert(variant.constructor_def, variant.operation_def);
                self.error_op_constructors
                    .insert(variant.operation_def, variant.constructor_def);
            }
        }
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
            ModuleDeclKind::Module { module: child, .. } => same_band_allows_module_step(
                self.module_band_path(module),
                self.module_band_path(child),
            )
            .then_some(child),
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
            .filter(|decl| matches!(decl.kind, ModuleTypeKind::Act | ModuleTypeKind::Error))
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
                tier: op.tier,
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
        let tier = self
            .act_ops
            .get(&op.effect)
            .and_then(|ops| ops.iter().find(|sig| sig.name == op.name))
            .map(|sig| sig.tier)
            .unwrap_or(poly::host_manifest::HostOperationTier::Sync);
        Some(ActOperationDecl {
            effect,
            name: op.name.clone(),
            def: Some(def),
            signature,
            tier,
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
    pub(crate) fn module_def(&self, module: ModuleId) -> Option<DefId> {
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

fn same_band_allows_module_step(parent: &ModulePath, child: &ModulePath) -> bool {
    parent == child || child.segments.is_empty()
}

fn remap_module_decl_kind(kind: &mut ModuleDeclKind, import: &CompiledRuntimeImport) {
    match kind {
        ModuleDeclKind::Value { def } | ModuleDeclKind::Module { def, .. } => {
            *def = import.map_def(*def);
        }
        ModuleDeclKind::Type { .. } => {}
    }
}

fn remap_optional_def(def: &mut Option<DefId>, import: &CompiledRuntimeImport) {
    if let Some(source) = *def {
        *def = Some(import.map_def(source));
    }
}

fn remap_error_decl(error: &mut ErrorDecl, import: &CompiledRuntimeImport) {
    for variant in &mut error.variants {
        variant.constructor_def = import.map_def(variant.constructor_def);
        variant.operation_def = import.map_def(variant.operation_def);
    }
    remap_optional_def(&mut error.wrap_def, import);
    remap_optional_def(&mut error.up_def, import);
}

fn remap_def_keyed_vec<T>(
    source: FxHashMap<DefId, Vec<T>>,
    import: &CompiledRuntimeImport,
) -> FxHashMap<DefId, Vec<T>> {
    source
        .into_iter()
        .map(|(def, values)| (import.map_def(def), values))
        .collect()
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
