use serde::{Deserialize, Serialize};

use poly::dump::DumpLabels;
use poly::expr::{
    Arena as PolyArena, ArgEffectContract, CaseArm, CastRule, CatchArm, CatchOperation,
    Constructor, Def, DefId, EffectOperation, Expr, ExprId, Pat, PatId, RecordPatField,
    RecordSpread, RefId, RuntimeRoot, SelectId, SelectResolution, Stmt,
};
use poly::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate, RoleImplMethod,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::lowering::BodyLowering;
use crate::{
    CompiledNamespaceMergeOutput, CompiledNamespaceSurface, CompiledTypeArena, CompiledTypeImporter,
};

/// Lowered per-unit runtime surface.
///
/// The namespace/typed surfaces are enough for parsing and type lookup, but not
/// for executing cached dependency values. Runtime import needs the lowered
/// poly body graph and the labels that keep diagnostics/dumps readable. The
/// remap/merge step is intentionally separate from this serialized surface.
#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledRuntimeSurface {
    pub arena: poly::expr::Arena,
    pub labels: poly::dump::DumpLabels,
    pub modules: Vec<CompiledRuntimeModuleDef>,
    pub values: Vec<CompiledRuntimeValueDef>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledRuntimeModuleDef {
    pub module: u32,
    pub module_path: Vec<String>,
    pub def: DefId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledRuntimeValueDef {
    pub symbol: u32,
    pub def: DefId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledRuntimeMergeError {
    MissingModule {
        prefix: usize,
        module: u32,
    },
    MissingMappedModule {
        prefix: usize,
        module: u32,
        mapped_module: u32,
    },
    MissingValueSymbol {
        prefix: usize,
        symbol: u32,
    },
    ConflictingModuleDef {
        module: u32,
    },
    DuplicateModuleDef {
        module: u32,
    },
    DuplicateValueDef {
        symbol: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledRuntimeReachableImportError {
    pub missing_external_defs: Vec<DefId>,
}

#[derive(Clone)]
pub struct CompiledRuntimeMergeOutput {
    pub surface: CompiledRuntimeSurface,
    def_remap: FxHashMap<(usize, DefId), DefId>,
}

impl CompiledRuntimeMergeOutput {
    pub fn map_def(&self, prefix: usize, def: DefId) -> Option<DefId> {
        self.def_remap.get(&(prefix, def)).copied()
    }
}

pub struct CompiledRuntimeImport {
    external_defs: FxHashSet<DefId>,
    pub defs: FxHashMap<DefId, DefId>,
    pub exprs: FxHashMap<ExprId, ExprId>,
    pub pats: FxHashMap<PatId, PatId>,
    pub refs: FxHashMap<RefId, RefId>,
    pub selects: FxHashMap<SelectId, SelectId>,
    pub roots: Vec<DefId>,
    pub runtime_roots: Vec<RuntimeRoot>,
    pub root_exprs: Vec<ExprId>,
    pub modules: Vec<CompiledRuntimeImportedModule>,
    pub values: Vec<CompiledRuntimeImportedValue>,
}

pub struct CompiledRuntimeImportedModule {
    pub module: u32,
    pub def: DefId,
}

pub struct CompiledRuntimeImportedValue {
    pub symbol: u32,
    pub def: DefId,
}

impl CompiledRuntimeSurface {
    pub fn from_lowering(lowering: &BodyLowering) -> Self {
        Self {
            arena: lowering.session.poly.clone(),
            labels: lowering.labels.clone(),
            modules: Vec::new(),
            values: Vec::new(),
        }
    }

    pub fn from_lowering_with_namespace(
        lowering: &BodyLowering,
        namespace: &CompiledNamespaceSurface,
    ) -> Self {
        Self {
            arena: lowering.session.poly.clone(),
            labels: lowering.labels.clone(),
            modules: runtime_module_defs_from_namespace(lowering, namespace),
            values: runtime_value_defs_from_namespace(lowering, namespace),
        }
    }

    pub fn import_into(
        &self,
        target: &mut PolyArena,
        labels: &mut DumpLabels,
    ) -> CompiledRuntimeImport {
        self.import_into_with_external_defs(target, labels, [])
    }

    pub fn import_into_with_external_defs(
        &self,
        target: &mut PolyArena,
        labels: &mut DumpLabels,
        external_defs: impl IntoIterator<Item = (DefId, DefId)>,
    ) -> CompiledRuntimeImport {
        let mut import = CompiledRuntimeImport::new();
        for (source, target) in external_defs {
            import.external_defs.insert(source);
            import.defs.insert(source, target);
        }
        reserve_def_ids(&self.arena, target, &mut import);
        reserve_ref_ids(&self.arena, target, &mut import);
        reserve_select_ids(&self.arena, target, &mut import);
        reserve_expr_ids(&self.arena, target, &mut import);
        reserve_pat_ids(&self.arena, target, &mut import);

        let source_types = CompiledTypeArena::from_type_arena(&self.arena.typ);
        let (defs, cast_rules, role_impls) = {
            let mut type_importer = CompiledTypeImporter::new(&source_types, target);
            (
                import_defs(&self.arena, &import, &mut type_importer),
                import_cast_rules(&self.arena, &import, &mut type_importer),
                import_role_impls(&self.arena, &import, &mut type_importer),
            )
        };

        import_refs(&self.arena, target, &import);
        import_selects(&self.arena, target, &import);
        import_exprs(&self.arena, target, &import);
        import_pats(&self.arena, target, &import);
        for (id, def) in defs {
            target.defs.set(id, def);
        }

        import.roots = self
            .arena
            .roots
            .iter()
            .filter(|id| !import.is_external_def(**id))
            .map(|id| import.map_def(*id))
            .collect();
        import.runtime_roots = self
            .arena
            .runtime_roots
            .iter()
            .filter(|root| !runtime_root_is_external(root, &import))
            .map(|root| import_runtime_root(root, &import))
            .collect();
        import.root_exprs = self
            .arena
            .root_exprs
            .iter()
            .filter(|id| !root_expr_is_external(&self.arena, **id, &import))
            .map(|id| import.map_expr(*id))
            .collect();
        import.modules = self
            .modules
            .iter()
            .map(|module| CompiledRuntimeImportedModule {
                module: module.module,
                def: import.map_def(module.def),
            })
            .collect();
        import.values = self
            .values
            .iter()
            .map(|value| CompiledRuntimeImportedValue {
                symbol: value.symbol,
                def: import.map_def(value.def),
            })
            .collect();
        target.roots.extend(import.roots.iter().copied());
        target
            .runtime_roots
            .extend(import.runtime_roots.iter().copied());
        target.root_exprs.extend(import.root_exprs.iter().copied());

        import_root_expr_defs(&self.arena, target, &import);
        target.cast_rules.extend(cast_rules);
        for candidate in role_impls {
            target.role_impls.insert(candidate);
        }
        import_effect_operations(&self.arena, target, &import);
        import_synthetic_var_effects(&self.arena, target, &import);
        import_constructors(&self.arena, target, &import);
        import_arg_effect_contracts(&self.arena, target, &import);
        import_field_projections(&self.arena, target, &import);
        import_labels(&self.labels, labels, &import);
        import
    }

    pub fn import_reachable_into_with_external_defs(
        &self,
        target: &mut PolyArena,
        labels: &mut DumpLabels,
        external_defs: impl IntoIterator<Item = (DefId, DefId)>,
    ) -> Result<CompiledRuntimeImport, CompiledRuntimeReachableImportError> {
        let mut import = CompiledRuntimeImport::new();
        for (source, target) in external_defs {
            import.external_defs.insert(source);
            import.defs.insert(source, target);
        }
        let selection = RuntimeImportSelection::new(self, &import.external_defs);
        let missing = selection.missing_external_defs(import.defs.keys().copied());
        if !missing.is_empty() {
            return Err(CompiledRuntimeReachableImportError {
                missing_external_defs: missing,
            });
        }

        reserve_selected_def_ids(&self.arena, target, &mut import, &selection);
        reserve_selected_ref_ids(target, &mut import, &selection);
        reserve_selected_select_ids(&self.arena, target, &mut import, &selection);
        reserve_selected_expr_ids(target, &mut import, &selection);
        reserve_selected_pat_ids(target, &mut import, &selection);

        let source_types = CompiledTypeArena::from_type_arena(&self.arena.typ);
        let (defs, cast_rules, role_impls) = {
            let mut type_importer = CompiledTypeImporter::new(&source_types, target);
            (
                import_selected_defs(&self.arena, &import, &mut type_importer, &selection),
                import_selected_cast_rules(&self.arena, &import, &mut type_importer, &selection),
                import_selected_role_impls(&self.arena, &import, &mut type_importer, &selection),
            )
        };

        import_selected_refs(&self.arena, target, &import, &selection);
        import_selected_selects(&self.arena, target, &import, &selection);
        import_selected_exprs(&self.arena, target, &import, &selection);
        import_selected_pats(&self.arena, target, &import, &selection);
        for (id, def) in defs {
            target.defs.set(id, def);
        }

        import.roots = self
            .arena
            .roots
            .iter()
            .filter(|id| selection.defs.contains(id))
            .map(|id| import.map_def(*id))
            .collect();
        import.runtime_roots = self
            .arena
            .runtime_roots
            .iter()
            .filter(|root| runtime_root_is_selected(root, &selection))
            .map(|root| import_runtime_root(root, &import))
            .collect();
        import.root_exprs = self
            .arena
            .root_exprs
            .iter()
            .filter(|id| selection.exprs.contains(id))
            .map(|id| import.map_expr(*id))
            .collect();
        import.modules = self
            .modules
            .iter()
            .map(|module| CompiledRuntimeImportedModule {
                module: module.module,
                def: import.map_def(module.def),
            })
            .collect();
        import.values = self
            .values
            .iter()
            .map(|value| CompiledRuntimeImportedValue {
                symbol: value.symbol,
                def: import.map_def(value.def),
            })
            .collect();
        target.roots.extend(import.roots.iter().copied());
        target
            .runtime_roots
            .extend(import.runtime_roots.iter().copied());
        target.root_exprs.extend(import.root_exprs.iter().copied());

        import_selected_root_expr_defs(&self.arena, target, &import, &selection);
        target.cast_rules.extend(cast_rules);
        for candidate in role_impls {
            target.role_impls.insert(candidate);
        }
        import_selected_effect_operations(&self.arena, target, &import, &selection);
        import_synthetic_var_effects(&self.arena, target, &import);
        import_selected_constructors(&self.arena, target, &import, &selection);
        import_selected_arg_effect_contracts(&self.arena, target, &import, &selection);
        import_selected_field_projections(&self.arena, target, &import, &selection);
        import_selected_labels(&self.labels, labels, &import, &selection);
        Ok(import)
    }

    pub fn required_external_defs_for_reachable_import(
        &self,
        external_defs: impl IntoIterator<Item = DefId>,
    ) -> Vec<DefId> {
        let external_defs = external_defs.into_iter().collect::<FxHashSet<_>>();
        RuntimeImportSelection::new(self, &external_defs).required_external_defs()
    }

    pub fn merge_prefixes<'a>(
        prefixes: impl IntoIterator<Item = &'a CompiledRuntimeSurface>,
        namespace: &CompiledNamespaceMergeOutput,
    ) -> Result<Self, CompiledRuntimeMergeError> {
        Ok(Self::merge_prefixes_with_remap(prefixes, namespace)?.surface)
    }

    pub fn merge_prefixes_with_remap<'a>(
        prefixes: impl IntoIterator<Item = &'a CompiledRuntimeSurface>,
        namespace: &CompiledNamespaceMergeOutput,
    ) -> Result<CompiledRuntimeMergeOutput, CompiledRuntimeMergeError> {
        let mut arena = PolyArena::new();
        let mut labels = DumpLabels::new();
        let mut modules: Vec<CompiledRuntimeModuleDef> = Vec::new();
        let mut values: Vec<CompiledRuntimeValueDef> = Vec::new();
        let mut def_remap = FxHashMap::default();
        let mut module_defs = FxHashMap::default();
        let mut seen_values = FxHashSet::default();
        for (prefix, surface) in prefixes.into_iter().enumerate() {
            let import = surface.import_into(&mut arena, &mut labels);
            for (source, target) in &import.defs {
                def_remap.insert((prefix, *source), *target);
            }
            for module in import.modules {
                let Some(merged_module) = namespace.map_module(prefix, module.module) else {
                    return Err(CompiledRuntimeMergeError::MissingModule {
                        prefix,
                        module: module.module,
                    });
                };
                if let Some(existing_def) = module_defs.get(&merged_module).copied() {
                    merge_imported_module_def_children(
                        &mut arena,
                        merged_module,
                        existing_def,
                        module.def,
                    )?;
                    arena.roots.retain(|root| *root != module.def);
                    continue;
                }
                if modules.iter().any(|module| module.module == merged_module) {
                    return Err(CompiledRuntimeMergeError::DuplicateModuleDef {
                        module: merged_module,
                    });
                }
                let Some(module_path) = namespace
                    .surface
                    .modules
                    .get(merged_module as usize)
                    .filter(|module| module.id == merged_module)
                    .map(|module| module.path.clone())
                else {
                    return Err(CompiledRuntimeMergeError::MissingMappedModule {
                        prefix,
                        module: module.module,
                        mapped_module: merged_module,
                    });
                };
                module_defs.insert(merged_module, module.def);
                modules.push(CompiledRuntimeModuleDef {
                    module: merged_module,
                    module_path,
                    def: module.def,
                });
            }
            for value in import.values {
                let Some(merged_symbol) = namespace.map_value(prefix, value.symbol) else {
                    return Err(CompiledRuntimeMergeError::MissingValueSymbol {
                        prefix,
                        symbol: value.symbol,
                    });
                };
                if !seen_values.insert(merged_symbol) {
                    return Err(CompiledRuntimeMergeError::DuplicateValueDef {
                        symbol: merged_symbol,
                    });
                }
                values.push(CompiledRuntimeValueDef {
                    symbol: merged_symbol,
                    def: value.def,
                });
            }
        }
        modules.sort_by_key(|module| module.module);
        values.sort_by_key(|value| value.symbol);
        Ok(CompiledRuntimeMergeOutput {
            surface: Self {
                arena,
                labels,
                modules,
                values,
            },
            def_remap,
        })
    }
}

impl CompiledRuntimeImport {
    fn new() -> Self {
        Self {
            external_defs: FxHashSet::default(),
            defs: FxHashMap::default(),
            exprs: FxHashMap::default(),
            pats: FxHashMap::default(),
            refs: FxHashMap::default(),
            selects: FxHashMap::default(),
            roots: Vec::new(),
            runtime_roots: Vec::new(),
            root_exprs: Vec::new(),
            modules: Vec::new(),
            values: Vec::new(),
        }
    }

    pub(crate) fn map_def(&self, id: DefId) -> DefId {
        *self
            .defs
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime def id {} is missing", id.0))
    }

    fn is_external_def(&self, id: DefId) -> bool {
        self.external_defs.contains(&id)
    }

    fn map_expr(&self, id: ExprId) -> ExprId {
        *self
            .exprs
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime expr id {} is missing", id.0))
    }

    fn map_pat(&self, id: PatId) -> PatId {
        *self
            .pats
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime pattern id {} is missing", id.0))
    }

    fn map_ref(&self, id: RefId) -> RefId {
        *self
            .refs
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime ref id {} is missing", id.0))
    }

    fn map_select(&self, id: SelectId) -> SelectId {
        *self
            .selects
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime select id {} is missing", id.0))
    }
}

fn merge_imported_module_def_children(
    arena: &mut PolyArena,
    module: u32,
    target: DefId,
    source: DefId,
) -> Result<(), CompiledRuntimeMergeError> {
    let Some(Def::Mod {
        vis: source_vis,
        children: source_children,
    }) = arena.defs.get(source).cloned()
    else {
        return Err(CompiledRuntimeMergeError::ConflictingModuleDef { module });
    };
    let Some(Def::Mod {
        vis: target_vis,
        children: target_children,
    }) = arena.defs.get_mut(target)
    else {
        return Err(CompiledRuntimeMergeError::ConflictingModuleDef { module });
    };
    if *target_vis != source_vis {
        return Err(CompiledRuntimeMergeError::ConflictingModuleDef { module });
    }
    for child in source_children {
        if !target_children.contains(&child) {
            target_children.push(child);
        }
    }
    Ok(())
}

fn runtime_module_defs_from_namespace(
    lowering: &BodyLowering,
    namespace: &CompiledNamespaceSurface,
) -> Vec<CompiledRuntimeModuleDef> {
    let mut modules = Vec::new();
    for module in namespace
        .modules
        .iter()
        .filter(|module| !module.path.is_empty())
    {
        let Some(live_module) = lowering
            .modules
            .module_by_path(&path_from_strings(&module.path))
        else {
            continue;
        };
        let Some(def) = lowering.modules.module_def(live_module) else {
            continue;
        };
        modules.push(CompiledRuntimeModuleDef {
            module: module.id,
            module_path: module.path.clone(),
            def,
        });
    }
    modules.sort_by_key(|module| module.module);
    modules
}

fn runtime_value_defs_from_namespace(
    lowering: &BodyLowering,
    namespace: &CompiledNamespaceSurface,
) -> Vec<CompiledRuntimeValueDef> {
    let mut values = Vec::new();
    for module in &namespace.modules {
        let Some(live_module) = lowering
            .modules
            .module_by_path(&path_from_strings(&module.path))
        else {
            continue;
        };
        for value in &module.values {
            let name = sources::Name(value.name.clone());
            let Some(def) = lowering
                .modules
                .value_decls(live_module, &name)
                .into_iter()
                .find(|decl| decl.order.index() == value.order)
                .map(|decl| decl.def)
            else {
                continue;
            };
            values.push(CompiledRuntimeValueDef {
                symbol: value.symbol,
                def,
            });
        }
    }
    values.sort_by_key(|value| value.symbol);
    values
}

fn path_from_strings(path: &[String]) -> sources::Path {
    sources::Path {
        segments: path.iter().cloned().map(sources::Name).collect(),
    }
}

#[derive(Default)]
struct RuntimeImportSelection {
    defs: FxHashSet<DefId>,
    exprs: FxHashSet<ExprId>,
    pats: FxHashSet<PatId>,
    refs: FxHashSet<RefId>,
    selects: FxHashSet<SelectId>,
    required_external_defs: FxHashSet<DefId>,
}

impl RuntimeImportSelection {
    fn new(surface: &CompiledRuntimeSurface, external_defs: &FxHashSet<DefId>) -> Self {
        let mut selection = Self::default();
        for root in &surface.arena.roots {
            selection.select_def(&surface.arena, external_defs, *root);
        }
        for root in &surface.arena.runtime_roots {
            selection.select_runtime_root(&surface.arena, external_defs, root);
        }
        for expr in &surface.arena.root_exprs {
            if !root_expr_def_is_external(&surface.arena, *expr, external_defs) {
                selection.select_expr(&surface.arena, external_defs, *expr);
            }
        }
        for module in &surface.modules {
            selection.select_def(&surface.arena, external_defs, module.def);
        }
        for value in &surface.values {
            selection.select_def(&surface.arena, external_defs, value.def);
        }
        selection.select_runtime_metadata(&surface.arena, external_defs);
        selection
    }

    fn required_external_defs(&self) -> Vec<DefId> {
        let mut defs = self
            .required_external_defs
            .iter()
            .copied()
            .collect::<Vec<_>>();
        defs.sort_by_key(|def| def.0);
        defs
    }

    fn missing_external_defs(&self, available: impl IntoIterator<Item = DefId>) -> Vec<DefId> {
        let available = available.into_iter().collect::<FxHashSet<_>>();
        self.required_external_defs()
            .into_iter()
            .filter(|def| !available.contains(def))
            .collect()
    }

    fn select_runtime_root(
        &mut self,
        source: &PolyArena,
        external_defs: &FxHashSet<DefId>,
        root: &RuntimeRoot,
    ) {
        match root {
            RuntimeRoot::Expr(expr) => {
                if !root_expr_def_is_external(source, *expr, external_defs) {
                    self.select_expr(source, external_defs, *expr);
                }
            }
            RuntimeRoot::ComputedDef(def) => self.select_def(source, external_defs, *def),
        }
    }

    fn select_runtime_metadata(&mut self, source: &PolyArena, external_defs: &FxHashSet<DefId>) {
        for rule in &source.cast_rules {
            self.select_def(source, external_defs, rule.def);
        }
        for candidate in source.role_impls.iter() {
            if candidate
                .impl_def
                .is_some_and(|def| external_defs.contains(&def))
            {
                continue;
            }
            if let Some(def) = candidate.impl_def {
                self.select_def(source, external_defs, def);
            }
            for method in &candidate.methods {
                self.select_def(source, external_defs, method.requirement);
                self.select_def(source, external_defs, method.implementation);
            }
        }
    }

    fn select_def(&mut self, source: &PolyArena, external_defs: &FxHashSet<DefId>, def: DefId) {
        if external_defs.contains(&def) {
            self.required_external_defs.insert(def);
            return;
        }
        if !self.defs.insert(def) {
            return;
        }
        let Some(item) = source.defs.get(def) else {
            return;
        };
        match item {
            Def::Mod { children, .. } => {
                for child in children {
                    self.select_def(source, external_defs, *child);
                }
            }
            Def::Let { body, children, .. } => {
                if let Some(expr) = body {
                    self.select_expr(source, external_defs, *expr);
                }
                for child in children {
                    self.select_def(source, external_defs, *child);
                }
            }
            Def::Arg => {}
        }
    }

    fn select_ref(
        &mut self,
        source: &PolyArena,
        external_defs: &FxHashSet<DefId>,
        reference: RefId,
    ) {
        if !self.refs.insert(reference) {
            return;
        }
        if let Some(Some(def)) = source.refs().get(reference.0 as usize) {
            self.select_def(source, external_defs, *def);
        }
    }

    fn select_select(
        &mut self,
        source: &PolyArena,
        external_defs: &FxHashSet<DefId>,
        select: SelectId,
    ) {
        if !self.selects.insert(select) {
            return;
        }
        match source.select(select).resolution {
            Some(SelectResolution::Method { def }) => self.select_def(source, external_defs, def),
            Some(SelectResolution::TypeclassMethod { member }) => {
                self.select_def(source, external_defs, member)
            }
            Some(SelectResolution::RecordField) | None => {}
        }
    }

    fn select_expr(&mut self, source: &PolyArena, external_defs: &FxHashSet<DefId>, expr: ExprId) {
        if !self.exprs.insert(expr) {
            return;
        }
        match source.expr(expr) {
            Expr::Lit(_) | Expr::PrimitiveOp(_) => {}
            Expr::Var(reference) => self.select_ref(source, external_defs, *reference),
            Expr::App(callee, arg) | Expr::RefSet(callee, arg) => {
                self.select_expr(source, external_defs, *callee);
                self.select_expr(source, external_defs, *arg);
            }
            Expr::Lambda(param, body) => {
                self.select_pat(source, external_defs, *param);
                self.select_expr(source, external_defs, *body);
            }
            Expr::Tuple(items) | Expr::PolyVariant(_, items) => {
                for item in items {
                    self.select_expr(source, external_defs, *item);
                }
            }
            Expr::Record { fields, spread } => {
                for (_, field) in fields {
                    self.select_expr(source, external_defs, *field);
                }
                self.select_expr_spread(source, external_defs, spread);
            }
            Expr::Select(receiver, select) => {
                self.select_expr(source, external_defs, *receiver);
                self.select_select(source, external_defs, *select);
            }
            Expr::Case(scrutinee, arms) => {
                self.select_expr(source, external_defs, *scrutinee);
                for arm in arms {
                    self.select_pat(source, external_defs, arm.pat);
                    if let Some(guard) = arm.guard {
                        self.select_expr(source, external_defs, guard);
                    }
                    self.select_expr(source, external_defs, arm.body);
                }
            }
            Expr::Catch(body, arms) => {
                self.select_expr(source, external_defs, *body);
                for arm in arms {
                    if let Some(operation) = &arm.operation
                        && let Some(def) = operation.def
                    {
                        self.select_def(source, external_defs, def);
                    }
                    self.select_pat(source, external_defs, arm.pat);
                    if let Some(continuation) = arm.continuation {
                        self.select_pat(source, external_defs, continuation);
                    }
                    if let Some(guard) = arm.guard {
                        self.select_expr(source, external_defs, guard);
                    }
                    self.select_expr(source, external_defs, arm.body);
                }
            }
            Expr::Block(stmts, result) => {
                for stmt in stmts {
                    self.select_stmt(source, external_defs, stmt);
                }
                if let Some(result) = result {
                    self.select_expr(source, external_defs, *result);
                }
            }
        }
    }

    fn select_stmt(&mut self, source: &PolyArena, external_defs: &FxHashSet<DefId>, stmt: &Stmt) {
        match stmt {
            Stmt::Let(_, pat, expr) => {
                self.select_pat(source, external_defs, *pat);
                self.select_expr(source, external_defs, *expr);
            }
            Stmt::Expr(expr) => self.select_expr(source, external_defs, *expr),
            Stmt::Module(def, stmts) => {
                self.select_def(source, external_defs, *def);
                for stmt in stmts {
                    self.select_stmt(source, external_defs, stmt);
                }
            }
        }
    }

    fn select_pat(&mut self, source: &PolyArena, external_defs: &FxHashSet<DefId>, pat: PatId) {
        if !self.pats.insert(pat) {
            return;
        }
        match source.pat(pat) {
            Pat::Wild | Pat::Lit(_) => {}
            Pat::Tuple(items) | Pat::PolyVariant(_, items) => {
                for item in items {
                    self.select_pat(source, external_defs, *item);
                }
            }
            Pat::List {
                prefix,
                spread,
                suffix,
            } => {
                for item in prefix {
                    self.select_pat(source, external_defs, *item);
                }
                if let Some(spread) = spread {
                    self.select_pat(source, external_defs, *spread);
                }
                for item in suffix {
                    self.select_pat(source, external_defs, *item);
                }
            }
            Pat::Record { fields, spread } => {
                for field in fields {
                    self.select_pat(source, external_defs, field.pat);
                    if let Some(default) = field.default {
                        self.select_expr(source, external_defs, default);
                    }
                }
                self.select_def_spread(source, external_defs, spread);
            }
            Pat::Con(reference, payloads) => {
                self.select_ref(source, external_defs, *reference);
                for payload in payloads {
                    self.select_pat(source, external_defs, *payload);
                }
            }
            Pat::Ref(reference) => self.select_ref(source, external_defs, *reference),
            Pat::Var(def) => self.select_def(source, external_defs, *def),
            Pat::Or(left, right) => {
                self.select_pat(source, external_defs, *left);
                self.select_pat(source, external_defs, *right);
            }
            Pat::As(inner, binding) => {
                self.select_pat(source, external_defs, *inner);
                self.select_def(source, external_defs, *binding);
            }
        }
    }

    fn select_expr_spread(
        &mut self,
        source: &PolyArena,
        external_defs: &FxHashSet<DefId>,
        spread: &RecordSpread<ExprId>,
    ) {
        match spread {
            RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                self.select_expr(source, external_defs, *expr);
            }
            RecordSpread::None => {}
        }
    }

    fn select_def_spread(
        &mut self,
        source: &PolyArena,
        external_defs: &FxHashSet<DefId>,
        spread: &RecordSpread<DefId>,
    ) {
        match spread {
            RecordSpread::Head(def) | RecordSpread::Tail(def) => {
                self.select_def(source, external_defs, *def);
            }
            RecordSpread::None => {}
        }
    }
}

fn root_expr_def_is_external(
    source: &PolyArena,
    expr: ExprId,
    external_defs: &FxHashSet<DefId>,
) -> bool {
    source
        .root_expr_def(expr)
        .is_some_and(|def| external_defs.contains(&def))
}

fn reserve_def_ids(source: &PolyArena, target: &mut PolyArena, import: &mut CompiledRuntimeImport) {
    for id in sorted_def_ids(source) {
        if import.is_external_def(id) {
            continue;
        }
        import.defs.insert(id, target.defs.fresh());
    }
}

fn reserve_ref_ids(source: &PolyArena, target: &mut PolyArena, import: &mut CompiledRuntimeImport) {
    for index in 0..source.refs().len() {
        import.refs.insert(RefId(index as u32), target.add_ref());
    }
}

fn reserve_select_ids(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &mut CompiledRuntimeImport,
) {
    for (index, select) in source.selects().iter().enumerate() {
        import.selects.insert(
            SelectId(index as u32),
            target.add_select(select.name.clone()),
        );
    }
}

fn reserve_expr_ids(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &mut CompiledRuntimeImport,
) {
    for index in 0..source.exprs().len() {
        import
            .exprs
            .insert(ExprId(index as u32), target.reserve_expr_slot());
    }
}

fn reserve_pat_ids(source: &PolyArena, target: &mut PolyArena, import: &mut CompiledRuntimeImport) {
    for index in 0..source.pats().len() {
        import
            .pats
            .insert(PatId(index as u32), target.reserve_pat_slot());
    }
}

fn reserve_selected_def_ids(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &mut CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    for id in sorted_def_ids(source) {
        if selection.defs.contains(&id) {
            import.defs.insert(id, target.defs.fresh());
        }
    }
}

fn reserve_selected_ref_ids(
    target: &mut PolyArena,
    import: &mut CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    for id in sorted_ref_ids(&selection.refs) {
        import.refs.insert(id, target.add_ref());
    }
}

fn reserve_selected_select_ids(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &mut CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    for id in sorted_select_ids(&selection.selects) {
        import
            .selects
            .insert(id, target.add_select(source.select(id).name.clone()));
    }
}

fn reserve_selected_expr_ids(
    target: &mut PolyArena,
    import: &mut CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    for id in sorted_expr_ids(&selection.exprs) {
        import.exprs.insert(id, target.reserve_expr_slot());
    }
}

fn reserve_selected_pat_ids(
    target: &mut PolyArena,
    import: &mut CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    for id in sorted_pat_ids(&selection.pats) {
        import.pats.insert(id, target.reserve_pat_slot());
    }
}

fn import_defs(
    source: &PolyArena,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> Vec<(DefId, Def)> {
    sorted_def_ids(source)
        .into_iter()
        .filter(|source_id| !import.is_external_def(*source_id))
        .map(|source_id| {
            let target_id = import.map_def(source_id);
            let source_def = source
                .defs
                .get(source_id)
                .unwrap_or_else(|| panic!("compiled runtime def id {} is missing", source_id.0));
            (target_id, import_def(source_def, import, type_importer))
        })
        .collect()
}

fn import_selected_defs(
    source: &PolyArena,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
    selection: &RuntimeImportSelection,
) -> Vec<(DefId, Def)> {
    sorted_def_ids(source)
        .into_iter()
        .filter(|source_id| selection.defs.contains(source_id))
        .map(|source_id| {
            let target_id = import.map_def(source_id);
            let source_def = source
                .defs
                .get(source_id)
                .unwrap_or_else(|| panic!("compiled runtime def id {} is missing", source_id.0));
            (target_id, import_def(source_def, import, type_importer))
        })
        .collect()
}

fn import_def(
    def: &Def,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> Def {
    match def {
        Def::Mod { vis, children } => Def::Mod {
            vis: *vis,
            children: children.iter().map(|id| import.map_def(*id)).collect(),
        },
        Def::Let {
            vis,
            scheme,
            body,
            children,
        } => Def::Let {
            vis: *vis,
            scheme: scheme
                .as_ref()
                .map(|scheme| type_importer.import_scheme(scheme)),
            body: body.map(|id| import.map_expr(id)),
            children: children.iter().map(|id| import.map_def(*id)).collect(),
        },
        Def::Arg => Def::Arg,
    }
}

fn import_refs(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    for (index, def) in source.refs().iter().enumerate() {
        let Some(def) = def else {
            continue;
        };
        target.resolve_ref(import.map_ref(RefId(index as u32)), import.map_def(*def));
    }
}

fn import_selects(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    for (index, select) in source.selects().iter().enumerate() {
        let Some(resolution) = select.resolution else {
            continue;
        };
        target.resolve_select(
            import.map_select(SelectId(index as u32)),
            import_select_resolution(resolution, import),
        );
    }
}

fn import_exprs(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    for (index, expr) in source.exprs().iter().enumerate() {
        let id = import.map_expr(ExprId(index as u32));
        target.set_expr(id, import_expr(expr, import));
    }
}

fn import_pats(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    for (index, pat) in source.pats().iter().enumerate() {
        let id = import.map_pat(PatId(index as u32));
        target.set_pat(id, import_pat(pat, import));
    }
}

fn import_selected_refs(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    for id in sorted_ref_ids(&selection.refs) {
        let Some(Some(def)) = source.refs().get(id.0 as usize) else {
            continue;
        };
        target.resolve_ref(import.map_ref(id), import.map_def(*def));
    }
}

fn import_selected_selects(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    for id in sorted_select_ids(&selection.selects) {
        let Some(resolution) = source.select(id).resolution else {
            continue;
        };
        target.resolve_select(
            import.map_select(id),
            import_select_resolution(resolution, import),
        );
    }
}

fn import_selected_exprs(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    for id in sorted_expr_ids(&selection.exprs) {
        target.set_expr(import.map_expr(id), import_expr(source.expr(id), import));
    }
}

fn import_selected_pats(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    for id in sorted_pat_ids(&selection.pats) {
        target.set_pat(import.map_pat(id), import_pat(source.pat(id), import));
    }
}

fn import_expr(expr: &Expr, import: &CompiledRuntimeImport) -> Expr {
    match expr {
        Expr::Lit(lit) => Expr::Lit(lit.clone()),
        Expr::PrimitiveOp(op) => Expr::PrimitiveOp(*op),
        Expr::Var(id) => Expr::Var(import.map_ref(*id)),
        Expr::App(callee, arg) => Expr::App(import.map_expr(*callee), import.map_expr(*arg)),
        Expr::RefSet(place, value) => {
            Expr::RefSet(import.map_expr(*place), import.map_expr(*value))
        }
        Expr::Lambda(param, body) => Expr::Lambda(import.map_pat(*param), import.map_expr(*body)),
        Expr::Tuple(items) => Expr::Tuple(import_expr_ids(items, import)),
        Expr::Record { fields, spread } => Expr::Record {
            fields: fields
                .iter()
                .map(|(name, expr)| (name.clone(), import.map_expr(*expr)))
                .collect(),
            spread: import_expr_spread(spread, import),
        },
        Expr::PolyVariant(name, payloads) => {
            Expr::PolyVariant(name.clone(), import_expr_ids(payloads, import))
        }
        Expr::Select(receiver, select) => {
            Expr::Select(import.map_expr(*receiver), import.map_select(*select))
        }
        Expr::Case(scrutinee, arms) => Expr::Case(
            import.map_expr(*scrutinee),
            arms.iter()
                .map(|arm| import_case_arm(arm, import))
                .collect(),
        ),
        Expr::Catch(body, arms) => Expr::Catch(
            import.map_expr(*body),
            arms.iter()
                .map(|arm| import_catch_arm(arm, import))
                .collect(),
        ),
        Expr::Block(stmts, result) => Expr::Block(
            stmts.iter().map(|stmt| import_stmt(stmt, import)).collect(),
            result.map(|id| import.map_expr(id)),
        ),
    }
}

fn import_pat(pat: &Pat, import: &CompiledRuntimeImport) -> Pat {
    match pat {
        Pat::Wild => Pat::Wild,
        Pat::Lit(lit) => Pat::Lit(lit.clone()),
        Pat::Tuple(items) => Pat::Tuple(import_pat_ids(items, import)),
        Pat::List {
            prefix,
            spread,
            suffix,
        } => Pat::List {
            prefix: import_pat_ids(prefix, import),
            spread: spread.map(|id| import.map_pat(id)),
            suffix: import_pat_ids(suffix, import),
        },
        Pat::Record { fields, spread } => Pat::Record {
            fields: fields
                .iter()
                .map(|field| RecordPatField {
                    name: field.name.clone(),
                    pat: import.map_pat(field.pat),
                    default: field.default.map(|id| import.map_expr(id)),
                })
                .collect(),
            spread: import_def_spread(spread, import),
        },
        Pat::PolyVariant(name, payloads) => {
            Pat::PolyVariant(name.clone(), import_pat_ids(payloads, import))
        }
        Pat::Con(constructor, payloads) => Pat::Con(
            import.map_ref(*constructor),
            import_pat_ids(payloads, import),
        ),
        Pat::Ref(id) => Pat::Ref(import.map_ref(*id)),
        Pat::Var(id) => Pat::Var(import.map_def(*id)),
        Pat::Or(left, right) => Pat::Or(import.map_pat(*left), import.map_pat(*right)),
        Pat::As(pat, binding) => Pat::As(import.map_pat(*pat), import.map_def(*binding)),
    }
}

fn import_stmt(stmt: &Stmt, import: &CompiledRuntimeImport) -> Stmt {
    match stmt {
        Stmt::Let(vis, pat, expr) => Stmt::Let(*vis, import.map_pat(*pat), import.map_expr(*expr)),
        Stmt::Expr(expr) => Stmt::Expr(import.map_expr(*expr)),
        Stmt::Module(def, stmts) => Stmt::Module(
            import.map_def(*def),
            stmts.iter().map(|stmt| import_stmt(stmt, import)).collect(),
        ),
    }
}

fn import_case_arm(arm: &CaseArm, import: &CompiledRuntimeImport) -> CaseArm {
    CaseArm {
        pat: import.map_pat(arm.pat),
        guard: arm.guard.map(|id| import.map_expr(id)),
        body: import.map_expr(arm.body),
    }
}

fn import_catch_arm(arm: &CatchArm, import: &CompiledRuntimeImport) -> CatchArm {
    CatchArm {
        operation: arm
            .operation
            .as_ref()
            .map(|operation| import_catch_operation(operation, import)),
        pat: import.map_pat(arm.pat),
        continuation: arm.continuation.map(|id| import.map_pat(id)),
        guard: arm.guard.map(|id| import.map_expr(id)),
        body: import.map_expr(arm.body),
    }
}

fn import_catch_operation(
    operation: &CatchOperation,
    import: &CompiledRuntimeImport,
) -> CatchOperation {
    CatchOperation {
        path: operation.path.clone(),
        def: operation.def.map(|id| import.map_def(id)),
    }
}

fn import_select_resolution(
    resolution: SelectResolution,
    import: &CompiledRuntimeImport,
) -> SelectResolution {
    match resolution {
        SelectResolution::RecordField => SelectResolution::RecordField,
        SelectResolution::Method { def } => SelectResolution::Method {
            def: import.map_def(def),
        },
        SelectResolution::TypeclassMethod { member } => SelectResolution::TypeclassMethod {
            member: import.map_def(member),
        },
    }
}

fn import_runtime_root(root: &RuntimeRoot, import: &CompiledRuntimeImport) -> RuntimeRoot {
    match root {
        RuntimeRoot::Expr(id) => RuntimeRoot::Expr(import.map_expr(*id)),
        RuntimeRoot::ComputedDef(id) => RuntimeRoot::ComputedDef(import.map_def(*id)),
    }
}

fn runtime_root_is_external(root: &RuntimeRoot, import: &CompiledRuntimeImport) -> bool {
    match root {
        RuntimeRoot::Expr(_) => false,
        RuntimeRoot::ComputedDef(def) => import.is_external_def(*def),
    }
}

fn runtime_root_is_selected(root: &RuntimeRoot, selection: &RuntimeImportSelection) -> bool {
    match root {
        RuntimeRoot::Expr(expr) => selection.exprs.contains(expr),
        RuntimeRoot::ComputedDef(def) => selection.defs.contains(def),
    }
}

fn root_expr_is_external(source: &PolyArena, expr: ExprId, import: &CompiledRuntimeImport) -> bool {
    source
        .root_expr_def(expr)
        .is_some_and(|def| import.is_external_def(def))
}

fn import_root_expr_defs(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
) {
    let mut pairs = source.root_expr_defs.iter().collect::<Vec<_>>();
    pairs.sort_by_key(|(expr, _)| expr.0);
    for (expr, def) in pairs {
        if import.is_external_def(*def) {
            continue;
        }
        target
            .root_expr_defs
            .insert(import.map_expr(*expr), import.map_def(*def));
    }
}

fn import_selected_root_expr_defs(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    let mut pairs = source.root_expr_defs.iter().collect::<Vec<_>>();
    pairs.sort_by_key(|(expr, _)| expr.0);
    for (expr, def) in pairs {
        if !selection.exprs.contains(expr) || !selection.defs.contains(def) {
            continue;
        }
        target
            .root_expr_defs
            .insert(import.map_expr(*expr), import.map_def(*def));
    }
}

fn import_cast_rules(
    source: &PolyArena,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> Vec<CastRule> {
    source
        .cast_rules
        .iter()
        .filter(|rule| !import.is_external_def(rule.def))
        .map(|rule| CastRule {
            def: import.map_def(rule.def),
            source: rule.source.clone(),
            target: rule.target.clone(),
            scheme: type_importer.import_scheme(&rule.scheme),
            kind: rule.kind,
        })
        .collect()
}

fn import_selected_cast_rules(
    source: &PolyArena,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
    selection: &RuntimeImportSelection,
) -> Vec<CastRule> {
    source
        .cast_rules
        .iter()
        .filter(|rule| selection.defs.contains(&rule.def))
        .map(|rule| CastRule {
            def: import.map_def(rule.def),
            source: rule.source.clone(),
            target: rule.target.clone(),
            scheme: type_importer.import_scheme(&rule.scheme),
            kind: rule.kind,
        })
        .collect()
}

fn import_role_impls(
    source: &PolyArena,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> Vec<RoleImplCandidate> {
    source
        .role_impls
        .iter()
        .filter(|candidate| {
            candidate
                .impl_def
                .is_none_or(|def| !import.is_external_def(def))
        })
        .map(|candidate| import_role_impl_candidate(candidate, import, type_importer))
        .collect()
}

fn import_selected_role_impls(
    source: &PolyArena,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
    selection: &RuntimeImportSelection,
) -> Vec<RoleImplCandidate> {
    source
        .role_impls
        .iter()
        .filter(|candidate| {
            candidate
                .impl_def
                .is_none_or(|def| selection.defs.contains(&def))
        })
        .map(|candidate| import_role_impl_candidate(candidate, import, type_importer))
        .collect()
}

fn import_role_impl_candidate(
    candidate: &RoleImplCandidate,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> RoleImplCandidate {
    RoleImplCandidate {
        impl_def: candidate.impl_def.map(|id| import.map_def(id)),
        role: candidate.role.clone(),
        inputs: candidate
            .inputs
            .iter()
            .map(|arg| import_role_constraint_arg(arg, type_importer))
            .collect(),
        associated: candidate
            .associated
            .iter()
            .map(|associated| RoleAssociatedConstraint {
                name: associated.name.clone(),
                value: import_role_constraint_arg(&associated.value, type_importer),
            })
            .collect(),
        prerequisites: candidate
            .prerequisites
            .iter()
            .map(|constraint| import_role_constraint(constraint, type_importer))
            .collect(),
        methods: candidate
            .methods
            .iter()
            .map(|method| RoleImplMethod {
                requirement: import.map_def(method.requirement),
                implementation: import.map_def(method.implementation),
            })
            .collect(),
    }
}

fn import_role_constraint(
    constraint: &RoleConstraint,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> RoleConstraint {
    RoleConstraint {
        role: constraint.role.clone(),
        inputs: constraint
            .inputs
            .iter()
            .map(|arg| import_role_constraint_arg(arg, type_importer))
            .collect(),
        associated: constraint
            .associated
            .iter()
            .map(|associated| RoleAssociatedConstraint {
                name: associated.name.clone(),
                value: import_role_constraint_arg(&associated.value, type_importer),
            })
            .collect(),
    }
}

fn import_role_constraint_arg(
    arg: &RoleConstraintArg,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> RoleConstraintArg {
    RoleConstraintArg {
        lower: type_importer.import_pos_id(arg.lower),
        upper: type_importer.import_neg_id(arg.upper),
    }
}

fn import_effect_operations(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
) {
    let mut operations = source.effect_operations.iter().collect::<Vec<_>>();
    operations.sort_by_key(|(def, _)| def.0);
    for (def, operation) in operations {
        if import.is_external_def(*def) {
            continue;
        }
        target.effect_operations.insert(
            import.map_def(*def),
            EffectOperation {
                path: operation.path.clone(),
            },
        );
    }
}

fn import_selected_effect_operations(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    let mut operations = source.effect_operations.iter().collect::<Vec<_>>();
    operations.sort_by_key(|(def, _)| def.0);
    for (def, operation) in operations {
        if !selection.defs.contains(def) {
            continue;
        }
        target.effect_operations.insert(
            import.map_def(*def),
            EffectOperation {
                path: operation.path.clone(),
            },
        );
    }
}

fn import_synthetic_var_effects(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
) {
    let mut effects = source.synthetic_var_effects.iter().collect::<Vec<_>>();
    effects.sort_by(|left, right| left.effect_path.cmp(&right.effect_path));
    for effect in effects {
        match (
            effect
                .get_operation
                .and_then(|def| import.defs.get(&def).copied()),
            effect
                .set_operation
                .and_then(|def| import.defs.get(&def).copied()),
        ) {
            (Some(get_operation), Some(set_operation)) => {
                target.register_synthetic_var_effect_operations(
                    effect.effect_path.clone(),
                    get_operation,
                    set_operation,
                );
            }
            _ => target.register_synthetic_var_effect(effect.effect_path.clone()),
        }
    }
}

fn import_constructors(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    let mut constructors = source.constructors.iter().collect::<Vec<_>>();
    constructors.sort_by_key(|(def, _)| def.0);
    for (def, constructor) in constructors {
        if import.is_external_def(*def) {
            continue;
        }
        target.constructors.insert(
            import.map_def(*def),
            Constructor {
                owner_path: constructor.owner_path.clone(),
                name: constructor.name.clone(),
                arity: constructor.arity,
            },
        );
    }
}

fn import_selected_constructors(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    let mut constructors = source.constructors.iter().collect::<Vec<_>>();
    constructors.sort_by_key(|(def, _)| def.0);
    for (def, constructor) in constructors {
        if !selection.defs.contains(def) {
            continue;
        }
        target.constructors.insert(
            import.map_def(*def),
            Constructor {
                owner_path: constructor.owner_path.clone(),
                name: constructor.name.clone(),
                arity: constructor.arity,
            },
        );
    }
}

fn import_arg_effect_contracts(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
) {
    let mut contracts = source.arg_effect_contracts.iter().collect::<Vec<_>>();
    contracts.sort_by_key(|(def, _)| def.0);
    for (def, contract) in contracts {
        if import.is_external_def(*def) {
            continue;
        }
        target
            .arg_effect_contracts
            .insert(import.map_def(*def), import_arg_effect_contract(contract));
    }
}

fn import_selected_arg_effect_contracts(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    let mut contracts = source.arg_effect_contracts.iter().collect::<Vec<_>>();
    contracts.sort_by_key(|(def, _)| def.0);
    for (def, contract) in contracts {
        if !selection.defs.contains(def) {
            continue;
        }
        target
            .arg_effect_contracts
            .insert(import.map_def(*def), import_arg_effect_contract(contract));
    }
}

fn import_arg_effect_contract(contract: &ArgEffectContract) -> ArgEffectContract {
    contract.clone()
}

fn import_field_projections(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
) {
    let mut projections = source.field_projections.iter().copied().collect::<Vec<_>>();
    projections.sort_by_key(|def| def.0);
    for def in projections {
        if import.is_external_def(def) {
            continue;
        }
        target.field_projections.insert(import.map_def(def));
    }
}

fn import_selected_field_projections(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    let mut projections = source.field_projections.iter().copied().collect::<Vec<_>>();
    projections.sort_by_key(|def| def.0);
    for def in projections {
        if !selection.defs.contains(&def) {
            continue;
        }
        target.field_projections.insert(import.map_def(def));
    }
}

fn import_labels(source: &DumpLabels, target: &mut DumpLabels, import: &CompiledRuntimeImport) {
    let mut def_labels = source.def_labels().collect::<Vec<_>>();
    def_labels.sort_by_key(|(def, _)| def.0);
    for (def, label) in def_labels {
        if import.is_external_def(def) {
            continue;
        }
        target.set_def_label(import.map_def(def), label);
    }

    let mut ref_labels = source.ref_labels().collect::<Vec<_>>();
    ref_labels.sort_by_key(|(reference, _)| reference.0);
    for (reference, label) in ref_labels {
        target.set_ref_label(import.map_ref(reference), label);
    }
}

fn import_selected_labels(
    source: &DumpLabels,
    target: &mut DumpLabels,
    import: &CompiledRuntimeImport,
    selection: &RuntimeImportSelection,
) {
    let mut def_labels = source.def_labels().collect::<Vec<_>>();
    def_labels.sort_by_key(|(def, _)| def.0);
    for (def, label) in def_labels {
        if !selection.defs.contains(&def) {
            continue;
        }
        target.set_def_label(import.map_def(def), label);
    }

    let mut ref_labels = source.ref_labels().collect::<Vec<_>>();
    ref_labels.sort_by_key(|(reference, _)| reference.0);
    for (reference, label) in ref_labels {
        if !selection.refs.contains(&reference) {
            continue;
        }
        target.set_ref_label(import.map_ref(reference), label);
    }
}

fn import_expr_ids(ids: &[ExprId], import: &CompiledRuntimeImport) -> Vec<ExprId> {
    ids.iter().map(|id| import.map_expr(*id)).collect()
}

fn import_pat_ids(ids: &[PatId], import: &CompiledRuntimeImport) -> Vec<PatId> {
    ids.iter().map(|id| import.map_pat(*id)).collect()
}

fn import_expr_spread(
    spread: &RecordSpread<ExprId>,
    import: &CompiledRuntimeImport,
) -> RecordSpread<ExprId> {
    match spread {
        RecordSpread::Head(id) => RecordSpread::Head(import.map_expr(*id)),
        RecordSpread::Tail(id) => RecordSpread::Tail(import.map_expr(*id)),
        RecordSpread::None => RecordSpread::None,
    }
}

fn import_def_spread(
    spread: &RecordSpread<DefId>,
    import: &CompiledRuntimeImport,
) -> RecordSpread<DefId> {
    match spread {
        RecordSpread::Head(id) => RecordSpread::Head(import.map_def(*id)),
        RecordSpread::Tail(id) => RecordSpread::Tail(import.map_def(*id)),
        RecordSpread::None => RecordSpread::None,
    }
}

fn sorted_def_ids(arena: &PolyArena) -> Vec<DefId> {
    let mut ids = arena.defs.iter().map(|(id, _)| id).collect::<Vec<_>>();
    ids.sort_by_key(|id| id.0);
    ids
}

fn sorted_ref_ids(ids: &FxHashSet<RefId>) -> Vec<RefId> {
    let mut ids = ids.iter().copied().collect::<Vec<_>>();
    ids.sort_by_key(|id| id.0);
    ids
}

fn sorted_select_ids(ids: &FxHashSet<SelectId>) -> Vec<SelectId> {
    let mut ids = ids.iter().copied().collect::<Vec<_>>();
    ids.sort_by_key(|id| id.0);
    ids
}

fn sorted_expr_ids(ids: &FxHashSet<ExprId>) -> Vec<ExprId> {
    let mut ids = ids.iter().copied().collect::<Vec<_>>();
    ids.sort_by_key(|id| id.0);
    ids
}

fn sorted_pat_ids(ids: &FxHashSet<PatId>) -> Vec<PatId> {
    let mut ids = ids.iter().copied().collect::<Vec<_>>();
    ids.sort_by_key(|id| id.0);
    ids
}

#[cfg(test)]
mod tests {
    use sources::{Name, Path, SourceFile};

    use crate::lowering::{
        BodyLoweringPrefix, lower_loaded_files, lower_root_loaded_file_with_prefix,
    };
    use crate::{
        CompiledLoweringSurface, CompiledNamespaceSurface, ConstructorPayload, ModuleOrder,
    };

    use super::*;

    #[test]
    fn runtime_surface_import_remaps_lowered_arena_ids() {
        let loaded = sources::load(vec![
            source(&[], "mod ops;\npub use ops::*\n"),
            source(
                &["ops"],
                "pub act signal:\n  pub ping: () -> int\n\npub struct Box { value: int }\npub id x = x\npub make = Box { value: 1 }\n",
            ),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        assert!(lowering.session.poly.effect_operations.len() > 0);
        assert!(lowering.session.poly.constructors.len() > 0);

        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let runtime = CompiledRuntimeSurface::from_lowering_with_namespace(&lowering, &namespace);
        assert!(!runtime.modules.is_empty());
        assert!(!runtime.values.is_empty());
        let mut target = PolyArena::new();
        let prefix_def = target.defs.fresh();
        target.defs.set(prefix_def, Def::Arg);
        let mut labels = DumpLabels::new();

        let import = runtime.import_into(&mut target, &mut labels);

        assert_eq!(import.defs.len(), runtime.arena.defs.len());
        assert_eq!(import.exprs.len(), runtime.arena.exprs().len());
        assert_eq!(import.pats.len(), runtime.arena.pats().len());
        assert_eq!(import.refs.len(), runtime.arena.refs().len());
        assert_eq!(import.selects.len(), runtime.arena.selects().len());
        assert_eq!(import.roots.len(), runtime.arena.roots.len());
        assert_eq!(
            import.runtime_roots.len(),
            runtime.arena.runtime_roots.len()
        );
        assert_eq!(import.root_exprs.len(), runtime.arena.root_exprs.len());
        assert_eq!(import.modules.len(), runtime.modules.len());
        assert_eq!(import.values.len(), runtime.values.len());
        assert_eq!(
            target.effect_operations.len(),
            runtime.arena.effect_operations.len()
        );
        assert_eq!(target.constructors.len(), runtime.arena.constructors.len());
        assert!(import.defs.iter().any(|(source, target)| source != target));
        assert!(target.defs.get(prefix_def).is_some());

        for root in &import.roots {
            assert!(target.defs.get(*root).is_some());
        }
        for value in &import.values {
            assert!(target.defs.get(value.def).is_some());
        }
        for module in &import.modules {
            assert!(target.defs.get(module.def).is_some());
        }
        for root in &import.runtime_roots {
            match root {
                RuntimeRoot::Expr(expr) => {
                    target.expr(*expr);
                }
                RuntimeRoot::ComputedDef(def) => {
                    assert!(target.defs.get(*def).is_some());
                }
            }
        }
    }

    #[test]
    fn runtime_surface_merge_remaps_modules_values_and_arena_ids() {
        let left = compiled_runtime_surface(&["left"], "pub id x = x\n");
        let right = compiled_runtime_surface(&["right"], "pub value = 42\n");
        let namespace = CompiledNamespaceSurface::merge_prefixes_with_remap([
            &left.namespace,
            &right.namespace,
        ])
        .unwrap();
        let output = CompiledRuntimeSurface::merge_prefixes_with_remap(
            [&left.runtime, &right.runtime],
            &namespace,
        )
        .unwrap();
        let runtime = &output.surface;
        let namespace_index = crate::CompiledNamespaceIndex::new(&namespace.surface);
        let left_id = namespace_index
            .exported_value_symbol(&["left".to_string()], "id")
            .unwrap();
        let right_value = namespace_index
            .exported_value_symbol(&["right".to_string()], "value")
            .unwrap();
        let left_module = namespace_index.exported_module_id(&[], "left").unwrap();
        let right_module = namespace_index.exported_module_id(&[], "right").unwrap();

        assert_eq!(
            namespace.map_value(0, left.value_symbol("id")),
            Some(left_id)
        );
        assert_eq!(
            namespace.map_value(1, right.value_symbol("value")),
            Some(right_value)
        );
        assert_eq!(
            output.map_def(0, left.value_def("id")),
            runtime
                .values
                .iter()
                .find(|value| value.symbol == left_id)
                .map(|value| value.def)
        );
        assert_eq!(runtime.values.len(), 2);
        assert!(runtime.values.iter().any(|value| value.symbol == left_id));
        assert!(
            runtime
                .values
                .iter()
                .any(|value| value.symbol == right_value)
        );
        assert!(runtime.modules.iter().any(|module| {
            module.module == left_module && module.module_path == vec!["left".to_string()]
        }));
        assert!(runtime.modules.iter().any(|module| {
            module.module == right_module && module.module_path == vec!["right".to_string()]
        }));
        for value in &runtime.values {
            assert!(runtime.arena.defs.get(value.def).is_some());
        }
        for module in &runtime.modules {
            assert!(runtime.arena.defs.get(module.def).is_some());
        }
    }

    #[test]
    fn runtime_surface_merge_rejects_value_without_namespace_remap() {
        let mut unit = compiled_runtime_surface(&["unit"], "pub id x = x\n");
        let def = unit.runtime.values[0].def;
        unit.runtime.values.push(CompiledRuntimeValueDef {
            symbol: u32::MAX,
            def,
        });
        let namespace =
            CompiledNamespaceSurface::merge_prefixes_with_remap([&unit.namespace]).unwrap();
        let error = match CompiledRuntimeSurface::merge_prefixes([&unit.runtime], &namespace) {
            Ok(_) => panic!("runtime merge should reject a value without a namespace remap"),
            Err(error) => error,
        };

        assert_eq!(
            error,
            CompiledRuntimeMergeError::MissingValueSymbol {
                prefix: 0,
                symbol: u32::MAX,
            }
        );
    }

    #[test]
    fn runtime_surface_merge_coalesces_shared_parent_module_defs() {
        let left = compiled_runtime_surface_from_files(vec![
            source(&[], "mod a;\n"),
            source(&["a"], "mod b;\n"),
            source(&["a", "b"], "pub x = 1\n"),
        ]);
        let right = compiled_runtime_surface_from_files(vec![
            source(&[], "mod a;\n"),
            source(&["a"], "mod c;\n"),
            source(&["a", "c"], "pub y = 2\n"),
        ]);
        let namespace = CompiledNamespaceSurface::merge_prefixes_with_remap([
            &left.namespace,
            &right.namespace,
        ])
        .unwrap();
        let runtime = CompiledRuntimeSurface::merge_prefixes_with_remap(
            [&left.runtime, &right.runtime],
            &namespace,
        )
        .unwrap();
        let namespace_index = crate::CompiledNamespaceIndex::new(&namespace.surface);
        let a_module = namespace_index.exported_module_id(&[], "a").unwrap();
        let b_module = namespace_index
            .exported_module_id(&["a".to_string()], "b")
            .unwrap();
        let c_module = namespace_index
            .exported_module_id(&["a".to_string()], "c")
            .unwrap();
        let a_def = runtime
            .surface
            .modules
            .iter()
            .find(|module| module.module == a_module)
            .unwrap()
            .def;
        let b_def = runtime
            .surface
            .modules
            .iter()
            .find(|module| module.module == b_module)
            .unwrap()
            .def;
        let c_def = runtime
            .surface
            .modules
            .iter()
            .find(|module| module.module == c_module)
            .unwrap()
            .def;

        assert_eq!(
            runtime
                .surface
                .modules
                .iter()
                .filter(|module| module.module == a_module)
                .count(),
            1
        );
        let Some(Def::Mod { children, .. }) = runtime.surface.arena.defs.get(a_def) else {
            panic!("merged parent module should remain a module def");
        };
        assert!(children.contains(&b_def));
        assert!(children.contains(&c_def));
    }

    #[test]
    fn compiled_unit_surface_prefix_rebuilds_module_table_without_source_modules() {
        let loaded = sources::load(vec![
            source(&[], "mod ops;\npub use ops::*\n"),
            source(
                &["ops"],
                "pub act signal:\n  pub ping: () -> int\n\npub struct Box { value: int }\n",
            ),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let lowering_surface =
            CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
        let runtime = CompiledRuntimeSurface::from_lowering_with_namespace(&lowering, &namespace);
        let prefix = BodyLoweringPrefix::from_compiled_unit_surfaces(
            &namespace,
            &lowering_surface,
            &runtime,
        )
        .expect("compiled surfaces should rebuild a root prefix");
        let root = sources::load(vec![source(
            &[],
            "my boxed = Box { value: 1 }\nmy value = boxed.value\nmy handled = catch signal::ping():\n    signal::ping(), k -> k 1\n    v -> v\n",
        )])
        .into_iter()
        .next()
        .unwrap();

        let lowered = lower_root_loaded_file_with_prefix(&prefix, &root).unwrap();

        assert_eq!(lowered.errors, Vec::new());
    }

    #[test]
    fn runtime_surface_prefix_remaps_module_defs_for_later_root_lowering() {
        let loaded = sources::load(vec![
            source(&[], "mod ops;\npub use ops::*\n"),
            source(
                &["ops"],
                "pub act signal:\n  pub ping: () -> int\n\npub struct Box { value: int }\npub id x = x\n",
            ),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let runtime = CompiledRuntimeSurface::from_lowering(&lowering);
        let prefix = BodyLoweringPrefix::from_runtime_surface(&runtime, &lowering.modules);
        let root = sources::load(vec![source(
            &[],
            "my boxed = Box { value: 1 }\nmy value = boxed.value\nmy request = signal::ping()\nmy same = id value\n",
        )])
        .into_iter()
        .next()
        .unwrap();

        let lowered = lower_root_loaded_file_with_prefix(&prefix, &root).unwrap();

        assert_eq!(lowered.errors, Vec::new());
        let root = lowered.modules.root_id();
        let site = ModuleOrder::from_index(u32::MAX);
        let box_ctor = lowered
            .modules
            .value_path_at(root, &[Name("Box".into())], site)
            .expect("imported struct constructor should resolve");
        assert!(lowered.session.poly.defs.get(box_ctor).is_some());
        let operation = lowered
            .modules
            .act_operation_decls_at(root, &[Name("signal".into())], site)
            .into_iter()
            .find(|operation| operation.name == Name("ping".into()))
            .and_then(|operation| operation.def)
            .expect("imported act operation should resolve to a remapped def");
        assert!(lowered.session.poly.defs.get(operation).is_some());
    }

    #[test]
    fn compiled_unit_prefix_marks_imported_runtime_defs() {
        let loaded = sources::load(vec![
            source(&[], "mod deps;\npub use deps::*\n"),
            source(&["deps"], "pub id x = x\n"),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let lowering_surface =
            CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
        let runtime = CompiledRuntimeSurface::from_lowering_with_namespace(&lowering, &namespace);
        let prefix = BodyLoweringPrefix::from_compiled_unit_surfaces(
            &namespace,
            &lowering_surface,
            &runtime,
        )
        .expect("compiled surfaces should rebuild a root prefix");
        let namespace_index = crate::CompiledNamespaceIndex::new(&namespace);
        let id_symbol = namespace_index
            .exported_value_symbol(&["deps".to_string()], "id")
            .expect("dependency value should be exported");
        let imported_id = prefix
            .runtime()
            .value_def(id_symbol)
            .expect("prefix should retain a symbol-keyed imported value");
        let root = sources::load(vec![source(&[], "my y = id 1\n")])
            .into_iter()
            .next()
            .unwrap();

        let lowered = lower_root_loaded_file_with_prefix(&prefix, &root).unwrap();

        assert_eq!(lowered.errors, Vec::new());
        assert!(prefix.runtime().contains_def(imported_id));
        assert!(lowered.prefix_runtime().contains_def(imported_id));
        assert_eq!(
            prefix.runtime().def_count(),
            lowered.prefix_runtime().def_count()
        );
        assert_eq!(
            prefix.runtime().value_count(),
            lowered.prefix_runtime().value_count()
        );
        let site = ModuleOrder::from_index(u32::MAX);
        let root = lowered.modules.root_id();
        let id = lowered
            .modules
            .value_path_at(root, &[Name("id".into())], site)
            .expect("imported id should resolve");
        let y = lowered
            .modules
            .value_path_at(root, &[Name("y".into())], site)
            .expect("suffix binding should resolve");
        assert!(lowered.prefix_runtime().contains_def(id));
        assert!(!lowered.prefix_runtime().contains_def(y));
    }

    #[test]
    fn runtime_surface_import_resolves_external_defs_without_copying_them() {
        let loaded = sources::load(vec![
            source(&[], "mod deps;\npub use deps::*\n"),
            source(&["deps"], "pub id x = x\n"),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let lowering_surface =
            CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
        let runtime = CompiledRuntimeSurface::from_lowering_with_namespace(&lowering, &namespace);
        let prefix = BodyLoweringPrefix::from_compiled_unit_surfaces(
            &namespace,
            &lowering_surface,
            &runtime,
        )
        .expect("compiled surfaces should rebuild a root prefix");
        let root = sources::load(vec![source(&[], "pub y = id 1\n")])
            .into_iter()
            .next()
            .unwrap();
        let lowered = lower_root_loaded_file_with_prefix(&prefix, &root).unwrap();
        assert_eq!(lowered.errors, Vec::new());
        let namespace = CompiledNamespaceSurface::from_module_table(&lowered.modules);
        let runtime = CompiledRuntimeSurface::from_lowering_with_namespace(&lowered, &namespace);
        let external_defs = lowered.prefix_runtime().def_ids().collect::<FxHashSet<_>>();
        let mut target = lowered.session.poly.clone();
        let old_def_count = target.defs.len();
        let external_pairs = external_defs
            .iter()
            .map(|def| (*def, *def))
            .collect::<Vec<_>>();
        let mut labels = DumpLabels::new();

        let import =
            runtime.import_into_with_external_defs(&mut target, &mut labels, external_pairs);

        let local_def_count = runtime.arena.defs.len() - external_defs.len();
        assert_eq!(target.defs.len(), old_def_count + local_def_count);
        for def in &external_defs {
            assert_eq!(import.map_def(*def), *def);
        }
        let site = ModuleOrder::from_index(u32::MAX);
        let root = lowered.modules.root_id();
        let y = lowered
            .modules
            .value_path_at(root, &[Name("y".into())], site)
            .expect("suffix binding should resolve");
        assert!(!external_defs.contains(&y));
        assert_ne!(import.map_def(y), y);
        assert!(target.defs.get(import.map_def(y)).is_some());
    }

    #[test]
    fn runtime_surface_prefix_reads_lowered_constructor_and_operation_signatures() {
        let loaded = sources::load(vec![
            source(&[], "mod ops;\npub use ops::*\n"),
            source(
                &["ops"],
                "pub act signal:\n  pub ping: () -> int\n\npub struct Box { value: int }\n",
            ),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let lowering_surface =
            CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
        let runtime = CompiledRuntimeSurface::from_lowering(&lowering);
        let mut modules = lowering.modules.clone();
        clear_test_signatures(&mut modules);
        let prefix = BodyLoweringPrefix::from_runtime_surface_with_lowering(
            &runtime,
            &lowering_surface,
            &modules,
        );
        let root = sources::load(vec![source(
            &[],
            "my boxed = Box { value: 1 }\nmy value = boxed.value\nmy handled = catch signal::ping():\n    signal::ping(), k -> k 1\n    v -> v\n",
        )])
        .into_iter()
        .next()
        .unwrap();

        let lowered = lower_root_loaded_file_with_prefix(&prefix, &root).unwrap();

        assert_eq!(lowered.errors, Vec::new());
    }

    #[test]
    fn runtime_surface_prefix_reads_lowered_role_method_signatures() {
        let loaded = sources::load(vec![
            source(&[], "mod roles;\npub use roles::*\n"),
            source(&["roles"], "pub role Display 'a:\n  pub x.display: unit\n"),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let lowering_surface =
            CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
        let runtime = CompiledRuntimeSurface::from_lowering(&lowering);
        let mut modules = lowering.modules.clone();
        clear_test_signatures(&mut modules);
        let prefix = BodyLoweringPrefix::from_runtime_surface_with_lowering(
            &runtime,
            &lowering_surface,
            &modules,
        );
        let root = sources::load(vec![source(
            &[],
            "impl int: Display:\n  pub x.display = 1\n",
        )])
        .into_iter()
        .next()
        .unwrap();

        let lowered = lower_root_loaded_file_with_prefix(&prefix, &root).unwrap();

        let errors = format!("{:?}", lowered.errors);
        assert!(
            errors.contains("TypeMismatch"),
            "lowered role method signature should constrain downstream impl bodies: {errors}"
        );
    }

    fn clear_test_signatures(modules: &mut crate::ModuleTable) {
        for constructor in modules.constructors.values_mut() {
            match &mut constructor.payload {
                ConstructorPayload::Record(fields) => {
                    for field in fields {
                        field.ty = None;
                    }
                }
                ConstructorPayload::Tuple(items) => {
                    for item in items {
                        item.ty = None;
                    }
                }
                ConstructorPayload::Unit => {}
            }
        }

        for ops in modules.act_ops.values_mut() {
            for op in ops {
                op.signature = None;
            }
        }

        for methods in modules.role_methods.values_mut() {
            for method in methods {
                method.signature = None;
            }
        }
    }

    struct RuntimeSurfaceFixture {
        path: Vec<String>,
        namespace: CompiledNamespaceSurface,
        runtime: CompiledRuntimeSurface,
    }

    impl RuntimeSurfaceFixture {
        fn value_symbol(&self, name: &str) -> u32 {
            crate::CompiledNamespaceIndex::new(&self.namespace)
                .exported_value_symbol(&self.path, name)
                .unwrap()
        }

        fn value_def(&self, name: &str) -> DefId {
            let symbol = self.value_symbol(name);
            self.runtime
                .values
                .iter()
                .find(|value| value.symbol == symbol)
                .map(|value| value.def)
                .unwrap()
        }
    }

    fn compiled_runtime_surface(module: &[&str], text: &str) -> RuntimeSurfaceFixture {
        assert_eq!(module.len(), 1);
        let root = format!("mod {};\n", module[0]);
        compiled_runtime_surface_from_files(vec![source(&[], &root), source(module, text)])
    }

    fn compiled_runtime_surface_from_files(files: Vec<SourceFile>) -> RuntimeSurfaceFixture {
        let path = files.last().unwrap().module_path.segments.clone();
        let loaded = sources::load(files);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let runtime = CompiledRuntimeSurface::from_lowering_with_namespace(&lowering, &namespace);
        RuntimeSurfaceFixture {
            path: path.into_iter().map(|segment| segment.0).collect(),
            namespace,
            runtime,
        }
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
