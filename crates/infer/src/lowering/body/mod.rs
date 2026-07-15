//! Extracted lowering implementation.

pub(super) mod act;
pub(super) mod error_decl;
pub(super) mod impl_decl;
pub(super) mod methods;
pub(super) mod register;
pub(super) mod role;
#[cfg(test)]
mod shadow_dirty_oracle_tests;
pub(super) mod signature_helpers;
#[cfg(test)]
mod skip_parity_tests;
#[cfg(test)]
mod stage0_tests;
pub(super) mod type_decl;

use super::*;
use crate::analysis::AnalysisTiming;
use crate::constraints::ConstraintTiming;
use crate::source_range_for_name;
use register::*;
use signature_helpers::*;

pub struct BodyLowering {
    pub session: AnalysisSession,
    pub modules: ModuleTable,
    pub typing: Typing,
    pub labels: DumpLabels,
    pub errors: Vec<BodyLoweringError>,
    pub timing: BodyLoweringTiming,
    pub(crate) role_impl_conformance_contracts:
        Vec<crate::role_impl_conformance::RoleImplConformanceContract>,
    #[cfg(test)]
    receiverless_conformance_shadow: Vec<ReceiverlessConformanceShadowWitness>,
    #[cfg(test)]
    receiver_conformance_shadow: Vec<ReceiverConformanceShadowWitness>,
    #[cfg(test)]
    conformance_batch_events: Vec<ConformanceBatchEvent>,
    prefix_runtime: BodyLoweringPrefixRuntime,
}

#[derive(Clone)]
pub struct BodyLoweringPrefix {
    poly: poly::expr::Arena,
    boundary: crate::CompiledBoundaryInterface,
    modules: ModuleTable,
    labels: DumpLabels,
    errors: Vec<BodyLoweringError>,
    runtime: BodyLoweringPrefixRuntime,
}

#[derive(Clone, Debug, Default)]
pub struct BodyLoweringPrefixRuntime {
    defs: FxHashSet<DefId>,
    modules: FxHashMap<u32, BodyLoweringPrefixRuntimeModuleDef>,
    values: FxHashMap<u32, BodyLoweringPrefixRuntimeValueDef>,
    type_field_methods: Vec<BodyLoweringPrefixRuntimeTypeFieldMethodDef>,
    casts: Vec<BodyLoweringPrefixRuntimeCastDef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BodyLoweringPrefixRuntimeModuleDef {
    pub module: u32,
    pub module_path: Vec<String>,
    pub def: DefId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BodyLoweringPrefixRuntimeValueDef {
    pub symbol: u32,
    pub value_path: Vec<String>,
    pub def: DefId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BodyLoweringPrefixRuntimeTypeFieldMethodDef {
    pub owner_type_path: Vec<String>,
    pub name: String,
    pub receiver_kind: TypeMethodReceiver,
    pub def: DefId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BodyLoweringPrefixRuntimeCastDef {
    pub source_type_path: Vec<String>,
    pub target_type_path: Vec<String>,
    pub ordinal: u32,
    pub def: DefId,
}

impl BodyLowering {
    pub fn prefix_runtime(&self) -> &BodyLoweringPrefixRuntime {
        &self.prefix_runtime
    }

    #[cfg(test)]
    pub(crate) fn role_impl_conformance_contracts(
        &self,
    ) -> &[crate::role_impl_conformance::RoleImplConformanceContract] {
        &self.role_impl_conformance_contracts
    }

    #[cfg(test)]
    pub(crate) fn receiverless_conformance_shadow(
        &self,
    ) -> &[ReceiverlessConformanceShadowWitness] {
        &self.receiverless_conformance_shadow
    }

    #[cfg(test)]
    pub(crate) fn receiver_conformance_shadow(&self) -> &[ReceiverConformanceShadowWitness] {
        &self.receiver_conformance_shadow
    }

    #[cfg(test)]
    pub(crate) fn conformance_batch_events(&self) -> &[ConformanceBatchEvent] {
        &self.conformance_batch_events
    }

    pub fn into_prefix(self) -> BodyLoweringPrefix {
        let runtime = BodyLoweringPrefixRuntime::from_lowering(&self);
        // Source conformance is consumed before artifact/prefix construction in later stages.
        // Prefixes contain already-compiled units, so they do not carry source contracts forward.
        let _role_impl_conformance_contracts = self.role_impl_conformance_contracts;
        BodyLoweringPrefix {
            poly: self.session.poly,
            boundary: crate::CompiledBoundaryInterface::empty(),
            modules: self.modules,
            labels: self.labels,
            errors: self.errors,
            runtime,
        }
    }
}

impl BodyLoweringPrefix {
    pub fn runtime(&self) -> &BodyLoweringPrefixRuntime {
        &self.runtime
    }

    #[cfg(test)]
    pub(crate) fn imported_boundary_for_test(&self) -> &crate::CompiledBoundaryInterface {
        &self.boundary
    }

    /// Build a root-lowering prefix from a runtime surface and the matching
    /// lowering environment from the same source unit.
    ///
    /// The runtime surface remaps every process-local `DefId` while importing
    /// into a fresh arena, so the module table must be remapped with the same
    /// import before later root files can resolve constructors, effect
    /// operations, methods, casts, and ordinary values against it.
    pub fn from_runtime_surface(
        runtime: &crate::CompiledRuntimeSurface,
        modules: &ModuleTable,
    ) -> Self {
        Self::from_runtime_surface_inner(runtime, None, modules)
    }

    pub fn from_runtime_surface_with_lowering(
        runtime: &crate::CompiledRuntimeSurface,
        lowering: &crate::CompiledLoweringSurface,
        modules: &ModuleTable,
    ) -> Self {
        Self::from_runtime_surface_inner(runtime, Some(lowering), modules)
    }

    pub fn from_compiled_unit_surfaces(
        namespace: &crate::CompiledNamespaceSurface,
        lowering: &crate::CompiledLoweringSurface,
        runtime: &crate::CompiledRuntimeSurface,
    ) -> Option<Self> {
        Self::from_compiled_unit_surfaces_inner(
            None,
            namespace,
            lowering,
            runtime,
            std::iter::empty::<(DefId, DefId)>(),
        )
    }

    pub fn extend_with_compiled_unit_surfaces_and_external_defs(
        &self,
        namespace: &crate::CompiledNamespaceSurface,
        lowering: &crate::CompiledLoweringSurface,
        runtime: &crate::CompiledRuntimeSurface,
        external_defs: impl IntoIterator<Item = (DefId, DefId)>,
    ) -> Option<Self> {
        Self::from_compiled_unit_surfaces_inner(
            Some(self),
            namespace,
            lowering,
            runtime,
            external_defs,
        )
    }

    fn from_compiled_unit_surfaces_inner(
        base: Option<&Self>,
        namespace: &crate::CompiledNamespaceSurface,
        lowering: &crate::CompiledLoweringSurface,
        runtime: &crate::CompiledRuntimeSurface,
        external_defs: impl IntoIterator<Item = (DefId, DefId)>,
    ) -> Option<Self> {
        let mut poly = base
            .map(|prefix| prefix.poly.clone())
            .unwrap_or_else(poly::expr::Arena::new);
        let mut labels = base
            .map(|prefix| prefix.labels.clone())
            .unwrap_or_else(DumpLabels::new);
        let import = if base.is_some() {
            runtime
                .import_reachable_into_with_external_defs(&mut poly, &mut labels, external_defs)
                .ok()?
        } else {
            runtime.import_into_with_external_defs(&mut poly, &mut labels, external_defs)
        };
        let imported_runtime = BodyLoweringPrefixRuntime::from_runtime_import_with_surfaces(
            &import, namespace, lowering, runtime,
        );
        let runtime = if let Some(prefix) = base {
            prefix.runtime.extended_with(imported_runtime)
        } else {
            imported_runtime
        };
        let mut boundary = base
            .map(|prefix| prefix.boundary.clone())
            .unwrap_or_else(crate::CompiledBoundaryInterface::empty);
        boundary
            .bounds
            .extend(import.boundary.bounds.iter().copied());
        let modules = ModuleTable::from_compiled_surfaces(namespace, lowering, &import)?;
        let errors = base.map(|prefix| prefix.errors.clone()).unwrap_or_default();
        Some(Self {
            poly,
            boundary,
            modules,
            labels,
            errors,
            runtime,
        })
    }

    fn from_runtime_surface_inner(
        runtime: &crate::CompiledRuntimeSurface,
        lowering: Option<&crate::CompiledLoweringSurface>,
        modules: &ModuleTable,
    ) -> Self {
        let mut poly = poly::expr::Arena::new();
        let mut labels = DumpLabels::new();
        let import = runtime.import_into(&mut poly, &mut labels);
        let runtime = BodyLoweringPrefixRuntime::from_runtime_import_with_optional_surfaces(
            &import, lowering, runtime,
        );
        let mut modules = modules.clone();
        modules.remap_runtime_defs(&import);
        if let Some(lowering) = lowering {
            lowering.apply_to_module_table(&mut modules);
        }
        Self {
            poly,
            boundary: import.boundary,
            modules,
            labels,
            errors: Vec::new(),
            runtime,
        }
    }
}

impl BodyLoweringPrefixRuntime {
    fn from_lowering(lowering: &BodyLowering) -> Self {
        Self {
            defs: lowering
                .session
                .poly
                .defs
                .iter()
                .map(|(def, _)| def)
                .collect(),
            modules: FxHashMap::default(),
            values: FxHashMap::default(),
            type_field_methods: type_field_method_defs_from_module_table(
                &lowering.modules,
                |def| def,
            ),
            casts: cast_defs_from_arena(&lowering.session.poly, |def| def),
        }
    }

    fn from_runtime_import_with_optional_surfaces(
        import: &crate::CompiledRuntimeImport,
        lowering: Option<&crate::CompiledLoweringSurface>,
        runtime: &crate::CompiledRuntimeSurface,
    ) -> Self {
        Self {
            defs: import.defs.values().copied().collect(),
            modules: import
                .modules
                .iter()
                .map(|module| {
                    (
                        module.module,
                        BodyLoweringPrefixRuntimeModuleDef {
                            module: module.module,
                            module_path: Vec::new(),
                            def: module.def,
                        },
                    )
                })
                .collect(),
            values: import
                .values
                .iter()
                .map(|value| {
                    (
                        value.symbol,
                        BodyLoweringPrefixRuntimeValueDef {
                            symbol: value.symbol,
                            value_path: Vec::new(),
                            def: value.def,
                        },
                    )
                })
                .collect(),
            type_field_methods: lowering
                .map(|lowering| type_field_method_defs_from_lowering_surface(lowering, import))
                .unwrap_or_default(),
            casts: cast_defs_from_import(import, Some(runtime)),
        }
    }

    fn from_runtime_import_with_surfaces(
        import: &crate::CompiledRuntimeImport,
        namespace: &crate::CompiledNamespaceSurface,
        lowering: &crate::CompiledLoweringSurface,
        runtime: &crate::CompiledRuntimeSurface,
    ) -> Self {
        let module_paths = namespace
            .modules
            .iter()
            .map(|module| (module.id, module.path.clone()))
            .collect::<FxHashMap<_, _>>();
        let value_paths = namespace
            .values
            .iter()
            .map(|value| (value.unit_id, value.path.clone()))
            .collect::<FxHashMap<_, _>>();
        Self {
            defs: import.defs.values().copied().collect(),
            modules: import
                .modules
                .iter()
                .map(|module| {
                    (
                        module.module,
                        BodyLoweringPrefixRuntimeModuleDef {
                            module: module.module,
                            module_path: module_paths
                                .get(&module.module)
                                .cloned()
                                .unwrap_or_default(),
                            def: module.def,
                        },
                    )
                })
                .collect(),
            values: import
                .values
                .iter()
                .map(|value| {
                    (
                        value.symbol,
                        BodyLoweringPrefixRuntimeValueDef {
                            symbol: value.symbol,
                            value_path: value_paths.get(&value.symbol).cloned().unwrap_or_default(),
                            def: value.def,
                        },
                    )
                })
                .collect(),
            type_field_methods: type_field_method_defs_from_lowering_surface(lowering, import),
            casts: cast_defs_from_import(import, Some(runtime)),
        }
    }

    fn extended_with(&self, imported: Self) -> Self {
        let mut defs = self.defs.clone();
        defs.extend(imported.defs);
        let mut modules = self.modules.clone();
        modules.extend(imported.modules);
        let mut values = self.values.clone();
        values.extend(imported.values);
        let mut type_field_methods = self.type_field_methods.clone();
        type_field_methods.extend(imported.type_field_methods);
        sort_type_field_method_defs(&mut type_field_methods);
        let mut casts = self.casts.clone();
        casts.extend(imported.casts);
        sort_cast_defs(&mut casts);
        Self {
            defs,
            modules,
            values,
            type_field_methods,
            casts,
        }
    }

    pub fn def_count(&self) -> usize {
        self.defs.len()
    }

    pub fn module_count(&self) -> usize {
        self.modules.len()
    }

    pub fn value_count(&self) -> usize {
        self.values.len()
    }

    pub fn contains_def(&self, def: DefId) -> bool {
        self.defs.contains(&def)
    }

    pub fn def_ids(&self) -> impl Iterator<Item = DefId> + '_ {
        self.defs.iter().copied()
    }

    pub fn module_def(&self, module: u32) -> Option<DefId> {
        self.modules.get(&module).map(|entry| entry.def)
    }

    pub fn value_def(&self, symbol: u32) -> Option<DefId> {
        self.values.get(&symbol).map(|entry| entry.def)
    }

    pub fn module_defs(&self) -> impl Iterator<Item = &BodyLoweringPrefixRuntimeModuleDef> {
        self.modules.values()
    }

    pub fn value_defs(&self) -> impl Iterator<Item = &BodyLoweringPrefixRuntimeValueDef> {
        self.values.values()
    }

    pub fn type_field_method_defs(
        &self,
    ) -> impl Iterator<Item = &BodyLoweringPrefixRuntimeTypeFieldMethodDef> {
        self.type_field_methods.iter()
    }

    pub fn cast_defs(&self) -> impl Iterator<Item = &BodyLoweringPrefixRuntimeCastDef> {
        self.casts.iter()
    }
}

fn type_field_method_defs_from_module_table(
    modules: &ModuleTable,
    map_def: impl Fn(DefId) -> DefId,
) -> Vec<BodyLoweringPrefixRuntimeTypeFieldMethodDef> {
    let mut methods = modules
        .all_type_field_methods()
        .filter_map(|method| {
            let owner = modules.type_decl_by_id(method.owner)?;
            Some(BodyLoweringPrefixRuntimeTypeFieldMethodDef {
                owner_type_path: crate::namespace_path(&modules.type_decl_path(&owner)),
                name: method.name.0.clone(),
                receiver_kind: method.receiver_kind,
                def: map_def(method.def),
            })
        })
        .collect::<Vec<_>>();
    sort_type_field_method_defs(&mut methods);
    methods
}

fn type_field_method_defs_from_lowering_surface(
    lowering: &crate::CompiledLoweringSurface,
    import: &crate::CompiledRuntimeImport,
) -> Vec<BodyLoweringPrefixRuntimeTypeFieldMethodDef> {
    let mut methods = lowering
        .type_field_methods
        .iter()
        .map(|method| BodyLoweringPrefixRuntimeTypeFieldMethodDef {
            owner_type_path: method.owner_type_path.clone(),
            name: method.name.clone(),
            receiver_kind: method.receiver_kind,
            def: import.map_def(method.source_def),
        })
        .collect::<Vec<_>>();
    sort_type_field_method_defs(&mut methods);
    methods
}

fn sort_type_field_method_defs(methods: &mut Vec<BodyLoweringPrefixRuntimeTypeFieldMethodDef>) {
    methods.sort_by(|left, right| {
        (
            &left.owner_type_path,
            &left.name,
            left.receiver_kind as u8,
            left.def.0,
        )
            .cmp(&(
                &right.owner_type_path,
                &right.name,
                right.receiver_kind as u8,
                right.def.0,
            ))
    });
    methods.dedup_by(|left, right| {
        left.owner_type_path == right.owner_type_path
            && left.name == right.name
            && left.receiver_kind == right.receiver_kind
            && left.def == right.def
    });
}

fn cast_defs_from_arena(
    arena: &poly::expr::Arena,
    map_def: impl Fn(DefId) -> DefId,
) -> Vec<BodyLoweringPrefixRuntimeCastDef> {
    let mut counts = FxHashMap::<(Vec<String>, Vec<String>), u32>::default();
    let mut casts = Vec::new();
    for rule in &arena.cast_rules {
        if rule.kind != poly::expr::CastRuleKind::Value {
            continue;
        }
        let key = (rule.source.clone(), rule.target.clone());
        let ordinal = counts.entry(key).or_insert(0);
        casts.push(BodyLoweringPrefixRuntimeCastDef {
            source_type_path: rule.source.clone(),
            target_type_path: rule.target.clone(),
            ordinal: *ordinal,
            def: map_def(rule.def),
        });
        *ordinal += 1;
    }
    sort_cast_defs(&mut casts);
    casts
}

fn cast_defs_from_import(
    import: &crate::CompiledRuntimeImport,
    runtime: Option<&crate::CompiledRuntimeSurface>,
) -> Vec<BodyLoweringPrefixRuntimeCastDef> {
    runtime
        .map(|runtime| cast_defs_from_arena(&runtime.arena, |def| import.map_def(def)))
        .unwrap_or_default()
}

fn sort_cast_defs(casts: &mut Vec<BodyLoweringPrefixRuntimeCastDef>) {
    casts.sort_by(|left, right| {
        (
            &left.source_type_path,
            &left.target_type_path,
            left.ordinal,
            left.def.0,
        )
            .cmp(&(
                &right.source_type_path,
                &right.target_type_path,
                right.ordinal,
                right.def.0,
            ))
    });
    casts.dedup_by(|left, right| {
        left.source_type_path == right.source_type_path
            && left.target_type_path == right.target_type_path
            && left.ordinal == right.ordinal
            && left.def == right.def
    });
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BodyLoweringTiming {
    pub index_csts: Duration,
    pub module_map: Duration,
    pub init_lowerer: Duration,
    pub lower_bodies: Duration,
    pub synthetic_act_copy: Duration,
    pub drain_analysis: Duration,
    pub resolve_selections: Duration,
    pub finish: Duration,
    pub total: Duration,
    pub analysis: AnalysisTiming,
    pub constraint: ConstraintTiming,
}

/// pass1 の結果へ binding body を書き戻す。
///
/// body lowering は全 binding を走査してから `AnalysisSession` の queue を drain する。
/// 先に drain すると、source 上で後に現れる binding への forward ref が SCC graph に入る前に
/// earlier binding が量化されることがあるため。
pub fn lower_binding_bodies(root: &Cst, lower: Lower) -> BodyLowering {
    let mut lowerer = BodyLowerer::new(lower);
    lowerer.lower_block(root, lowerer.modules.root_id());
    lowerer.lower_synthetic_act_copy_bodies();
    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    lowerer.finish()
}

/// 複数 `LoadedFile` を1つの module tree として body lowering する。
///
/// pass1 は root file から `mod` / `use mod` の module skeleton を作り、child file の
/// top-level block を対応する module に差し込む。pass2 は全 file の binding を走査してから
/// work queue を drain するため、file をまたぐ forward ref / cycle も同じ SCC machine に乗る。
pub fn lower_loaded_files(files: &[LoadedFile]) -> Result<BodyLowering, LoadedFilesError> {
    let timing = InferTiming::from_env();
    let mut measured = BodyLoweringTiming::default();
    let total_start = Instant::now();

    let phase_start = Instant::now();
    let loaded = LoadedFileCsts::new(files)?;
    measured.index_csts = phase_start.elapsed();
    timing.phase("index loaded file CSTs", measured.index_csts);

    let phase_start = Instant::now();
    let lower = lower_loaded_file_csts_module_map(&loaded)?;
    measured.module_map = phase_start.elapsed();
    timing.phase("lower module map", measured.module_map);

    let phase_start = Instant::now();
    let mut lowerer = BodyLowerer::new(lower);
    measured.init_lowerer = phase_start.elapsed();
    timing.phase("initialize body lowerer", measured.init_lowerer);

    let phase_start = Instant::now();
    for file in loaded.by_depth() {
        let Some(module) = lowerer.modules.module_by_path(&file.module_path) else {
            return Err(LoadedFilesError::MissingModulePath {
                module_path: file.module_path.clone(),
            });
        };
        let file_start = Instant::now();
        timing.file_start(&file.module_path);
        let previous_source_file =
            std::mem::replace(&mut lowerer.source_file, file.module_path.clone());
        lowerer.lower_block(&file.cst, module);
        lowerer.source_file = previous_source_file;
        timing.file_done(&file.module_path, file_start.elapsed());
    }
    measured.lower_bodies = phase_start.elapsed();
    timing.phase("lower binding bodies", measured.lower_bodies);

    let phase_start = Instant::now();
    lowerer.lower_synthetic_act_copy_bodies();
    measured.synthetic_act_copy = phase_start.elapsed();
    timing.phase(
        "lower synthetic act copy bodies",
        measured.synthetic_act_copy,
    );

    trace_requested_def_labels(&lowerer.labels);

    let phase_start = Instant::now();
    lowerer.drain_analysis_with_conformance();
    measured.drain_analysis = phase_start.elapsed();
    timing.phase("drain analysis work", measured.drain_analysis);

    let phase_start = Instant::now();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    measured.resolve_selections = phase_start.elapsed();
    measured.analysis = lowerer.session.timing();
    measured.constraint = lowerer.session.infer.constraint_timing();
    timing.phase("resolve remaining selections", measured.resolve_selections);

    let phase_start = Instant::now();
    let mut output = lowerer.finish();
    measured.finish = phase_start.elapsed();
    measured.total = total_start.elapsed();
    output.timing = measured;
    timing.phase("finish lowering", measured.finish);
    timing.phase("total lower_loaded_files", measured.total);
    Ok(output)
}

pub fn lower_loaded_files_prefix(
    files: &[LoadedFile],
) -> Result<BodyLoweringPrefix, LoadedFilesError> {
    lower_loaded_files(files).map(BodyLowering::into_prefix)
}

pub fn lower_loaded_files_with_prefix(
    prefix: &BodyLoweringPrefix,
    files: &[LoadedFile],
) -> Result<BodyLowering, LoadedFilesError> {
    let timing = InferTiming::from_env();
    let mut measured = BodyLoweringTiming::default();
    let total_start = Instant::now();

    let phase_start = Instant::now();
    let append = append_loaded_files_to_lower(
        Lower {
            arena: prefix.poly.clone(),
            modules: prefix.modules.clone(),
            source_file: Path::default(),
            source_text: None,
        },
        files,
    )?;
    measured.module_map = phase_start.elapsed();
    timing.phase(
        "append suffix files to cached lower module map",
        measured.module_map,
    );

    let phase_start = Instant::now();
    let mut lowerer = BodyLowerer::new_with_imported_boundary(append.lower, &prefix.boundary);
    lowerer.prefix_runtime = prefix.runtime.clone();
    let suffix_labels = lowerer.labels.clone();
    lowerer.labels = prefix.labels.clone();
    lowerer.labels.extend(suffix_labels);
    lowerer.errors.extend(prefix.errors.clone());
    measured.init_lowerer = phase_start.elapsed();
    timing.phase(
        "initialize cached suffix body lowerer",
        measured.init_lowerer,
    );

    let phase_start = Instant::now();
    for file in append.loaded.by_depth() {
        let Some(module) = lowerer.modules.module_by_path(&file.module_path) else {
            return Err(LoadedFilesError::MissingModulePath {
                module_path: file.module_path.clone(),
            });
        };
        let file_start = Instant::now();
        timing.file_start(&file.module_path);
        let previous_source_file =
            std::mem::replace(&mut lowerer.source_file, file.module_path.clone());
        lowerer.lower_block(&file.cst, module);
        lowerer.source_file = previous_source_file;
        timing.file_done(&file.module_path, file_start.elapsed());
    }
    measured.lower_bodies = phase_start.elapsed();
    timing.phase("lower cached suffix bodies", measured.lower_bodies);

    let phase_start = Instant::now();
    lowerer.lower_synthetic_act_copy_bodies_for(
        append.synthetic_var_act_copy_ids,
        append.synthetic_sub_label_act_copy_ids,
    );
    measured.synthetic_act_copy = phase_start.elapsed();
    timing.phase(
        "lower cached suffix synthetic act copy bodies",
        measured.synthetic_act_copy,
    );

    trace_requested_def_labels(&lowerer.labels);

    let phase_start = Instant::now();
    lowerer.drain_analysis_with_conformance();
    measured.drain_analysis = phase_start.elapsed();
    timing.phase("drain cached suffix analysis work", measured.drain_analysis);

    let phase_start = Instant::now();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    measured.resolve_selections = phase_start.elapsed();
    measured.analysis = lowerer.session.timing();
    measured.constraint = lowerer.session.infer.constraint_timing();
    timing.phase(
        "resolve cached suffix remaining selections",
        measured.resolve_selections,
    );

    let phase_start = Instant::now();
    let mut output = lowerer.finish();
    measured.finish = phase_start.elapsed();
    measured.total = total_start.elapsed();
    output.timing = measured;
    timing.phase("finish cached suffix lowering", measured.finish);
    timing.phase("total lower_loaded_files_with_prefix", measured.total);
    Ok(output)
}

pub fn lower_root_loaded_file_with_prefix(
    prefix: &BodyLoweringPrefix,
    root: &LoadedFile,
) -> Result<BodyLowering, LoadedFilesError> {
    let timing = InferTiming::from_env();
    let mut measured = BodyLoweringTiming::default();
    let total_start = Instant::now();

    let phase_start = Instant::now();
    let append = append_root_loaded_file_to_lower(
        Lower {
            arena: prefix.poly.clone(),
            modules: prefix.modules.clone(),
            source_file: Path::default(),
            source_text: None,
        },
        root,
    )?;
    measured.module_map = phase_start.elapsed();
    timing.phase(
        "append root to cached lower module map",
        measured.module_map,
    );

    let phase_start = Instant::now();
    let mut lowerer = BodyLowerer::new_with_imported_boundary(append.lower, &prefix.boundary);
    lowerer.prefix_runtime = prefix.runtime.clone();
    let root_labels = lowerer.labels.clone();
    lowerer.labels = prefix.labels.clone();
    lowerer.labels.extend(root_labels);
    lowerer.errors.extend(prefix.errors.clone());
    measured.init_lowerer = phase_start.elapsed();
    timing.phase("initialize cached body lowerer", measured.init_lowerer);

    let phase_start = Instant::now();
    lowerer.lower_block(&append.root, lowerer.modules.root_id());
    measured.lower_bodies = phase_start.elapsed();
    timing.phase("lower cached root body", measured.lower_bodies);

    let phase_start = Instant::now();
    lowerer.lower_synthetic_act_copy_bodies_for(
        append.synthetic_var_act_copy_ids,
        append.synthetic_sub_label_act_copy_ids,
    );
    measured.synthetic_act_copy = phase_start.elapsed();
    timing.phase(
        "lower cached root synthetic act copy bodies",
        measured.synthetic_act_copy,
    );

    trace_requested_def_labels(&lowerer.labels);

    let phase_start = Instant::now();
    lowerer.drain_analysis_with_conformance();
    measured.drain_analysis = phase_start.elapsed();
    timing.phase("drain cached analysis work", measured.drain_analysis);

    let phase_start = Instant::now();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    measured.resolve_selections = phase_start.elapsed();
    measured.analysis = lowerer.session.timing();
    measured.constraint = lowerer.session.infer.constraint_timing();
    timing.phase(
        "resolve cached remaining selections",
        measured.resolve_selections,
    );

    let phase_start = Instant::now();
    let mut output = lowerer.finish();
    measured.finish = phase_start.elapsed();
    measured.total = total_start.elapsed();
    output.timing = measured;
    timing.phase("finish cached root lowering", measured.finish);
    timing.phase("total lower_root_loaded_file_with_prefix", measured.total);
    Ok(output)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InferTiming {
    Off,
    Phases,
    Files,
}

impl InferTiming {
    pub(super) fn from_env() -> Self {
        match std::env::var("YULANG_INFER_TIMING") {
            Ok(value) if value == "files" => Self::Files,
            Ok(value) if !value.is_empty() && value != "0" => Self::Phases,
            _ => Self::Off,
        }
    }

    pub(super) fn phase(self, label: &str, elapsed: Duration) {
        if matches!(self, Self::Phases | Self::Files) {
            eprintln!("[infer] {label}: {}", format_timing_duration(elapsed));
        }
    }

    pub(super) fn file_start(self, module: &Path) {
        if matches!(self, Self::Files) {
            eprintln!("[infer] lower {} ...", format_module_path(module));
        }
    }

    pub(super) fn file_done(self, module: &Path, elapsed: Duration) {
        if matches!(self, Self::Files) {
            eprintln!(
                "[infer] lower {}: {}",
                format_module_path(module),
                format_timing_duration(elapsed)
            );
        }
    }
}

fn format_timing_duration(duration: Duration) -> String {
    if duration.as_secs() > 0 {
        format!("{:.3}s", duration.as_secs_f64())
    } else {
        format!("{:.3}ms", duration.as_secs_f64() * 1000.0)
    }
}

fn format_module_path(path: &Path) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn trace_requested_def_labels(labels: &DumpLabels) {
    let Ok(value) = std::env::var("YULANG_TRACE_DEFS") else {
        return;
    };
    for part in value.split(',') {
        let Ok(id) = part.trim().parse::<u32>() else {
            continue;
        };
        let def = DefId(id);
        let label = labels.def_label(def).unwrap_or("<unlabeled>");
        eprintln!("[infer] def {def:?}: {label}");
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// binding body lowering が構造化して返す失敗。
pub enum BodyLoweringError {
    MissingBindingDecl {
        name: Name,
    },
    MissingModuleDecl {
        name: Name,
    },
    MissingBody {
        def: poly::expr::DefId,
        name: Name,
    },
    NonLetDef {
        def: poly::expr::DefId,
        name: Name,
    },
    Expr {
        def: poly::expr::DefId,
        name: Name,
        error: LoweringError,
    },
    RootExpr {
        error: LoweringError,
    },
    Analysis(AnalysisDiagnostic),
}

pub(super) struct BodyLowerer {
    pub(super) session: AnalysisSession,
    pub(super) modules: ModuleTable,
    pub(super) source_file: Path,
    pub(super) typing: Typing,
    pub(super) labels: DumpLabels,
    pub(super) errors: Vec<BodyLoweringError>,
    pub(super) value_cursors: FxHashMap<(ModuleId, Name), usize>,
    pub(super) module_cursors: FxHashMap<(ModuleId, Name), usize>,
    pub(super) type_cursors: FxHashMap<(ModuleId, Name), usize>,
    pub(super) root_expr_cursors: FxHashMap<ModuleId, usize>,
    pub(super) impl_cursors: FxHashMap<ModuleId, usize>,
    pub(super) cast_cursors: FxHashMap<ModuleId, usize>,
    pub(super) role_requirements: FxHashMap<DefId, RoleMethodRequirement>,
    pub(super) deferred_result_annotation_checks: Vec<DeferredResultAnnotationCheck>,
    pub(super) role_impl_conformance_contracts:
        Vec<crate::role_impl_conformance::RoleImplConformanceContract>,
    pending_role_impl_conformance: FxHashMap<DefId, PendingRoleImplConformance>,
    receiverless_conformance_shadow_enabled: bool,
    #[cfg(test)]
    receiverless_conformance_shadow: Vec<ReceiverlessConformanceShadowWitness>,
    #[cfg(test)]
    receiver_conformance_shadow: Vec<ReceiverConformanceShadowWitness>,
    #[cfg(test)]
    conformance_batch_events: Vec<ConformanceBatchEvent>,
    #[cfg(test)]
    candidate_independent_fallback_early_resolution_enabled: bool,
    #[cfg(test)]
    inactive_receiver_provisional_config: Option<InactiveReceiverProvisionalConfig>,
    #[cfg(test)]
    inactive_receiver_provisional_bindings: FxHashMap<DefId, InactiveReceiverProvisionalBinding>,
    #[cfg(test)]
    receiver_descriptor_gate_failures: FxHashSet<DefId>,
    #[cfg(test)]
    receiver_capture_failures: FxHashSet<DefId>,
    #[cfg(test)]
    binding_def_finished_emissions: FxHashMap<DefId, usize>,
    #[cfg(test)]
    binding_publication_commits: FxHashMap<DefId, usize>,
    pub(super) local_method_scope: Option<ModuleId>,
    pub(super) prefix_runtime: BodyLoweringPrefixRuntime,
    pub(super) record_source_spans: bool,
    // Synthetic act copy bodies are implementation helpers. Their computed bindings keep
    // BindingFetch for use-site semantics, but they are not source-level runtime roots.
    pub(super) suppress_runtime_roots: bool,
}

pub(super) struct DeferredResultAnnotationCheck {
    def: poly::expr::DefId,
    name: Name,
    arity: usize,
    expected: SignatureType,
}

/// Successful binding publications retained across a future conformance pause.
///
/// The payload is same-session lowering state. It is deliberately neither cloneable nor
/// serializable; the owning pending slot must move it into `commit_provisional_binding` exactly
/// once. T1 still commits every payload immediately through `finish_binding`.
pub(super) struct ProvisionalBindingCommit {
    def: DefId,
    name: Name,
    root: TypeVar,
    computation: Computation,
    connect_body: bool,
    publish_runtime_root: bool,
}

#[cfg(test)]
#[derive(Clone, Copy)]
struct InactiveReceiverProvisionalConfig {
    evaluation: Evaluation,
    suppress_runtime_root: bool,
}

#[cfg(test)]
struct InactiveReceiverProvisionalBinding {
    descriptor: DeferredRoleImplMethodRequirement,
    binding: Option<ProvisionalBindingCommit>,
}

struct PendingRoleImplConformance {
    impl_def: DefId,
    member: DefId,
    module: ModuleId,
    site: ModuleOrder,
    name: Name,
    bridge: Result<
        crate::role_impl_conformance::RoleImplConformanceBinderBridge,
        crate::role_impl_conformance::RoleImplConformanceBinderBridgeUnavailable,
    >,
    kind: PendingRoleImplConformanceKind,
    deferred: Option<DeferredRoleImplMethodRequirement>,
    actual_view: Option<PendingRoleImplActualView>,
    phase: PendingRoleImplConformancePhase,
    edge_applications: usize,
}

enum PendingRoleImplConformanceKind {
    Receiverless,
    Receiver {
        binding: Option<ProvisionalBindingCommit>,
        committed: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PendingRoleImplActualView {
    Receiverless(crate::role_impl_conformance::ActualReceiverlessMethodConformanceView),
    Receiver(crate::role_impl_conformance::ActualReceiverMethodConformanceView),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PendingRoleImplConformancePhase {
    Captured,
    SnapshotTakenEdgesApplied,
    FailedAndEdgesApplied,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReceiverlessConformanceShadowWitness {
    pub(crate) impl_def: DefId,
    pub(crate) member: DefId,
    pub(crate) actual_view: crate::role_impl_conformance::ActualMethodConformanceView,
    pub(crate) edge_applications: usize,
    pub(crate) releases: usize,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReceiverConformanceShadowWitness {
    pub(crate) impl_def: DefId,
    pub(crate) member: DefId,
    pub(crate) actual_view: crate::role_impl_conformance::ActualReceiverMethodConformanceView,
    pub(crate) edge_applications: usize,
    pub(crate) releases: usize,
    pub(crate) binding_committed: bool,
    pub(crate) def_finished_emissions: usize,
    pub(crate) binding_publication_commits: usize,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConformanceBatchEvent {
    Captured(DefId),
    RequirementApplied(DefId),
}

fn unavailable_receiver_actual_view(
    reason: crate::role_impl_conformance::ActualMethodConformanceViewUnavailable,
) -> crate::role_impl_conformance::ActualReceiverMethodConformanceView {
    crate::role_impl_conformance::ActualReceiverMethodConformanceView {
        value: crate::role_impl_conformance::ActualMethodConformanceView::Unavailable(
            reason.clone(),
        ),
        effect: crate::role_impl_conformance::ActualMethodConformanceView::Unavailable(reason),
        #[cfg(test)]
        tail_parameter_count: None,
    }
}

fn unavailable_receiverless_actual_view(
    reason: crate::role_impl_conformance::ActualMethodConformanceViewUnavailable,
) -> crate::role_impl_conformance::ActualReceiverlessMethodConformanceView {
    crate::role_impl_conformance::ActualReceiverlessMethodConformanceView {
        value: crate::role_impl_conformance::ActualMethodConformanceView::Unavailable(
            reason.clone(),
        ),
        effect: crate::role_impl_conformance::ActualMethodConformanceView::Unavailable(reason),
        #[cfg(test)]
        parameter_count: None,
    }
}

fn unavailable_pending_actual_view(
    kind: &PendingRoleImplConformanceKind,
    reason: crate::role_impl_conformance::ActualMethodConformanceViewUnavailable,
) -> PendingRoleImplActualView {
    match kind {
        PendingRoleImplConformanceKind::Receiverless => {
            PendingRoleImplActualView::Receiverless(unavailable_receiverless_actual_view(reason))
        }
        PendingRoleImplConformanceKind::Receiver { .. } => {
            PendingRoleImplActualView::Receiver(unavailable_receiver_actual_view(reason))
        }
    }
}

fn capture_pending_actual_view(
    machine: &crate::constraints::ConstraintMachine,
    pending: &PendingRoleImplConformance,
) -> PendingRoleImplActualView {
    let Some(deferred) = pending.deferred.as_ref() else {
        return unavailable_pending_actual_view(
            &pending.kind,
            crate::role_impl_conformance::ActualMethodConformanceViewUnavailable::NonAtomicSurface,
        );
    };
    match (&pending.kind, deferred.anchor) {
        (
            PendingRoleImplConformanceKind::Receiverless,
            DeferredRequirementAnchor::Receiverless {
                body_value,
                body_effect,
                parameter_count,
                ..
            },
        ) => PendingRoleImplActualView::Receiverless(
            crate::role_impl_conformance::capture_receiverless_method_actual_view(
                machine,
                body_value,
                body_effect,
                parameter_count,
                &pending.bridge,
            ),
        ),
        (
            PendingRoleImplConformanceKind::Receiver { .. },
            DeferredRequirementAnchor::Receiver { .. },
        ) => {
            let Some(anchors) = deferred.receiver_anchors.as_ref() else {
                return unavailable_pending_actual_view(
                    &pending.kind,
                    crate::role_impl_conformance::ActualMethodConformanceViewUnavailable::NonAtomicSurface,
                );
            };
            PendingRoleImplActualView::Receiver(
                crate::role_impl_conformance::capture_receiver_actual_view(
                    machine,
                    anchors.body_value,
                    anchors.body_effect,
                    &pending.bridge,
                ),
            )
        }
        _ => unavailable_pending_actual_view(
            &pending.kind,
            crate::role_impl_conformance::ActualMethodConformanceViewUnavailable::NonAtomicSurface,
        ),
    }
}

#[cfg(test)]
fn attach_receiver_tail_parameter_count(
    view: &mut PendingRoleImplActualView,
    pending: &PendingRoleImplConformance,
) {
    let Some(count) = pending
        .deferred
        .as_ref()
        .and_then(|deferred| deferred.receiver_anchors.as_ref())
        .map(|anchors| anchors.tail_parameters.len())
    else {
        return;
    };
    if let PendingRoleImplActualView::Receiver(view) = view {
        view.tail_parameter_count = Some(count);
    }
}

fn pending_actual_view_is_available(view: &Option<PendingRoleImplActualView>) -> bool {
    match view {
        Some(PendingRoleImplActualView::Receiverless(view)) => matches!(
            view.value,
            crate::role_impl_conformance::ActualMethodConformanceView::Available(_)
        ),
        Some(PendingRoleImplActualView::Receiver(view)) => matches!(
            (&view.value, &view.effect),
            (
                crate::role_impl_conformance::ActualMethodConformanceView::Available(_),
                crate::role_impl_conformance::ActualMethodConformanceView::Available(_),
            )
        ),
        _ => false,
    }
}

fn take_pending_actual_surface(
    pending: &mut PendingRoleImplConformance,
) -> crate::role_impl_conformance::RoleImplMethodActualSurface {
    match (&pending.kind, pending.actual_view.take()) {
        (
            PendingRoleImplConformanceKind::Receiverless,
            Some(PendingRoleImplActualView::Receiverless(view)),
        ) => crate::role_impl_conformance::RoleImplMethodActualSurface::Receiverless(view),
        (PendingRoleImplConformanceKind::Receiverless, _) => {
            crate::role_impl_conformance::RoleImplMethodActualSurface::Receiverless(
                unavailable_receiverless_actual_view(
                    crate::role_impl_conformance::ActualMethodConformanceViewUnavailable::NonAtomicSurface,
                ),
            )
        }
        (
            PendingRoleImplConformanceKind::Receiver { .. },
            Some(PendingRoleImplActualView::Receiver(view)),
        ) => crate::role_impl_conformance::RoleImplMethodActualSurface::Receiver(view),
        (PendingRoleImplConformanceKind::Receiver { .. }, _) => {
            crate::role_impl_conformance::RoleImplMethodActualSurface::Receiver(
                unavailable_receiver_actual_view(
                    crate::role_impl_conformance::ActualMethodConformanceViewUnavailable::NonAtomicSurface,
                ),
            )
        }
    }
}

fn apply_pending_requirement(
    session: &mut AnalysisSession,
    modules: &ModuleTable,
    pending: &mut PendingRoleImplConformance,
) -> Result<(), LoweringError> {
    let Some(deferred) = pending.deferred.take() else {
        return Err(LoweringError::SignatureShapeMismatch {
            expected: SignatureShape::Any,
        });
    };
    let mut lowerer = ExprLowerer::new(
        session,
        modules,
        pending.module,
        pending.site,
        pending.member,
    );
    match pending.kind {
        PendingRoleImplConformanceKind::Receiverless => {
            let DeferredRequirementAnchor::Receiverless { value, .. } = deferred.anchor else {
                return Err(LoweringError::SignatureShapeMismatch {
                    expected: SignatureShape::Any,
                });
            };
            let Some(parameter_count) =
                crate::lowering::expr::method_body::clean_plain_receiverless_parameter_count(
                    &deferred,
                )
            else {
                return Err(LoweringError::SignatureShapeMismatch {
                    expected: SignatureShape::Any,
                });
            };
            if parameter_count == 0 {
                debug_assert_eq!(
                    deferred.continuation.vars,
                    deferred.final_metadata.signature_vars
                );
            }
            lowerer.connect_impl_method_requirement_from_continuation(
                value,
                &deferred.requirement,
                deferred.continuation,
                deferred.final_metadata.connect_value_upper,
            )
        }
        PendingRoleImplConformanceKind::Receiver { .. } => {
            lowerer.connect_deferred_receiver_requirement(deferred)
        }
    }
}

impl BodyLowerer {
    pub(super) fn new(lower: Lower) -> Self {
        Self::new_with_imported_boundary(lower, &crate::CompiledBoundaryInterface::empty())
    }

    fn new_with_imported_boundary(
        lower: Lower,
        boundary: &crate::CompiledBoundaryInterface,
    ) -> Self {
        let labels = lower.modules.dump_labels();
        let mut session = AnalysisSession::new_with_imported_boundary(lower.arena, boundary);
        register_declared_type_methods(&mut session, &lower.modules);
        register_declared_type_field_methods(&mut session, &lower.modules);
        register_declared_act_methods(&mut session, &lower.modules);
        register_declared_role_methods(&mut session, &lower.modules);
        register_declared_companion_local_methods(&mut session, &lower.modules);
        let mut lowerer = Self {
            session,
            modules: lower.modules,
            source_file: lower.source_file,
            typing: Typing::new(),
            labels,
            errors: Vec::new(),
            value_cursors: FxHashMap::default(),
            module_cursors: FxHashMap::default(),
            type_cursors: FxHashMap::default(),
            root_expr_cursors: FxHashMap::default(),
            impl_cursors: FxHashMap::default(),
            cast_cursors: FxHashMap::default(),
            role_requirements: FxHashMap::default(),
            deferred_result_annotation_checks: Vec::new(),
            role_impl_conformance_contracts: Vec::new(),
            pending_role_impl_conformance: FxHashMap::default(),
            receiverless_conformance_shadow_enabled: true,
            #[cfg(test)]
            receiverless_conformance_shadow: Vec::new(),
            #[cfg(test)]
            receiver_conformance_shadow: Vec::new(),
            #[cfg(test)]
            conformance_batch_events: Vec::new(),
            #[cfg(test)]
            candidate_independent_fallback_early_resolution_enabled: false,
            #[cfg(test)]
            inactive_receiver_provisional_config: None,
            #[cfg(test)]
            inactive_receiver_provisional_bindings: FxHashMap::default(),
            #[cfg(test)]
            receiver_descriptor_gate_failures: FxHashSet::default(),
            #[cfg(test)]
            receiver_capture_failures: FxHashSet::default(),
            #[cfg(test)]
            binding_def_finished_emissions: FxHashMap::default(),
            #[cfg(test)]
            binding_publication_commits: FxHashMap::default(),
            local_method_scope: None,
            prefix_runtime: BodyLoweringPrefixRuntime::default(),
            record_source_spans: true,
            suppress_runtime_roots: false,
        };
        lowerer.collect_declared_role_requirements();
        lowerer.collect_declared_role_input_variances();
        lowerer
    }

    pub(super) fn finish(mut self) -> BodyLowering {
        for (member, residual) in self.session.take_role_impl_member_residual_prerequisites() {
            let Some(contract) = self
                .role_impl_conformance_contracts
                .iter_mut()
                .find(|contract| contract.impl_def == residual.impl_def())
            else {
                continue;
            };
            let handed_off = contract.handoff_method_residual_prerequisites(member, residual);
            debug_assert!(
                handed_off,
                "a captured source method residual must belong to its unique contract"
            );
        }
        let source_impl_defs = self
            .role_impl_conformance_contracts
            .iter()
            .map(|contract| contract.impl_def)
            .collect::<Vec<_>>();
        let mut session = self.session;
        session.settle_source_role_impl_candidates(source_impl_defs);
        session.finalize_poly_role_impls();
        let analysis_timing = session.timing();
        let constraint_timing = session.infer.constraint_timing();
        let mut errors = self.errors;
        errors.extend(deferred_result_annotation_errors(
            &session,
            &self.modules,
            &self.deferred_result_annotation_checks,
        ));
        errors.extend(
            session
                .take_diagnostics()
                .into_iter()
                .map(BodyLoweringError::Analysis),
        );
        BodyLowering {
            session,
            modules: self.modules,
            typing: self.typing,
            labels: self.labels,
            errors,
            timing: BodyLoweringTiming {
                analysis: analysis_timing,
                constraint: constraint_timing,
                ..BodyLoweringTiming::default()
            },
            role_impl_conformance_contracts: self.role_impl_conformance_contracts,
            #[cfg(test)]
            receiverless_conformance_shadow: self.receiverless_conformance_shadow,
            #[cfg(test)]
            receiver_conformance_shadow: self.receiver_conformance_shadow,
            #[cfg(test)]
            conformance_batch_events: self.conformance_batch_events,
            prefix_runtime: self.prefix_runtime,
        }
    }

    #[cfg(test)]
    pub(in crate::lowering) fn set_receiverless_conformance_shadow_enabled(
        &mut self,
        enabled: bool,
    ) {
        self.receiverless_conformance_shadow_enabled = enabled;
    }

    #[cfg(test)]
    pub(in crate::lowering) fn set_candidate_independent_fallback_early_resolution_enabled(
        &mut self,
        enabled: bool,
    ) {
        self.candidate_independent_fallback_early_resolution_enabled = enabled;
    }

    #[cfg(test)]
    pub(in crate::lowering) fn lower_synthetic_act_copy_bodies_for_test(&mut self) {
        self.lower_synthetic_act_copy_bodies();
    }

    #[cfg(test)]
    pub(in crate::lowering) fn set_inactive_receiver_provisional_test_mode(
        &mut self,
        evaluation: Evaluation,
        suppress_runtime_root: bool,
    ) {
        self.inactive_receiver_provisional_config = Some(InactiveReceiverProvisionalConfig {
            evaluation,
            suppress_runtime_root,
        });
    }

    #[cfg(test)]
    pub(in crate::lowering) fn force_receiver_descriptor_gate_failure(&mut self, def: DefId) {
        self.receiver_descriptor_gate_failures.insert(def);
    }

    #[cfg(test)]
    pub(in crate::lowering) fn force_receiver_capture_failure(&mut self, def: DefId) {
        self.receiver_capture_failures.insert(def);
    }

    #[cfg(test)]
    pub(in crate::lowering) fn inactive_receiver_provisional_descriptor_is_complete(
        &self,
        def: DefId,
    ) -> bool {
        self.inactive_receiver_provisional_bindings
            .get(&def)
            .is_some_and(|pending| pending.descriptor.receiver_anchors.is_some())
    }

    #[cfg(test)]
    pub(in crate::lowering) fn resolve_inactive_receiver_provisional_for_test(
        &mut self,
        def: DefId,
        commit: bool,
    ) -> bool {
        let mut pending = self
            .inactive_receiver_provisional_bindings
            .remove(&def)
            .expect("inactive receiver provisional binding must exist");
        debug_assert!(pending.descriptor.receiver_anchors.is_some());
        if commit {
            return self.commit_provisional_binding(&mut pending.binding);
        }

        let discarded = pending
            .binding
            .take()
            .expect("a rejected provisional binding must be consumed exactly once");
        debug_assert_eq!(discarded.def, def);
        self.errors.push(BodyLoweringError::Expr {
            def,
            name: discarded.name,
            error: LoweringError::SignatureTypeMismatch {
                expected: SignatureShape::of(&pending.descriptor.requirement.signature),
            },
        });
        false
    }

    #[cfg(test)]
    pub(in crate::lowering) fn binding_def_finished_emission_count(&self, def: DefId) -> usize {
        self.binding_def_finished_emissions
            .get(&def)
            .copied()
            .unwrap_or(0)
    }

    #[cfg(test)]
    pub(in crate::lowering) fn binding_publication_commit_count(&self, def: DefId) -> usize {
        self.binding_publication_commits
            .get(&def)
            .copied()
            .unwrap_or(0)
    }

    pub(super) fn drain_analysis_with_conformance(&mut self) {
        #[cfg(test)]
        let mut early_resolution_passes = 0usize;
        loop {
            self.session.drain_work();
            #[cfg(test)]
            if self.candidate_independent_fallback_early_resolution_enabled
                && self.enqueue_candidate_independent_fallback_frontier_resolutions()
            {
                early_resolution_passes += 1;
                assert!(
                    early_resolution_passes <= 4096,
                    "candidate-independent fallback early resolution exceeded 4096 successful passes; resolved selections must not be reinserted",
                );
                // The next drain applies this batch and removes its SelectIds permanently. Run
                // the existing apply path before consulting conformance readiness again.
                continue;
            }
            let Some(component) = self.session.scc.first_component_ready_except_conformance()
            else {
                if self.pending_role_impl_conformance.is_empty() {
                    break;
                }
                let mut members = self
                    .pending_role_impl_conformance
                    .keys()
                    .copied()
                    .collect::<Vec<_>>();
                members.sort_by_key(|member| member.0);
                if members.iter().any(|member| {
                    self.pending_role_impl_conformance
                        .get(member)
                        .is_some_and(|pending| {
                            pending.phase == PendingRoleImplConformancePhase::Captured
                        })
                }) {
                    // A remaining ordinary SCC/method-dependency blocker means no sound
                    // quiescent snapshot is available in this slice. Fail the shadow capture
                    // closed, restore every legacy edge, settle once, and release on the next
                    // quiescence so final record-field resolution cannot deadlock.
                    for member in &members {
                        if let Some(pending) = self.pending_role_impl_conformance.get_mut(member) {
                            pending.actual_view = Some(unavailable_pending_actual_view(
                                &pending.kind,
                                crate::role_impl_conformance::ActualMethodConformanceViewUnavailable::OrdinarySccBlocker,
                            ));
                        }
                    }
                    self.capture_and_apply_role_impl_component(&members);
                } else {
                    self.release_role_impl_component(&members);
                }
                continue;
            };

            let has_captured = component.pending_members.iter().any(|member| {
                self.pending_role_impl_conformance
                    .get(member)
                    .is_some_and(|pending| {
                        pending.phase == PendingRoleImplConformancePhase::Captured
                    })
            });
            if has_captured {
                self.capture_and_apply_role_impl_component(&component.pending_members);
                continue;
            }

            let all_edges_applied = component.pending_members.iter().all(|member| {
                self.pending_role_impl_conformance
                    .get(member)
                    .is_none_or(|pending| {
                        matches!(
                            pending.phase,
                            PendingRoleImplConformancePhase::SnapshotTakenEdgesApplied
                                | PendingRoleImplConformancePhase::FailedAndEdgesApplied
                        )
                    })
            });
            if all_edges_applied {
                self.release_role_impl_component(&component.pending_members);
                continue;
            }

            // No production emitter other than this lowerer exists in Slice 3. Releasing an
            // unknown record is the fail-safe that keeps a malformed shadow capture from
            // deadlocking the analysis graph.
            self.release_role_impl_component(&component.pending_members);
        }
    }

    #[cfg(test)]
    fn enqueue_candidate_independent_fallback_frontier_resolutions(&mut self) -> bool {
        let frontier = self
            .session
            .scc
            .candidate_independent_fallback_frontier(|member| {
                self.pending_role_impl_conformance
                    .get(&member)
                    .is_some_and(|pending| {
                        pending.phase == PendingRoleImplConformancePhase::Captured
                    })
            });
        self.session
            .enqueue_candidate_independent_fallback_frontier_resolutions(&frontier)
    }

    fn capture_and_apply_role_impl_component(&mut self, members: &[DefId]) {
        // Capture every member first. No legacy requirement edge is applied until the complete
        // component batch has an immutable view or a structured Unavailable result.
        let mut ordered_members = members.to_vec();
        ordered_members.sort_by_key(|member| member.0);
        let captures = ordered_members
            .iter()
            .filter_map(|member| {
                let pending = self.pending_role_impl_conformance.get(member)?;
                (pending.phase == PendingRoleImplConformancePhase::Captured).then(|| {
                    let view = pending.actual_view.clone().unwrap_or_else(|| {
                        capture_pending_actual_view(self.session.infer.constraints(), pending)
                    });
                    #[cfg(test)]
                    let view = {
                        let mut view = view;
                        attach_receiver_tail_parameter_count(&mut view, pending);
                        view
                    };
                    (*member, view)
                })
            })
            .collect::<Vec<_>>();
        for (member, view) in captures {
            if let Some(pending) = self.pending_role_impl_conformance.get_mut(&member) {
                pending.actual_view = Some(view);
            }
            #[cfg(test)]
            self.conformance_batch_events
                .push(ConformanceBatchEvent::Captured(member));
        }

        let captured = ordered_members
            .iter()
            .copied()
            .filter(|member| {
                self.pending_role_impl_conformance
                    .get(member)
                    .is_some_and(|pending| {
                        pending.phase == PendingRoleImplConformancePhase::Captured
                    })
            })
            .collect::<Vec<_>>();
        for member in captured {
            let Some(mut pending) = self.pending_role_impl_conformance.remove(&member) else {
                continue;
            };
            pending.edge_applications = pending.edge_applications.saturating_add(1);
            #[cfg(test)]
            self.conformance_batch_events
                .push(ConformanceBatchEvent::RequirementApplied(member));
            let result = apply_pending_requirement(&mut self.session, &self.modules, &mut pending);

            let mut connection_succeeded = result.is_ok();
            if let Err(error) = result {
                self.errors.push(BodyLoweringError::Expr {
                    def: pending.member,
                    name: pending.name.clone(),
                    error,
                });
            }
            if let PendingRoleImplConformanceKind::Receiver { binding, committed } =
                &mut pending.kind
            {
                if connection_succeeded {
                    connection_succeeded =
                        binding.is_some() && self.commit_provisional_binding(binding);
                    *committed = connection_succeeded;
                } else {
                    let _discarded = binding.take();
                }
            }
            pending.phase =
                if connection_succeeded && pending_actual_view_is_available(&pending.actual_view) {
                    PendingRoleImplConformancePhase::SnapshotTakenEdgesApplied
                } else {
                    PendingRoleImplConformancePhase::FailedAndEdgesApplied
                };
            self.pending_role_impl_conformance.insert(member, pending);
        }
    }

    fn release_role_impl_component(&mut self, members: &[DefId]) {
        for member in members.iter().copied() {
            self.session
                .enqueue(AnalysisWork::Scc(SccInput::ConformanceReleased { member }));
            let Some(mut pending) = self.pending_role_impl_conformance.remove(&member) else {
                continue;
            };
            let actual_surface = take_pending_actual_surface(&mut pending);
            #[cfg(test)]
            let witness_surface = actual_surface.clone();
            let handed_off = self
                .role_impl_conformance_contracts
                .iter_mut()
                .find(|contract| contract.impl_def == pending.impl_def)
                .is_some_and(|contract| {
                    contract.handoff_actual_method_view(pending.member, actual_surface)
                });
            debug_assert!(
                handed_off,
                "a pending source method must hand its actual view to its unique contract once"
            );
            #[cfg(test)]
            self.record_conformance_shadow_witness(pending, witness_surface);
        }
    }

    #[cfg(test)]
    fn record_conformance_shadow_witness(
        &mut self,
        pending: PendingRoleImplConformance,
        actual_surface: crate::role_impl_conformance::RoleImplMethodActualSurface,
    ) {
        match pending.kind {
            PendingRoleImplConformanceKind::Receiverless => {
                let crate::role_impl_conformance::RoleImplMethodActualSurface::Receiverless(
                    actual_view,
                ) = actual_surface
                else {
                    unreachable!("receiverless pending record must retain a receiverless view")
                };
                self.receiverless_conformance_shadow
                    .push(ReceiverlessConformanceShadowWitness {
                        impl_def: pending.impl_def,
                        member: pending.member,
                        actual_view: actual_view.value,
                        edge_applications: pending.edge_applications,
                        releases: 1,
                    });
            }
            PendingRoleImplConformanceKind::Receiver { committed, .. } => {
                let crate::role_impl_conformance::RoleImplMethodActualSurface::Receiver(
                    actual_view,
                ) = actual_surface
                else {
                    unreachable!("receiver pending record must retain a receiver view")
                };
                self.receiver_conformance_shadow
                    .push(ReceiverConformanceShadowWitness {
                        impl_def: pending.impl_def,
                        member: pending.member,
                        actual_view,
                        edge_applications: pending.edge_applications,
                        releases: 1,
                        binding_committed: committed,
                        def_finished_emissions: self
                            .binding_def_finished_emission_count(pending.member),
                        binding_publication_commits: self
                            .binding_publication_commit_count(pending.member),
                    });
            }
        }
    }

    pub(super) fn lower_block(&mut self, block: &Cst, module: ModuleId) {
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => self.lower_binding(&child, module),
                SyntaxKind::Expr => self.lower_root_expr(&child, module),
                SyntaxKind::OpDef => self.lower_op_def_body(&child, module),
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, module),
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl => self.lower_type_decl(&child, module),
                SyntaxKind::RoleDecl => self.lower_role_decl_body(&child, module),
                SyntaxKind::ActDecl => self.lower_act_decl_body(&child, module),
                SyntaxKind::ImplDecl => self.lower_role_impl_decl(&child, module, None),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, module),
                _ => {}
            }
        }
    }

    pub(super) fn lower_root_expr(&mut self, node: &Cst, module: ModuleId) {
        let registered_owner = self.next_root_expr_owner(module);
        let parent = registered_owner.unwrap_or_else(|| self.session.poly.defs.fresh());
        if registered_owner.is_some() {
            self.session.poly.defs.set(
                parent,
                Def::Let {
                    vis: Vis::My,
                    scheme: None,
                    body: None,
                    children: Vec::new(),
                },
            );
        }
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: parent,
                root,
            }));
        let site = ModuleOrder::from_index(u32::MAX);
        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            site,
            parent,
            &mut self.labels,
        )
        .with_source_file(self.source_file.clone())
        .with_source_spans(self.record_source_spans)
        .with_local_method_scope(self.local_method_scope)
        .lower_expr(node);
        match lowered {
            Ok(computation) => {
                if registered_owner.is_some() {
                    self.constrain_def_body(root, computation.value);
                    if let Some(Def::Let { body, .. }) = self.session.poly.defs.get_mut(parent) {
                        *body = Some(computation.expr);
                    }
                    self.session
                        .poly
                        .root_expr_defs
                        .insert(computation.expr, parent);
                }
                self.session.poly.root_exprs.push(computation.expr);
                self.session
                    .poly
                    .runtime_roots
                    .push(poly::expr::RuntimeRoot::Expr(computation.expr));
            }
            Err(error) => self.errors.push(BodyLoweringError::RootExpr { error }),
        }
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: parent }));
        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn next_root_expr_owner(&mut self, module: ModuleId) -> Option<DefId> {
        let cursor = self.root_expr_cursors.entry(module).or_default();
        let index = *cursor;
        *cursor += 1;
        self.modules.root_expr_owner(module, index).flatten()
    }

    pub(super) fn lower_mod_decl(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::mod_name(node) else {
            return;
        };
        let Some(decl) = self.next_module_decl(module, &name) else {
            self.errors
                .push(BodyLoweringError::MissingModuleDecl { name });
            return;
        };
        if let Some(body) = module_body(node) {
            self.lower_block(&body, decl.module);
        }
    }

    pub(super) fn lower_binding(&mut self, node: &Cst, module: ModuleId) {
        self.lower_binding_with_self_alias(node, module, None);
    }

    pub(super) fn lower_binding_with_self_alias(
        &mut self,
        node: &Cst,
        module: ModuleId,
        self_alias: Option<AnnSelfAlias>,
    ) {
        self.lower_binding_with_context(node, module, self_alias, &[], &[]);
    }

    pub(super) fn lower_binding_with_context(
        &mut self,
        node: &Cst,
        module: ModuleId,
        self_alias: Option<AnnSelfAlias>,
        type_var_aliases: &[(String, String)],
        type_name_aliases: &[(String, TypeDeclId)],
    ) {
        let names = crate::binding_value_names(node);
        if names.is_empty() {
            return;
        }
        let arg_patterns = binding_arg_patterns(node);
        if arg_patterns.is_empty()
            && let Some(source) = top_level_var_binding_source(node)
        {
            self.lower_top_level_var_binding_error(node, module, names, source);
            return;
        }
        if !arg_patterns.is_empty() || crate::binding_has_single_head_pattern(node) {
            self.lower_single_binding_with_context(
                node,
                module,
                self_alias,
                type_var_aliases,
                type_name_aliases,
                names[0].clone(),
                arg_patterns,
            );
        } else {
            self.lower_pattern_binding_with_context(
                node,
                module,
                self_alias,
                type_var_aliases,
                type_name_aliases,
                names,
            );
        }
    }

    fn lower_top_level_var_binding_error(
        &mut self,
        node: &Cst,
        module: ModuleId,
        names: Vec<Name>,
        source: Name,
    ) {
        let source_range = source_range_for_name(node, &source);
        for name in names {
            let Some(decl) = self.next_value_decl(module, &name) else {
                self.errors
                    .push(BodyLoweringError::MissingBindingDecl { name });
                continue;
            };
            self.errors.push(BodyLoweringError::Expr {
                def: decl.def,
                name,
                error: LoweringError::UnsupportedTopLevelVarBinding {
                    name: source.clone(),
                    source_range,
                },
            });
        }
    }

    pub(super) fn lower_single_binding_with_context(
        &mut self,
        node: &Cst,
        module: ModuleId,
        self_alias: Option<AnnSelfAlias>,
        type_var_aliases: &[(String, String)],
        type_name_aliases: &[(String, TypeDeclId)],
        name: Name,
        arg_patterns: Vec<Cst>,
    ) {
        let Some(decl) = self.next_value_decl(module, &name) else {
            self.errors
                .push(BodyLoweringError::MissingBindingDecl { name });
            return;
        };
        let Some(expr) = binding_body_expr(node) else {
            self.push_missing_body_for_decl(decl.def, name);
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(decl.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: decl.def,
                root,
            }));
        let has_header_args = !arg_patterns.is_empty();
        let has_type_annotation = binding_type_expr(node).is_some();
        let result_type_expr = has_header_args.then(|| binding_type_expr(node)).flatten();

        let mut lowerer = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            decl.order,
            decl.def,
            &mut self.labels,
        )
        .with_source_file(self.source_file.clone())
        .with_source_spans(self.record_source_spans)
        .with_local_method_scope(self.local_method_scope)
        .with_parent_type_annotation(has_type_annotation)
        .with_self_alias(self_alias.clone())
        .with_type_var_aliases(type_var_aliases)
        .with_type_name_aliases(type_name_aliases);
        let lowered = if has_header_args {
            lowerer.lower_binding_body_with_args_to_named_self(
                arg_patterns.as_slice(),
                &expr,
                result_type_expr.as_ref(),
                root,
                name.clone(),
                decl.def,
            )
        } else {
            lowerer.lower_binding_body_with_args_to_self(
                arg_patterns.as_slice(),
                &expr,
                result_type_expr.as_ref(),
                root,
            )
        };
        match lowered {
            Ok(computation) => {
                let connected = if has_header_args {
                    if let Some(type_expr) = result_type_expr.as_ref() {
                        self.defer_result_annotation_check(
                            decl.def,
                            name.clone(),
                            arg_patterns.len(),
                            module,
                            decl.order,
                            self_alias.clone(),
                            type_var_aliases,
                            type_name_aliases,
                            type_expr,
                        );
                    }
                    Ok(())
                } else {
                    self.connect_binding_annotation(
                        node,
                        module,
                        decl.order,
                        self_alias,
                        type_var_aliases,
                        type_name_aliases,
                        root,
                        computation,
                    )
                };
                match connected {
                    Ok(()) => {
                        self.finish_binding(decl.def, name, root, computation, !has_header_args)
                    }
                    Err(error) => self.push_registered_expr_error(decl.def, name, error),
                }
            }
            Err(error) => self.push_registered_expr_error(decl.def, name, error),
        }
        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn lower_pattern_binding_with_context(
        &mut self,
        node: &Cst,
        module: ModuleId,
        self_alias: Option<AnnSelfAlias>,
        type_var_aliases: &[(String, String)],
        type_name_aliases: &[(String, TypeDeclId)],
        names: Vec<Name>,
    ) {
        let Some(pattern) = crate::binding_pattern(node) else {
            return;
        };
        let Some(expr) = binding_body_expr(node) else {
            for name in names {
                if let Some(decl) = self.next_value_decl(module, &name) {
                    self.push_missing_body_for_decl(decl.def, name);
                }
            }
            return;
        };

        let hidden_def = self.session.poly.defs.fresh();
        self.session.poly.defs.set(
            hidden_def,
            Def::Let {
                vis: Vis::My,
                scheme: None,
                body: None,
                children: Vec::new(),
            },
        );
        self.labels
            .set_def_label(hidden_def, "#destructure".to_string());

        let hidden_root = self.session.infer.fresh_type_var();
        self.typing.set_def(hidden_def, hidden_root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: hidden_def,
                root: hidden_root,
            }));
        let previous_level = self.session.infer.enter_child_level();
        let hidden_lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            signature_module_path_site(),
            hidden_def,
            &mut self.labels,
        )
        .with_source_file(self.source_file.clone())
        .with_source_spans(self.record_source_spans)
        .with_local_method_scope(self.local_method_scope)
        .with_self_alias(self_alias.clone())
        .with_type_var_aliases(type_var_aliases)
        .with_type_name_aliases(type_name_aliases)
        .lower_binding_body_expr(&expr);
        match hidden_lowered {
            Ok(computation) => {
                let connected = self.connect_binding_annotation(
                    node,
                    module,
                    signature_module_path_site(),
                    self_alias.clone(),
                    type_var_aliases,
                    type_name_aliases,
                    hidden_root,
                    computation,
                );
                match connected {
                    Ok(()) => self.finish_binding(
                        hidden_def,
                        Name("#destructure".into()),
                        hidden_root,
                        computation,
                        true,
                    ),
                    Err(error) => {
                        self.push_registered_expr_error(
                            hidden_def,
                            Name("#destructure".into()),
                            error,
                        );
                    }
                }
            }
            Err(error) => {
                self.push_registered_expr_error(hidden_def, Name("#destructure".into()), error);
            }
        }
        self.session.infer.restore_level(previous_level);

        for name in names {
            let Some(decl) = self.next_value_decl(module, &name) else {
                self.errors
                    .push(BodyLoweringError::MissingBindingDecl { name });
                continue;
            };
            let root = self.session.infer.fresh_type_var();
            self.typing.set_def(decl.def, root);
            self.session
                .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                    def: decl.def,
                    root,
                }));
            let lowered = ExprLowerer::with_labels(
                &mut self.session,
                &self.modules,
                module,
                decl.order,
                decl.def,
                &mut self.labels,
            )
            .with_source_file(self.source_file.clone())
            .with_source_spans(self.record_source_spans)
            .with_local_method_scope(self.local_method_scope)
            .lower_destructured_binding_component(&pattern, hidden_def, name.clone());
            match lowered {
                Ok(computation) => self.finish_binding(decl.def, name, root, computation, true),
                Err(error) => self.push_registered_expr_error(decl.def, name, error),
            }
        }
    }

    pub(super) fn lower_op_def_body(&mut self, node: &Cst, module: ModuleId) {
        let Some(info) = crate::op_def_info(node) else {
            return;
        };
        let name = info.name;
        let Some(decl) = self.next_value_decl(module, &name) else {
            self.errors
                .push(BodyLoweringError::MissingBindingDecl { name });
            return;
        };
        let Some(expr) = op_def_body_expr(node) else {
            self.push_missing_body_for_decl(decl.def, name);
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(decl.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: decl.def,
                root,
            }));
        let mut lowerer = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            decl.order,
            decl.def,
            &mut self.labels,
        )
        .with_source_file(self.source_file.clone())
        .with_source_spans(self.record_source_spans);
        let body_result = lowerer.lower_binding_body_expr(&expr);
        // nullfix の本体は thunk に包み、評価を use site の unit 適用まで遅らせる。
        let lowered = body_result.map(|body| {
            if info.nullfix {
                lowerer.thunk_computation(body)
            } else {
                body
            }
        });
        match lowered {
            Ok(computation) => self.finish_binding(decl.def, name, root, computation, true),
            Err(error) => self.push_registered_expr_error(decl.def, name, error),
        }
        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn lower_cast_decl(&mut self, node: &Cst, module: ModuleId) {
        let Some(decl) = self.next_cast_decl(module) else {
            return;
        };
        self.labels.set_def_label(decl.def, "#cast");
        if let Err(error) = self.lower_cast_decl_body(node, &decl) {
            self.errors.push(BodyLoweringError::Expr {
                def: decl.def,
                name: Name("#cast".into()),
                error,
            });
        }
    }

    pub(super) fn lower_cast_decl_body(
        &mut self,
        node: &Cst,
        decl: &CastDecl,
    ) -> Result<(), LoweringError> {
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(decl.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: decl.def,
                root,
            }));

        let result = self.lower_registered_cast_decl_body(node, decl, root);
        if result.is_err() {
            self.finish_failed_def(decl.def);
        }
        self.session.infer.restore_level(previous_level);
        result
    }

    fn lower_registered_cast_decl_body(
        &mut self,
        node: &Cst,
        decl: &CastDecl,
        root: TypeVar,
    ) -> Result<(), LoweringError> {
        let pattern = crate::cast_pattern(node).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::CastDecl,
        })?;
        let source_type_expr =
            crate::cast_source_type_expr(node).ok_or(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::CastDecl,
            })?;
        let target_type_expr =
            crate::cast_target_type_expr(node).ok_or(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::CastDecl,
            })?;
        let body = crate::cast_body_expr(node).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::CastDecl,
        })?;

        let cast_scheme = self.build_cast_scheme(
            decl.module,
            decl.order,
            &source_type_expr,
            &target_type_expr,
        )?;

        let computation = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            decl.module,
            decl.order,
            decl.def,
            &mut self.labels,
        )
        .with_source_file(self.source_file.clone())
        .with_source_spans(self.record_source_spans)
        .lower_binding_body_with_args_to_self(
            std::slice::from_ref(&pattern),
            &body,
            Some(&target_type_expr),
            root,
        )?;

        self.session.casts.insert(
            cast_scheme.source.clone(),
            cast_scheme.target.clone(),
            cast_scheme.scheme.clone(),
        );
        self.session.poly.cast_rules.push(poly::expr::CastRule {
            def: decl.def,
            source: cast_scheme.source,
            target: cast_scheme.target,
            scheme: cast_scheme.scheme,
            kind: poly::expr::CastRuleKind::Value,
        });
        self.finish_binding(decl.def, Name("#cast".into()), root, computation, false);
        Ok(())
    }

    pub(super) fn build_cast_scheme(
        &mut self,
        module: ModuleId,
        site: ModuleOrder,
        source_type_expr: &Cst,
        target_type_expr: &Cst,
    ) -> Result<CastScheme, LoweringError> {
        let mut builder = ann_type_builder(&self.modules, module, site, None);
        let source = builder
            .build_type_expr(source_type_expr)
            .map_err(|error| LoweringError::annotation_build(error, source_type_expr))?;
        let target = builder
            .build_type_expr(target_type_expr)
            .map_err(|error| LoweringError::annotation_build(error, target_type_expr))?;
        build_cast_scheme_from_ann(&mut self.session.poly, &self.modules, &source, &target)
    }
}

fn deferred_result_annotation_errors(
    session: &AnalysisSession,
    modules: &ModuleTable,
    checks: &[DeferredResultAnnotationCheck],
) -> Vec<BodyLoweringError> {
    checks
        .iter()
        .filter_map(|check| {
            let scheme = match session.poly.defs.get(check.def) {
                Some(Def::Let {
                    scheme: Some(scheme),
                    ..
                }) => scheme,
                _ => return None,
            };
            let result = scheme_result_pos(&session.poly.typ, scheme, check.arity)?;
            if poly_pos_matches_signature(&session.poly.typ, modules, result, &check.expected) {
                return None;
            }
            Some(BodyLoweringError::Expr {
                def: check.def,
                name: check.name.clone(),
                error: LoweringError::SignatureTypeMismatch {
                    expected: SignatureShape::of(&check.expected),
                },
            })
        })
        .collect()
}

fn scheme_result_pos(
    types: &poly::types::TypeArena,
    scheme: &poly::types::Scheme,
    arity: usize,
) -> Option<PosId> {
    let mut pos = scheme.predicate;
    for _ in 0..arity {
        pos = match types.pos(pos) {
            Pos::Fun { ret, .. } => *ret,
            Pos::NonSubtract(inner, _) | Pos::Stack { inner, .. } => *inner,
            Pos::Bot | Pos::Var(_) => return None,
            _ => return Some(pos),
        };
    }
    Some(pos)
}

fn poly_pos_matches_signature(
    types: &poly::types::TypeArena,
    modules: &ModuleTable,
    pos: PosId,
    expected: &SignatureType,
) -> bool {
    match types.pos(pos) {
        Pos::Bot | Pos::Var(_) => true,
        Pos::NonSubtract(inner, _) | Pos::Stack { inner, .. } => {
            poly_pos_matches_signature(types, modules, *inner, expected)
        }
        Pos::Union(left, right) => {
            poly_pos_matches_signature(types, modules, *left, expected)
                && poly_pos_matches_signature(types, modules, *right, expected)
        }
        actual => poly_pos_node_matches_signature(types, modules, actual, expected),
    }
}

fn poly_pos_node_matches_signature(
    types: &poly::types::TypeArena,
    modules: &ModuleTable,
    actual: &Pos,
    expected: &SignatureType,
) -> bool {
    match expected {
        SignatureType::Var(_) => true,
        SignatureType::Effectful { ret, .. } => {
            poly_pos_node_matches_signature(types, modules, actual, ret)
        }
        SignatureType::Function { ret, .. } => match actual {
            Pos::Fun {
                ret: actual_ret, ..
            } => poly_pos_matches_signature(types, modules, *actual_ret, ret),
            _ => false,
        },
        SignatureType::Tuple(items) => match actual {
            Pos::Tuple(actual_items) => {
                actual_items.len() == items.len()
                    && actual_items.iter().zip(items).all(|(actual, expected)| {
                        poly_pos_matches_signature(types, modules, *actual, expected)
                    })
            }
            _ => false,
        },
        SignatureType::EffectRow(_) => matches!(actual, Pos::Row(_)),
        SignatureType::Builtin(_) | SignatureType::Named(_) | SignatureType::Apply { .. } => {
            matches!(actual, Pos::Con(_, _))
        }
    }
}

fn top_level_var_binding_source(node: &Cst) -> Option<Name> {
    let pattern = crate::binding_pattern(node)?;
    let mut sources = Vec::new();
    crate::collect_pattern_var_binding_sources(&pattern, &mut sources);
    sources.into_iter().next()
}
