//! Extracted lowering implementation.

pub(super) mod act;
pub(super) mod error_decl;
pub(super) mod impl_decl;
pub(super) mod methods;
pub(super) mod register;
pub(super) mod role;
pub(super) mod signature_helpers;
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
}

#[derive(Clone)]
pub struct BodyLoweringPrefix {
    poly: poly::expr::Arena,
    modules: ModuleTable,
    labels: DumpLabels,
    errors: Vec<BodyLoweringError>,
}

impl BodyLowering {
    pub fn into_prefix(self) -> BodyLoweringPrefix {
        BodyLoweringPrefix {
            poly: self.session.poly,
            modules: self.modules,
            labels: self.labels,
            errors: self.errors,
        }
    }
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
    lowerer.session.drain_work();
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
    lowerer.session.drain_work();
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
        },
        root,
    )?;
    measured.module_map = phase_start.elapsed();
    timing.phase(
        "append root to cached lower module map",
        measured.module_map,
    );

    let phase_start = Instant::now();
    let mut lowerer = BodyLowerer::new(append.lower);
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
    lowerer.session.drain_work();
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
    pub(super) local_method_scope: Option<ModuleId>,
    pub(super) record_source_spans: bool,
    // Synthetic act copy bodies are implementation helpers. Their computed bindings keep
    // BindingFetch for use-site semantics, but they are not source-level runtime roots.
    pub(super) suppress_runtime_roots: bool,
}

impl BodyLowerer {
    pub(super) fn new(lower: Lower) -> Self {
        let labels = lower.modules.dump_labels();
        let mut session = AnalysisSession::new(lower.arena);
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
            local_method_scope: None,
            record_source_spans: true,
            suppress_runtime_roots: false,
        };
        lowerer.collect_declared_role_requirements();
        lowerer.collect_declared_role_input_variances();
        lowerer
    }

    pub(super) fn finish(self) -> BodyLowering {
        let mut session = self.session;
        session.finalize_poly_role_impls();
        let analysis_timing = session.timing();
        let constraint_timing = session.infer.constraint_timing();
        let mut errors = self.errors;
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
        .with_parent_type_annotation(has_type_annotation)
        .with_self_alias(self_alias.clone())
        .with_type_var_aliases(type_var_aliases)
        .with_type_name_aliases(type_name_aliases)
        .lower_binding_body_with_args_to_self(
            arg_patterns.as_slice(),
            &expr,
            result_type_expr.as_ref(),
            root,
        );
        match lowered {
            Ok(computation) => {
                let connected = if has_header_args {
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
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let target = builder
            .build_type_expr(target_type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        build_cast_scheme_from_ann(&mut self.session.poly, &self.modules, &source, &target)
    }
}

fn top_level_var_binding_source(node: &Cst) -> Option<Name> {
    let pattern = crate::binding_pattern(node)?;
    let mut sources = Vec::new();
    crate::collect_pattern_var_binding_sources(&pattern, &mut sources);
    sources.into_iter().next()
}
