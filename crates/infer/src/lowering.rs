//! CST binding body / expression を `poly` IR と推論用 computation slot へ落とす。
//!
//! この module は pass2 の小さな入口として、pass1 が採番した `DefId` に body を書き戻しながら、
//! 式 node から `ExprId` と `typing::Computation` を同時に作る。式そのものに型 table は
//! 残さず、lowering 中に必要な value/effect slot だけを `Computation` として返す。
//!
//! 名前参照は `RefId` を発行して `AnalysisSession` の queue に解決結果を渡す。これにより、
//! `poly` への `RefId -> DefId` 書き戻しと SCC edge 追加は、lowering 本体から分離された
//! event routing 側に残る。

mod control;
mod pattern;

use rowan::{NodeOrToken, SyntaxNode};
use sources::{LoadedFile, Name};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::sink::YulangLanguage;

use poly::dump::DumpLabels;
use poly::expr::{
    CaseArm, CatchArm, Def, DefId, Expr, Lit, Pat, PatId, PrimitiveOp, RecordSpread, RefId, Stmt,
    Vis,
};
use poly::types::{
    BuiltinType, Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, Scheme, StackWeight, SubtractId,
    Subtractability, TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::{AnalysisDiagnostic, AnalysisSession, AnalysisWork};
use crate::annotation::{
    AnnBuildError, AnnComputationTarget, AnnConstraintError, AnnConstraintLowerer, AnnSelfAlias,
    AnnType, AnnTypeBuilder, AnnTypeVarId,
};
use crate::builtin_ops::{BuiltinOp, BuiltinOpSig, SigTy, resolve_builtin_op};
use crate::compact::{
    CompactBounds, CompactFun, CompactSimplification, CompactType, compact_role_constraint,
    compact_type_var,
};
use crate::constraints::TypeLevel;
use crate::generalize::{
    generalize_prepared_compact_root_with_roles, generalize_type_var_with_boundaries,
};
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate,
    RoleInputOccurrence, RoleInputVariance,
};
use crate::scc::SccInput;
use crate::typing::{EffectViewId, Typing};
use crate::uses::{RefUse, SelectionUse};
use crate::{
    ActMethodDecl, ActOperationDecl, CastDecl, ConstructorPayload, LoadedFileCsts,
    LoadedFilesError, Lower, ModuleChildDecl, ModuleId, ModuleOrder, ModuleTable, ModuleTypeDecl,
    ModuleTypeKind, RoleImplDecl, RoleImplMethodDecl, RoleMethodDecl, SyntheticVarActUse,
    TypeDeclId, TypeFieldMethodDecl, TypeMethodDecl, TypeMethodReceiver, binding_type_expr,
    lower_loaded_file_csts_module_map,
};

type Cst = SyntaxNode<YulangLanguage>;
type CstItem = NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>;

/// binding body lowering の出力。
///
/// `session` は body を持つ `poly::Arena` と制約/SCC machine を所有する。
/// `typing` は `DefId -> TypeVar` だけを保持し、式や pattern の永続型 table は作らない。
pub struct BodyLowering {
    pub session: AnalysisSession,
    pub modules: ModuleTable,
    pub typing: Typing,
    pub labels: DumpLabels,
    pub errors: Vec<BodyLoweringError>,
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
    let loaded = LoadedFileCsts::new(files)?;
    let lower = lower_loaded_file_csts_module_map(&loaded)?;
    let mut lowerer = BodyLowerer::new(lower);

    for file in loaded.by_depth() {
        let Some(module) = lowerer.modules.module_by_path(&file.module_path) else {
            return Err(LoadedFilesError::MissingModulePath {
                module_path: file.module_path.clone(),
            });
        };
        lowerer.lower_block(&file.cst, module);
    }

    lowerer.lower_synthetic_act_copy_bodies();
    lowerer.session.drain_work();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    Ok(lowerer.finish())
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

struct BodyLowerer {
    session: AnalysisSession,
    modules: ModuleTable,
    typing: Typing,
    labels: DumpLabels,
    errors: Vec<BodyLoweringError>,
    value_cursors: FxHashMap<(ModuleId, Name), usize>,
    module_cursors: FxHashMap<(ModuleId, Name), usize>,
    type_cursors: FxHashMap<(ModuleId, Name), usize>,
    impl_cursors: FxHashMap<ModuleId, usize>,
    cast_cursors: FxHashMap<ModuleId, usize>,
    role_requirements: FxHashMap<DefId, RoleMethodRequirement>,
    local_method_scope: Option<ModuleId>,
}

impl BodyLowerer {
    fn new(lower: Lower) -> Self {
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
            typing: Typing::new(),
            labels,
            errors: Vec::new(),
            value_cursors: FxHashMap::default(),
            module_cursors: FxHashMap::default(),
            type_cursors: FxHashMap::default(),
            impl_cursors: FxHashMap::default(),
            cast_cursors: FxHashMap::default(),
            role_requirements: FxHashMap::default(),
            local_method_scope: None,
        };
        lowerer.collect_declared_role_requirements();
        lowerer.collect_declared_role_input_variances();
        lowerer
    }

    fn finish(self) -> BodyLowering {
        let mut session = self.session;
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
        }
    }

    fn lower_block(&mut self, block: &Cst, module: ModuleId) {
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
                SyntaxKind::ImplDecl => self.lower_role_impl_decl(&child, module),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, module),
                _ => {}
            }
        }
    }

    fn lower_root_expr(&mut self, node: &Cst, module: ModuleId) {
        let parent = self.session.poly.defs.fresh();
        let site = ModuleOrder::from_index(u32::MAX);
        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            site,
            parent,
            &mut self.labels,
        )
        .with_local_method_scope(self.local_method_scope)
        .lower_expr(node);
        match lowered {
            Ok(computation) => {
                self.session.poly.root_exprs.push(computation.expr);
                self.session
                    .poly
                    .runtime_roots
                    .push(poly::expr::RuntimeRoot::Expr(computation.expr));
            }
            Err(error) => self.errors.push(BodyLoweringError::RootExpr { error }),
        }
    }

    fn lower_mod_decl(&mut self, node: &Cst, module: ModuleId) {
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

    fn lower_binding(&mut self, node: &Cst, module: ModuleId) {
        self.lower_binding_with_self_alias(node, module, None);
    }

    fn lower_binding_with_self_alias(
        &mut self,
        node: &Cst,
        module: ModuleId,
        self_alias: Option<AnnSelfAlias>,
    ) {
        self.lower_binding_with_context(node, module, self_alias, &[]);
    }

    fn lower_binding_with_context(
        &mut self,
        node: &Cst,
        module: ModuleId,
        self_alias: Option<AnnSelfAlias>,
        type_var_aliases: &[(String, String)],
    ) {
        let names = crate::binding_value_names(node);
        if names.is_empty() {
            return;
        }
        let arg_patterns = binding_arg_patterns(node);
        if !arg_patterns.is_empty() || crate::binding_has_single_head_pattern(node) {
            self.lower_single_binding_with_context(
                node,
                module,
                self_alias,
                type_var_aliases,
                names[0].clone(),
                arg_patterns,
            );
        } else {
            self.lower_pattern_binding_with_context(
                node,
                module,
                self_alias,
                type_var_aliases,
                names,
            );
        }
    }

    fn lower_single_binding_with_context(
        &mut self,
        node: &Cst,
        module: ModuleId,
        self_alias: Option<AnnSelfAlias>,
        type_var_aliases: &[(String, String)],
        name: Name,
        arg_patterns: Vec<Cst>,
    ) {
        let Some(decl) = self.next_value_decl(module, &name) else {
            self.errors
                .push(BodyLoweringError::MissingBindingDecl { name });
            return;
        };
        let Some(expr) = binding_body_expr(node) else {
            self.errors.push(BodyLoweringError::MissingBody {
                def: decl.def,
                name,
            });
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
        let result_type_expr = has_header_args.then(|| binding_type_expr(node)).flatten();

        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            decl.order,
            decl.def,
            &mut self.labels,
        )
        .with_local_method_scope(self.local_method_scope)
        .with_self_alias(self_alias.clone())
        .with_type_var_aliases(type_var_aliases)
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
                        root,
                        computation,
                    )
                };
                match connected {
                    Ok(()) => {
                        self.finish_binding(decl.def, name, root, computation, !has_header_args)
                    }
                    Err(error) => self.errors.push(BodyLoweringError::Expr {
                        def: decl.def,
                        name,
                        error,
                    }),
                }
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: decl.def,
                name,
                error,
            }),
        }
        self.session.infer.restore_level(previous_level);
    }

    fn lower_pattern_binding_with_context(
        &mut self,
        node: &Cst,
        module: ModuleId,
        self_alias: Option<AnnSelfAlias>,
        type_var_aliases: &[(String, String)],
        names: Vec<Name>,
    ) {
        let Some(pattern) = crate::binding_pattern(node) else {
            return;
        };
        let Some(expr) = binding_body_expr(node) else {
            for name in names {
                if let Some(decl) = self.next_value_decl(module, &name) {
                    self.errors.push(BodyLoweringError::MissingBody {
                        def: decl.def,
                        name,
                    });
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
        .with_local_method_scope(self.local_method_scope)
        .with_self_alias(self_alias.clone())
        .with_type_var_aliases(type_var_aliases)
        .lower_binding_body_expr(&expr);
        match hidden_lowered {
            Ok(computation) => {
                let connected = self.connect_binding_annotation(
                    node,
                    module,
                    signature_module_path_site(),
                    self_alias.clone(),
                    type_var_aliases,
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
                    Err(error) => self.errors.push(BodyLoweringError::Expr {
                        def: hidden_def,
                        name: Name("#destructure".into()),
                        error,
                    }),
                }
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: hidden_def,
                name: Name("#destructure".into()),
                error,
            }),
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
            .with_local_method_scope(self.local_method_scope)
            .lower_destructured_binding_component(&pattern, hidden_def, name.clone());
            match lowered {
                Ok(computation) => self.finish_binding(decl.def, name, root, computation, true),
                Err(error) => self.errors.push(BodyLoweringError::Expr {
                    def: decl.def,
                    name,
                    error,
                }),
            }
        }
    }

    fn lower_op_def_body(&mut self, node: &Cst, module: ModuleId) {
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
            self.errors.push(BodyLoweringError::MissingBody {
                def: decl.def,
                name,
            });
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
        );
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
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: decl.def,
                name,
                error,
            }),
        }
        self.session.infer.restore_level(previous_level);
    }

    fn lower_cast_decl(&mut self, node: &Cst, module: ModuleId) {
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

    fn lower_cast_decl_body(&mut self, node: &Cst, decl: &CastDecl) -> Result<(), LoweringError> {
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

        let previous_level = self.session.infer.enter_child_level();
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
            decl.module,
            decl.order,
            decl.def,
            &mut self.labels,
        )
        .lower_binding_body_with_args_to_self(
            std::slice::from_ref(&pattern),
            &body,
            Some(&target_type_expr),
            root,
        );
        let result = match lowered {
            Ok(computation) => {
                self.session.casts.insert(
                    cast_scheme.source,
                    cast_scheme.target,
                    cast_scheme.scheme,
                );
                self.finish_binding(decl.def, Name("#cast".into()), root, computation, false);
                Ok(())
            }
            Err(error) => Err(error),
        };
        self.session.infer.restore_level(previous_level);
        result
    }

    fn build_cast_scheme(
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

    fn lower_type_decl(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::type_decl_name(node) else {
            return;
        };
        let Some(decl) = self.next_type_decl(module, &name) else {
            return;
        };
        self.lower_type_constructors(node, module, &decl);
        self.lower_type_decl_with_body(node, &decl);
    }

    fn lower_type_decl_with_body(&mut self, node: &Cst, decl: &ModuleTypeDecl) {
        let Some(body) = crate::type_with_body(node) else {
            return;
        };
        let Some(companion) = self.modules.type_companion(decl.id) else {
            return;
        };
        let self_alias = AnnSelfAlias {
            owner: decl.id,
            type_vars: crate::type_var_names(node),
        };
        let type_vars = self_alias.type_vars.clone();
        let mut method_cursor = 0usize;
        let previous_scope = self.local_method_scope.replace(companion);
        for child in body.children() {
            match child.kind() {
                SyntaxKind::Binding if crate::type_method_binding(&child).is_some() => {
                    let method = self
                        .modules
                        .type_methods(decl.id)
                        .get(method_cursor)
                        .cloned();
                    method_cursor += usize::from(method.is_some());
                    if let Some(method) = method {
                        self.lower_type_method_binding(
                            &child, companion, &decl, &method, &type_vars,
                        );
                    }
                }
                SyntaxKind::Binding => {
                    self.lower_binding_with_self_alias(&child, companion, Some(self_alias.clone()));
                }
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, companion),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, companion),
                _ => {}
            }
        }
        self.local_method_scope = previous_scope;
    }

    fn lower_type_constructors(&mut self, node: &Cst, module: ModuleId, decl: &ModuleTypeDecl) {
        match decl.kind {
            ModuleTypeKind::TypeAlias => {
                if let Some(self_struct) = crate::type_self_struct_node(node) {
                    let payload = ConstructorPayload::from_struct(&self_struct);
                    self.lower_constructor_def(node, module, decl, decl.name.clone(), payload);
                    self.lower_type_field_methods(node, &self_struct, module, decl);
                }
            }
            ModuleTypeKind::Struct => {
                let payload = ConstructorPayload::from_struct(node);
                self.lower_constructor_def(node, module, decl, decl.name.clone(), payload);
                self.lower_type_field_methods(node, node, module, decl);
            }
            ModuleTypeKind::Enum | ModuleTypeKind::Error => {
                // constructor の decl は型 companion module に登録されている。
                let Some(companion) = self.modules.type_companion(decl.id) else {
                    return;
                };
                for variant in crate::enum_variant_nodes(node) {
                    let Some(name) = crate::enum_variant_name(&variant) else {
                        continue;
                    };
                    let payload = ConstructorPayload::from_enum_variant(&variant);
                    self.lower_constructor_def(node, companion, decl, name, payload);
                }
            }
            ModuleTypeKind::Role | ModuleTypeKind::Act => {}
        }
    }

    fn lower_type_field_methods(
        &mut self,
        owner_node: &Cst,
        fields_node: &Cst,
        module: ModuleId,
        owner: &ModuleTypeDecl,
    ) {
        let methods = self.modules.type_field_methods(owner.id).to_vec();
        let mut cursor = 0usize;
        let type_vars = crate::type_var_names(owner_node);

        for field in crate::struct_field_nodes(fields_node) {
            if crate::struct_field_name(&field).is_none() {
                continue;
            }
            let Some(type_expr) = crate::field_type_expr(&field) else {
                for method in methods[cursor..methods.len().min(cursor + 2)].iter() {
                    self.errors.push(BodyLoweringError::Expr {
                        def: method.def,
                        name: method.name.clone(),
                        error: LoweringError::UnsupportedSyntax { kind: field.kind() },
                    });
                }
                cursor += 2;
                continue;
            };
            let signature = match NegSignatureBuilder::with_self_alias(
                &self.modules,
                module,
                owner.order,
                SignatureSelfAlias {
                    owner: owner.id,
                    type_vars: type_vars.clone(),
                },
            )
            .build_type_expr(&type_expr)
            {
                Ok(signature) => signature,
                Err(error) => {
                    for method in methods[cursor..methods.len().min(cursor + 2)].iter() {
                        self.errors.push(BodyLoweringError::Expr {
                            def: method.def,
                            name: method.name.clone(),
                            error: LoweringError::NegSignatureBuild {
                                error: error.clone(),
                            },
                        });
                    }
                    cursor += 2;
                    continue;
                }
            };
            for _ in 0..2 {
                let Some(method) = methods.get(cursor).cloned() else {
                    return;
                };
                cursor += 1;
                self.lower_type_field_method_def(owner_node, owner, &method, &signature);
            }
        }
    }

    fn lower_type_field_method_def(
        &mut self,
        owner_node: &Cst,
        owner: &ModuleTypeDecl,
        method: &TypeFieldMethodDecl,
        field_signature: &NegSignature,
    ) {
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let lowered = self.lower_type_field_method_type(owner_node, owner, method, field_signature);
        match lowered {
            Ok(predicate) => {
                let root_upper = self.session.infer.alloc_neg(Neg::Var(root));
                self.session.infer.subtype(predicate, root_upper);
                self.session
                    .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: method.def }));
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: method.def,
                name: method.name.clone(),
                error,
            }),
        }

        self.session.infer.restore_level(previous_level);
    }

    fn lower_type_field_method_type(
        &mut self,
        owner_node: &Cst,
        owner: &ModuleTypeDecl,
        method: &TypeFieldMethodDecl,
        field_signature: &NegSignature,
    ) -> Result<PosId, LoweringError> {
        let type_vars = crate::type_var_names(owner_node);
        let owner_arg_vars = type_vars
            .iter()
            .map(|_| self.session.infer.fresh_type_var())
            .collect::<Vec<_>>();
        let signature_vars = type_vars
            .iter()
            .cloned()
            .zip(owner_arg_vars.iter().copied())
            .collect::<FxHashMap<_, _>>();
        let owner_signature = owner_signature_type(owner.id, &type_vars);

        match method.receiver_kind {
            TypeMethodReceiver::Value => {
                let mut lowerer = SignatureLowerer::with_vars(
                    &mut self.session.infer,
                    &self.modules,
                    signature_vars,
                );
                let arg = lowerer
                    .lower_neg(&owner_signature)
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                let ret = lowerer
                    .lower_data_pos(field_signature.as_type())
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                let arg_eff = lowerer.alloc_neg(Neg::Bot);
                let ret_eff = lowerer.alloc_pos(Pos::Bot);
                Ok(lowerer.alloc_pos(Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
            TypeMethodReceiver::Ref => {
                let ref_effect = self.session.infer.fresh_type_var();
                let ref_effect_arg = self.invariant_var_arg(ref_effect);
                let mut lowerer = SignatureLowerer::with_vars(
                    &mut self.session.infer,
                    &self.modules,
                    signature_vars,
                );
                let owner_arg = lowerer
                    .lower_invariant_arg(&owner_signature)
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                let field_arg = lowerer
                    .lower_invariant_arg(field_signature.as_type())
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                let ref_path = crate::std_paths::control_var_ref_type();
                let arg =
                    lowerer.alloc_neg(Neg::Con(ref_path.clone(), vec![ref_effect_arg, owner_arg]));
                let ret = lowerer.alloc_pos(Pos::Con(ref_path, vec![ref_effect_arg, field_arg]));
                let arg_eff = lowerer.alloc_neg(Neg::Bot);
                let ret_eff = lowerer.alloc_pos(Pos::Bot);
                Ok(lowerer.alloc_pos(Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    fn lower_constructor_def(
        &mut self,
        owner_node: &Cst,
        module: ModuleId,
        owner: &ModuleTypeDecl,
        name: Name,
        payload: ConstructorPayload,
    ) {
        let Some(constructor) = self.next_value_decl(module, &name) else {
            self.errors
                .push(BodyLoweringError::MissingBindingDecl { name });
            return;
        };

        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(constructor.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: constructor.def,
                root,
            }));

        let lowered = self.lower_constructor_type(owner_node, module, owner, payload);
        match lowered {
            Ok(predicate) => {
                let root_upper = self.session.infer.alloc_neg(Neg::Var(root));
                self.session.infer.subtype(predicate, root_upper);
                self.session
                    .enqueue(AnalysisWork::Scc(SccInput::DefFinished {
                        def: constructor.def,
                    }));
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: constructor.def,
                name,
                error,
            }),
        }

        self.session.infer.restore_level(previous_level);
    }

    fn lower_constructor_type(
        &mut self,
        owner_node: &Cst,
        module: ModuleId,
        owner: &ModuleTypeDecl,
        payload: ConstructorPayload,
    ) -> Result<PosId, LoweringError> {
        let type_vars = crate::type_var_names(owner_node);
        let owner_arg_vars = type_vars
            .iter()
            .map(|_| self.session.infer.fresh_type_var())
            .collect::<Vec<_>>();
        let signature_builder = NegSignatureBuilder::with_self_alias(
            &self.modules,
            module,
            owner.order,
            SignatureSelfAlias {
                owner: owner.id,
                type_vars: type_vars.clone(),
            },
        );
        let signature_vars = type_vars
            .iter()
            .cloned()
            .zip(owner_arg_vars.iter().copied())
            .collect::<FxHashMap<_, _>>();
        let payload = build_constructor_payload_signatures(payload, &signature_builder)?;

        let owner_args = owner_arg_vars
            .into_iter()
            .map(|var| self.invariant_var_arg(var))
            .collect::<Vec<_>>();
        let args = prepare_constructor_args(&mut self.session.infer, payload);
        connect_constructor_arg_signatures(
            &mut self.session.infer,
            &self.modules,
            signature_vars,
            &args,
        )?;

        constrain_constructor_arg_shapes(&mut self.session.infer, &args);
        let path = self
            .modules
            .type_decl_path(owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let ret = self.session.infer.alloc_pos(Pos::Con(path, owner_args));
        Ok(self.constructor_function_type(args, ret))
    }

    fn constructor_function_type(&mut self, args: Vec<ConstructorArg>, ret: PosId) -> PosId {
        args.into_iter().rev().fold(ret, |ret, arg| {
            let arg = self.session.infer.alloc_neg(Neg::Var(arg.value()));
            let arg_eff = self.session.infer.alloc_neg(Neg::Bot);
            let ret_eff = self.session.infer.alloc_pos(Pos::Bot);
            self.session.infer.alloc_pos(Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            })
        })
    }

    fn invariant_var_arg(&mut self, var: TypeVar) -> NeuId {
        let lower = self.session.infer.alloc_pos(Pos::Var(var));
        let upper = self.session.infer.alloc_neg(Neg::Var(var));
        self.session.infer.alloc_neu(Neu::Bounds(lower, upper))
    }

    fn lower_act_decl_body(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::type_decl_name(node) else {
            return;
        };
        let Some(decl) = self.next_type_decl(module, &name) else {
            return;
        };
        let Some(companion) = self.modules.type_companion(decl.id) else {
            return;
        };
        let mut method_cursor = 0usize;
        let previous_scope = self.local_method_scope.replace(companion);
        if let Some(copy) = self.act_copy_lowering_context(module, &decl) {
            self.lower_act_body_contents(
                &copy.body,
                companion,
                &decl,
                &mut method_cursor,
                copy.type_var_aliases.as_slice(),
            );
        }
        if let Some(body) = crate::act_decl_body(node) {
            self.lower_act_body_contents(&body, companion, &decl, &mut method_cursor, &[]);
        }
        self.local_method_scope = previous_scope;
    }

    fn lower_act_operation_binding(
        &mut self,
        node: &Cst,
        companion: ModuleId,
        decl: &ModuleTypeDecl,
        type_var_aliases: &[(String, String)],
    ) {
        let Some(name) = crate::binding_name(node) else {
            return;
        };
        let Some(def) = self
            .modules
            .value_at(companion, &name, signature_module_path_site())
        else {
            self.errors
                .push(BodyLoweringError::MissingBindingDecl { name });
            return;
        };
        let Some(signature) = binding_type_expr(node) else {
            self.errors.push(BodyLoweringError::Expr {
                def,
                name,
                error: LoweringError::SignatureShapeMismatch {
                    expected: SignatureShape::Function,
                },
            });
            return;
        };
        let Some(operation_decl) = self.modules.act_operation_decl_by_def(def) else {
            self.errors.push(BodyLoweringError::NonLetDef { def, name });
            return;
        };

        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef { def, root }));

        let lowered = self.lower_act_operation_type(&operation_decl, &signature, type_var_aliases);
        match lowered {
            Ok(predicate) => {
                let root_upper = self.session.infer.alloc_neg(Neg::Var(root));
                self.session.infer.subtype(predicate, root_upper);
                self.session
                    .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
            }
            Err(error) => self
                .errors
                .push(BodyLoweringError::Expr { def, name, error }),
        }

        self.session.infer.restore_level(previous_level);

        debug_assert_eq!(decl.id, operation_decl.effect.id);
    }

    fn lower_act_operation_type(
        &mut self,
        operation_decl: &ActOperationDecl,
        signature: &Cst,
        type_var_aliases: &[(String, String)],
    ) -> Result<PosId, LoweringError> {
        let signature =
            self.act_operation_signature_type(operation_decl, signature, type_var_aliases)?;
        let mut lowerer = SignatureLowerer::new(&mut self.session.infer, &self.modules);
        lowerer
            .lower_pos(&signature)
            .map_err(|error| LoweringError::SignatureConstraint { error })
    }

    fn act_operation_signature_type(
        &self,
        operation_decl: &ActOperationDecl,
        signature: &Cst,
        type_var_aliases: &[(String, String)],
    ) -> Result<SignatureType, LoweringError> {
        let effect_type_vars = self
            .modules
            .act_template(operation_decl.effect.id)
            .map(crate::act_type_var_names)
            .unwrap_or_default();
        let mut builder = ann_type_builder(
            &self.modules,
            operation_decl.effect.module,
            operation_decl.effect.order,
            None,
        );
        for name in &effect_type_vars {
            builder.add_bare_type_var(name.clone());
        }
        add_type_var_aliases(&mut builder, type_var_aliases);

        let signature = build_signature_type_expr(&mut builder, signature)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let effect_ann = builder.type_decl_application(operation_decl.effect.id, &effect_type_vars);
        let effect = signature_from_ann_type(&effect_ann);
        operation_signature_with_effect(signature, effect).ok_or(
            LoweringError::SignatureShapeMismatch {
                expected: SignatureShape::Function,
            },
        )
    }

    fn lower_synthetic_act_copy_bodies(&mut self) {
        let ids = self.modules.synthetic_var_act_copy_ids();
        for id in ids {
            let Some(decl) = self.modules.type_decl_by_id(id) else {
                continue;
            };
            let Some(companion) = self.modules.type_companion(id) else {
                continue;
            };
            let Some(copy) = self.act_copy_lowering_context(decl.module, &decl) else {
                continue;
            };
            let previous_scope = self.local_method_scope.replace(companion);
            let mut method_cursor = 0usize;
            self.lower_act_body_contents(
                &copy.body,
                companion,
                &decl,
                &mut method_cursor,
                copy.type_var_aliases.as_slice(),
            );
            self.local_method_scope = previous_scope;
        }
    }

    fn lower_act_body_contents(
        &mut self,
        body: &Cst,
        companion: ModuleId,
        decl: &ModuleTypeDecl,
        method_cursor: &mut usize,
        type_var_aliases: &[(String, String)],
    ) {
        for child in body.children() {
            match child.kind() {
                SyntaxKind::Binding if crate::act_operation_binding(&child) => {
                    self.lower_act_operation_binding(&child, companion, decl, type_var_aliases);
                }
                SyntaxKind::Binding if crate::type_method_binding(&child).is_some() => {
                    let method = self
                        .modules
                        .act_methods(decl.id)
                        .get(*method_cursor)
                        .cloned();
                    *method_cursor += usize::from(method.is_some());
                    if let Some(method) = method {
                        self.lower_act_method_binding_with_aliases(
                            &child,
                            companion,
                            &method,
                            type_var_aliases,
                        );
                    }
                }
                SyntaxKind::Binding => {
                    self.lower_binding_with_context(&child, companion, None, type_var_aliases)
                }
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, companion),
                SyntaxKind::ActDecl => self.lower_act_decl_body(&child, companion),
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl => self.lower_type_decl(&child, companion),
                SyntaxKind::RoleDecl => self.lower_role_decl_body(&child, companion),
                SyntaxKind::ImplDecl => self.lower_role_impl_decl(&child, companion),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, companion),
                _ => {}
            }
        }
    }

    fn act_copy_lowering_context(
        &self,
        _module: ModuleId,
        decl: &ModuleTypeDecl,
    ) -> Option<ActCopyLoweringContext> {
        let copy = self.modules.resolved_act_copy(decl.id)?;
        let source_node = self.modules.act_template(copy.source)?;
        let body = crate::act_decl_body(source_node)?;
        Some(ActCopyLoweringContext {
            body,
            type_var_aliases: copy.type_var_aliases.clone(),
        })
    }

    fn lower_role_decl_body(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::type_decl_name(node) else {
            return;
        };
        let Some(decl) = self.next_type_decl(module, &name) else {
            return;
        };
        let Some(body) = crate::role_decl_body(node) else {
            return;
        };
        let Some(companion) = self.modules.type_companion(decl.id) else {
            return;
        };
        let role_inputs = self.modules.role_inputs(decl.id).to_vec();
        let role_associated = self.modules.role_associated(decl.id).to_vec();
        let mut method_cursor = 0usize;
        let previous_scope = self.local_method_scope.replace(companion);
        for child in body.children() {
            match child.kind() {
                SyntaxKind::Binding if crate::role_method_binding(&child).is_some() => {
                    let method = self
                        .modules
                        .role_methods(decl.id)
                        .get(method_cursor)
                        .cloned();
                    method_cursor += usize::from(method.is_some());
                    if let Some(method) = method {
                        if binding_body_expr(&child).is_some() {
                            self.lower_role_method_binding(
                                &child,
                                companion,
                                &decl,
                                &method,
                                &role_inputs,
                                &role_associated,
                            );
                        } else {
                            self.lower_role_method_signature(
                                &child,
                                companion,
                                &decl,
                                &method,
                                &role_inputs,
                                &role_associated,
                            );
                        }
                    }
                }
                SyntaxKind::Binding => {
                    self.lower_binding(&child, companion);
                }
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, companion),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, companion),
                _ => {}
            }
        }
        self.local_method_scope = previous_scope;
    }

    fn collect_declared_role_requirements(&mut self) {
        let methods = self.modules.all_role_methods().cloned().collect::<Vec<_>>();
        for method in methods {
            match self.build_role_method_requirement(&method) {
                Ok(Some(requirement)) => {
                    self.role_requirements.insert(method.def, requirement);
                }
                Ok(None) => {}
                Err(error) => self.errors.push(BodyLoweringError::Expr {
                    def: method.def,
                    name: method.name,
                    error,
                }),
            }
        }
    }

    fn collect_declared_role_input_variances(&mut self) {
        let mut role_owners = self
            .modules
            .all_role_methods()
            .map(|method| method.owner)
            .collect::<Vec<_>>();
        role_owners.sort_by_key(|owner| owner.0);
        role_owners.dedup();

        for owner in role_owners {
            let role_inputs = self.modules.role_inputs(owner);
            if role_inputs.is_empty() {
                continue;
            }
            let variances = role_input_variances_from_requirements(
                role_inputs,
                self.modules.role_methods(owner),
                &self.role_requirements,
            );
            let Some(role) = self.modules.type_decl_by_id(owner) else {
                continue;
            };
            let path = self
                .modules
                .type_decl_path(&role)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect::<Vec<_>>();
            self.session.register_role_input_variances(path, variances);
        }
    }

    fn build_role_method_requirement(
        &self,
        method: &RoleMethodDecl,
    ) -> Result<Option<RoleMethodRequirement>, LoweringError> {
        let Some(type_expr) = method.signature.clone() else {
            return Ok(None);
        };
        let Some(companion) = self.modules.type_companion(method.owner) else {
            return Ok(None);
        };
        let role_inputs = self.modules.role_inputs(method.owner);
        let role_associated = self.modules.role_associated(method.owner);
        let mut builder = ann_type_builder(&self.modules, companion, method.order, None);
        for name in role_inputs.iter().chain(role_associated.iter()) {
            builder.add_bare_type_var(name.clone());
        }
        if let Some(first) = role_inputs.first() {
            builder.add_bare_type_var_alias("self", first.clone());
        }
        let signature = build_signature_type_expr(&mut builder, &type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let signature = role_method_signature_with_receiver(
            method.receiver.as_ref(),
            role_inputs.first(),
            signature,
        );
        Ok(Some(RoleMethodRequirement { signature }))
    }

    fn lower_role_impl_decl(&mut self, node: &Cst, module: ModuleId) {
        let Some(impl_decl) = self.next_role_impl_decl(module) else {
            return;
        };
        let mut context =
            match self.register_role_impl_candidate(node, impl_decl.def, module, impl_decl.order) {
                Ok(context) => context,
                Err(error) => {
                    self.errors.push(BodyLoweringError::Expr {
                        def: impl_decl.def,
                        name: Name("impl".into()),
                        error,
                    });
                    return;
                }
            };

        let Some(body) = crate::role_impl_body(node) else {
            return;
        };
        let previous_scope = self.local_method_scope.replace(impl_decl.body_module);
        let mut method_cursor = 0usize;
        for child in body.children() {
            match child.kind() {
                SyntaxKind::Binding if crate::role_method_binding(&child).is_some() => {
                    let method_info =
                        crate::role_method_binding(&child).expect("checked role method binding");
                    let decl = self.next_value_decl(impl_decl.body_module, &method_info.name);
                    if let Some(decl) = decl {
                        let impl_method = impl_decl.methods.get(method_cursor).cloned();
                        method_cursor += usize::from(
                            impl_method
                                .as_ref()
                                .is_some_and(|method| method.def == decl.def),
                        );
                        let requirement =
                            self.role_impl_method_requirement(&context, method_info.name.clone());
                        self.lower_role_impl_method_binding(
                            &child,
                            impl_decl.def,
                            impl_decl.body_module,
                            &RoleImplMethodDecl {
                                name: method_info.name,
                                receiver: method_info.receiver,
                                def: decl.def,
                                vis: impl_method
                                    .as_ref()
                                    .map(|method| method.vis)
                                    .unwrap_or(poly::expr::Vis::My),
                                order: decl.order,
                            },
                            &context.target_ann,
                            &context.type_var_bindings,
                            &mut context.ann_solver_vars,
                            requirement,
                        );
                    }
                }
                SyntaxKind::Binding => self.lower_binding(&child, impl_decl.body_module),
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, impl_decl.body_module),
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl => self.lower_type_decl(&child, impl_decl.body_module),
                SyntaxKind::RoleDecl => self.lower_role_decl_body(&child, impl_decl.body_module),
                SyntaxKind::ActDecl => self.lower_act_decl_body(&child, impl_decl.body_module),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, impl_decl.body_module),
                _ => {}
            }
        }
        self.local_method_scope = previous_scope;
    }

    fn register_role_impl_candidate(
        &mut self,
        node: &Cst,
        impl_def: DefId,
        module: ModuleId,
        site: ModuleOrder,
    ) -> Result<RoleImplLoweringContext, LoweringError> {
        let Some(head) = impl_head_type_expr(node) else {
            return Err(LoweringError::UnsupportedSyntax { kind: node.kind() });
        };
        let mut ann_builder = ann_type_builder(&self.modules, module, site, None);
        let head_ann = ann_builder
            .build_type_expr(&head)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let description_ann = impl_description_type_expr(node)
            .map(|type_expr| ann_builder.build_type_expr(&type_expr))
            .transpose()
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let spec = role_impl_ann_spec(&self.modules, head_ann, description_ann)
            .ok_or(LoweringError::UnsupportedSyntax { kind: node.kind() })?;
        let role_input_names = self.modules.role_inputs(spec.role).to_vec();
        let role_associated_names = self.modules.role_associated(spec.role).to_vec();
        let explicit_associated = role_impl_associated_type_exprs(node);
        let candidate_associated_anns = role_associated_names
            .iter()
            .map(|name| {
                let ann = explicit_associated
                    .get(name)
                    .map(|type_expr| ann_builder.build_type_expr(type_expr))
                    .transpose()
                    .map_err(|error| LoweringError::AnnotationBuild { error })?
                    .unwrap_or_else(|| AnnType::Var(ann_builder.ann_type_var_for_role(name)));
                Ok((name.clone(), ann))
            })
            .collect::<Result<Vec<_>, LoweringError>>()?;
        let requirement_associated_anns = role_associated_names
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    AnnType::Var(ann_builder.ann_type_var_for_role(name)),
                )
            })
            .collect::<Vec<_>>();
        let type_var_bindings = ann_builder.type_var_bindings();
        let explicit_associated_complete = role_associated_names
            .iter()
            .all(|name| explicit_associated.contains_key(name));
        let (candidate_inputs, candidate_associated, ann_solver_vars) =
            if explicit_associated_complete {
                let (candidate_inputs, candidate_associated, _) =
                    self.lower_role_impl_args(&spec.inputs, &candidate_associated_anns)?;
                let (_, _, ann_solver_vars) =
                    self.lower_role_impl_args(&spec.inputs, &requirement_associated_anns)?;
                (candidate_inputs, candidate_associated, ann_solver_vars)
            } else {
                self.lower_role_impl_args(&spec.inputs, &candidate_associated_anns)?
            };
        let role = self
            .modules
            .type_decl_by_id(spec.role)
            .map(|role| {
                self.modules
                    .type_decl_path(&role)
                    .segments
                    .into_iter()
                    .map(|name| name.0)
                    .collect::<Vec<_>>()
            })
            .ok_or(LoweringError::UnsupportedSyntax { kind: node.kind() })?;
        self.session.role_impls.insert(RoleImplCandidate {
            impl_def: Some(impl_def),
            role,
            inputs: candidate_inputs,
            associated: candidate_associated,
            prerequisites: Vec::new(),
        });
        Ok(RoleImplLoweringContext {
            role: spec.role,
            target_ann: spec.target,
            input_names: role_input_names,
            input_signatures: spec.inputs.iter().map(signature_from_ann_type).collect(),
            associated_signatures: requirement_associated_anns
                .iter()
                .map(|(name, ann)| (name.clone(), signature_from_ann_type(ann)))
                .collect(),
            type_var_bindings,
            ann_solver_vars,
        })
    }

    fn lower_role_impl_args(
        &mut self,
        inputs: &[AnnType],
        associated_anns: &[(String, AnnType)],
    ) -> Result<
        (
            Vec<RoleConstraintArg>,
            Vec<RoleAssociatedConstraint>,
            FxHashMap<AnnTypeVarId, TypeVar>,
        ),
        LoweringError,
    > {
        let mut lowerer = AnnConstraintLowerer::new(&mut self.session.infer, &self.modules);
        let mut lowered_inputs = Vec::with_capacity(inputs.len());
        for input in inputs {
            lowered_inputs.push(
                lowerer
                    .lower_role_arg(input)
                    .map_err(|error| LoweringError::AnnotationConstraint { error })?,
            );
        }
        let mut lowered_associated = Vec::with_capacity(associated_anns.len());
        for (name, ann) in associated_anns {
            lowered_associated.push(RoleAssociatedConstraint {
                name: name.clone(),
                value: lowerer
                    .lower_role_arg(ann)
                    .map_err(|error| LoweringError::AnnotationConstraint { error })?,
            });
        }
        Ok((lowered_inputs, lowered_associated, lowerer.into_vars()))
    }

    fn role_impl_method_requirement(
        &self,
        context: &RoleImplLoweringContext,
        name: Name,
    ) -> Option<ResolvedRoleMethodRequirement> {
        let method = self
            .modules
            .role_methods(context.role)
            .iter()
            .find(|method| method.name == name)?;
        let requirement = self.role_requirements.get(&method.def)?;
        let role = self.modules.type_decl_by_id(context.role).map(|role| {
            self.modules
                .type_decl_path(&role)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect::<Vec<_>>()
        })?;
        Some(ResolvedRoleMethodRequirement {
            role_method: method.def,
            role,
            inputs: context.input_signatures.clone(),
            associated: context.associated_signatures.clone(),
            signature: substitute_role_requirement_signature(requirement, context),
        })
    }

    fn lower_role_impl_method_binding(
        &mut self,
        node: &Cst,
        impl_def: DefId,
        module: ModuleId,
        method: &RoleImplMethodDecl,
        target_ann: &AnnType,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        requirement: Option<ResolvedRoleMethodRequirement>,
    ) {
        let Some(expr) = binding_body_expr(node) else {
            self.errors.push(BodyLoweringError::MissingBody {
                def: method.def,
                name: method.name.clone(),
            });
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        if method.vis != Vis::My {
            self.session.register_role_impl_member(method.def, impl_def);
        }
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));
        if let Some(requirement) = &requirement {
            self.session
                .register_role_impl_member_requirement(method.def, requirement.role_method);
        }

        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            method.order,
            method.def,
            &mut self.labels,
        )
        .with_local_method_scope(self.local_method_scope)
        .lower_impl_method_body_expr(
            &expr,
            &binding_arg_patterns(node),
            method.receiver.clone(),
            target_ann,
            binding_type_expr(node),
            type_var_bindings,
            ann_solver_vars,
            requirement.as_ref(),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation, true)
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: method.def,
                name: method.name.clone(),
                error,
            }),
        }
        self.session.infer.restore_level(previous_level);
    }

    fn lower_role_method_signature(
        &mut self,
        node: &Cst,
        module: ModuleId,
        role: &ModuleTypeDecl,
        method: &RoleMethodDecl,
        role_inputs: &[String],
        role_associated: &[String],
    ) {
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let result = self.connect_role_method_signature(
            node,
            module,
            role,
            method,
            role_inputs,
            role_associated,
            root,
        );
        if let Err(error) = result {
            self.errors.push(BodyLoweringError::Expr {
                def: method.def,
                name: method.name.clone(),
                error,
            });
        }
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: method.def }));
        self.session.infer.restore_level(previous_level);
    }

    fn connect_role_method_signature(
        &mut self,
        node: &Cst,
        module: ModuleId,
        role: &ModuleTypeDecl,
        method: &RoleMethodDecl,
        role_inputs: &[String],
        role_associated: &[String],
        root: TypeVar,
    ) -> Result<(), LoweringError> {
        let Some(type_expr) = binding_type_expr(node) else {
            return Ok(());
        };
        let mut builder = ann_type_builder(&self.modules, module, method.order, None);
        for name in role_inputs.iter().chain(role_associated.iter()) {
            builder.add_bare_type_var(name.clone());
        }
        if let Some(first) = role_inputs.first() {
            builder.add_bare_type_var_alias("self", first.clone());
        }
        let signature = build_signature_type_expr(&mut builder, &type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let signature = role_method_signature_with_receiver(
            method.receiver.as_ref(),
            role_inputs.first(),
            signature,
        );
        let role_arg_names = role_inputs
            .iter()
            .chain(role_associated.iter())
            .cloned()
            .collect::<Vec<_>>();
        let role_arg_signatures = role_arg_names
            .iter()
            .map(|name| SignatureType::Var(SignatureVar { name: name.clone() }))
            .collect::<Vec<_>>();

        let (pos, role_args) = {
            let mut lowerer = SignatureLowerer::new(&mut self.session.infer, &self.modules);
            let pos = lowerer
                .lower_pos(&signature)
                .map_err(|error| LoweringError::SignatureConstraint { error })?;
            let mut role_args = Vec::with_capacity(role_arg_signatures.len());
            for signature in &role_arg_signatures {
                role_args.push(
                    lowerer
                        .lower_role_arg(signature)
                        .map_err(|error| LoweringError::SignatureConstraint { error })?,
                );
            }
            (pos, role_args)
        };
        let upper = self.session.infer.alloc_neg(Neg::Var(root));
        self.session.infer.subtype(pos, upper);

        let path = self
            .modules
            .type_decl_path(role)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let inputs = role_args[..role_inputs.len()].to_vec();
        let associated = role_associated
            .iter()
            .cloned()
            .zip(role_args[role_inputs.len()..].iter().copied())
            .map(|(name, value)| RoleAssociatedConstraint { name, value })
            .collect();
        self.session.roles.insert(
            method.def,
            RoleConstraint {
                role: path,
                inputs,
                associated,
            },
        );
        Ok(())
    }

    fn lower_role_method_binding(
        &mut self,
        node: &Cst,
        module: ModuleId,
        role: &ModuleTypeDecl,
        method: &RoleMethodDecl,
        role_inputs: &[String],
        role_associated: &[String],
    ) {
        let Some(expr) = binding_body_expr(node) else {
            self.errors.push(BodyLoweringError::MissingBody {
                def: method.def,
                name: method.name.clone(),
            });
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let role_path = self
            .modules
            .type_decl_path(role)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            method.order,
            method.def,
            &mut self.labels,
        )
        .with_local_method_scope(self.local_method_scope)
        .lower_role_method_body_expr(
            &expr,
            &binding_arg_patterns(node),
            method.receiver.clone(),
            role_path,
            role_inputs,
            role_associated,
            binding_type_expr(node),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation, true);
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: method.def,
                name: method.name.clone(),
                error,
            }),
        }
        self.session.infer.restore_level(previous_level);
    }

    fn lower_act_method_binding_with_aliases(
        &mut self,
        node: &Cst,
        module: ModuleId,
        method: &ActMethodDecl,
        type_var_aliases: &[(String, String)],
    ) {
        let Some(expr) = binding_body_expr(node) else {
            self.errors.push(BodyLoweringError::MissingBody {
                def: method.def,
                name: method.name.clone(),
            });
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            method.order,
            method.def,
            &mut self.labels,
        )
        .with_local_method_scope(self.local_method_scope)
        .with_type_var_aliases(type_var_aliases)
        .lower_act_method_body_expr(
            &expr,
            &binding_arg_patterns(node),
            method.receiver.clone(),
            method.owner,
            binding_type_expr(node),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation, true);
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: method.def,
                name: method.name.clone(),
                error,
            }),
        }
        self.session.infer.restore_level(previous_level);
    }

    fn lower_type_method_binding(
        &mut self,
        node: &Cst,
        module: ModuleId,
        owner: &ModuleTypeDecl,
        method: &TypeMethodDecl,
        type_vars: &[String],
    ) {
        let Some(expr) = binding_body_expr(node) else {
            self.errors.push(BodyLoweringError::MissingBody {
                def: method.def,
                name: method.name.clone(),
            });
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let self_alias = AnnSelfAlias {
            owner: owner.id,
            type_vars: type_vars.to_vec(),
        };
        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            method.order,
            method.def,
            &mut self.labels,
        )
        .with_local_method_scope(self.local_method_scope)
        .with_self_alias(Some(self_alias.clone()))
        .lower_type_method_body_expr(
            &expr,
            &binding_arg_patterns(node),
            method.receiver.clone(),
            method.receiver_kind,
            owner.id,
            &self_alias.type_vars,
            binding_type_expr(node),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation, true);
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: method.def,
                name: method.name.clone(),
                error,
            }),
        }
        self.session.infer.restore_level(previous_level);
    }

    fn connect_binding_annotation(
        &mut self,
        node: &Cst,
        module: ModuleId,
        site: ModuleOrder,
        self_alias: Option<AnnSelfAlias>,
        type_var_aliases: &[(String, String)],
        root: TypeVar,
        computation: Computation,
    ) -> Result<(), LoweringError> {
        let Some(type_expr) = binding_type_expr(node) else {
            return Ok(());
        };
        let mut builder = ann_type_builder(&self.modules, module, site, self_alias);
        add_type_var_aliases(&mut builder, type_var_aliases);
        let ann = builder
            .build_type_expr(&type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        self.check_binding_annotation_type(computation.value, &ann)?;
        AnnConstraintLowerer::new(&mut self.session.infer, &self.modules)
            .connect_computation(
                AnnComputationTarget {
                    value: root,
                    effect: computation.effect,
                },
                &ann,
            )
            .map_err(|error| LoweringError::AnnotationConstraint { error })?;
        Ok(())
    }

    fn check_binding_annotation_type(
        &self,
        value: TypeVar,
        ann: &AnnType,
    ) -> Result<(), LoweringError> {
        let expected = signature_from_ann_type(ann);
        let actual = compact_type_var(self.session.infer.constraints(), value);
        if let Some((actual, expected)) = builtin_annotation_mismatch(&actual.root, &expected) {
            return Err(LoweringError::TypeMismatch {
                actual: actual.surface_name().to_string(),
                expected: expected.surface_name().to_string(),
            });
        }
        Ok(())
    }

    fn finish_binding(
        &mut self,
        def: poly::expr::DefId,
        name: Name,
        root: TypeVar,
        computation: Computation,
        connect_body: bool,
    ) {
        let Some(current) = self.session.poly.defs.get_mut(def) else {
            self.errors.push(BodyLoweringError::NonLetDef { def, name });
            return;
        };
        let Def::Let { body, .. } = current else {
            self.errors.push(BodyLoweringError::NonLetDef { def, name });
            return;
        };

        *body = Some(computation.expr);
        if connect_body {
            self.constrain_def_body(root, computation.value);
        }
        let fetch = BindingFetch::from_evaluation(computation.evaluation);
        self.session.record_binding_fetch(def, fetch);
        if fetch.runs_computation() {
            self.session
                .poly
                .runtime_roots
                .push(poly::expr::RuntimeRoot::ComputedDef(def));
        }
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
    }

    fn constrain_def_body(&mut self, root: TypeVar, body: TypeVar) {
        let body_pos = self.session.infer.alloc_pos(Pos::Var(body));
        let root_neg = self.session.infer.alloc_neg(Neg::Var(root));
        self.session.infer.subtype(body_pos, root_neg);
    }

    fn next_value_decl(&mut self, module: ModuleId, name: &Name) -> Option<crate::ModuleValueDecl> {
        let key = (module, name.clone());
        let cursor = self.value_cursors.entry(key).or_default();
        let decls = self.modules.value_decls(module, name);
        while let Some(decl) = decls.get(*cursor).cloned() {
            *cursor += 1;
            if !self.modules.is_act_operation_def(decl.def) {
                return Some(decl);
            }
        }
        None
    }

    fn next_module_decl(&mut self, module: ModuleId, name: &Name) -> Option<ModuleChildDecl> {
        let key = (module, name.clone());
        let cursor = self.module_cursors.entry(key).or_default();
        let decl = self
            .modules
            .module_decls(module, name)
            .get(*cursor)
            .cloned();
        *cursor += usize::from(decl.is_some());
        decl
    }

    fn next_type_decl(&mut self, module: ModuleId, name: &Name) -> Option<ModuleTypeDecl> {
        let key = (module, name.clone());
        let cursor = self.type_cursors.entry(key).or_default();
        let decl = self.modules.type_decls(module, name).get(*cursor).cloned();
        *cursor += usize::from(decl.is_some());
        decl
    }

    fn next_role_impl_decl(&mut self, module: ModuleId) -> Option<RoleImplDecl> {
        let cursor = self.impl_cursors.entry(module).or_default();
        let decl = self.modules.role_impls(module).get(*cursor).cloned();
        *cursor += usize::from(decl.is_some());
        decl
    }

    fn next_cast_decl(&mut self, module: ModuleId) -> Option<CastDecl> {
        let cursor = self.cast_cursors.entry(module).or_default();
        let decl = self.modules.cast_decls(module).get(*cursor).cloned();
        *cursor += usize::from(decl.is_some());
        decl
    }
}

fn register_declared_type_methods(session: &mut AnalysisSession, modules: &ModuleTable) {
    for method in modules.all_type_methods() {
        if method.vis == poly::expr::Vis::My {
            continue;
        }
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let receiver = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        match method.receiver_kind {
            TypeMethodReceiver::Value => {
                session.register_value_type_method(receiver, method.name.0.clone(), method.def);
            }
            TypeMethodReceiver::Ref => {
                session.register_ref_type_method(receiver, method.name.0.clone(), method.def);
            }
        }
    }
}

fn register_declared_type_field_methods(session: &mut AnalysisSession, modules: &ModuleTable) {
    for method in modules.all_type_field_methods() {
        if method.vis == poly::expr::Vis::My
            || visible_explicit_type_method_exists(
                modules,
                method.owner,
                &method.name,
                method.receiver_kind,
            )
        {
            continue;
        }
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let receiver = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        match method.receiver_kind {
            TypeMethodReceiver::Value => {
                session.register_value_type_method(receiver, method.name.0.clone(), method.def);
            }
            TypeMethodReceiver::Ref => {
                session.register_ref_type_method(receiver, method.name.0.clone(), method.def);
            }
        }
    }
}

fn visible_explicit_type_method_exists(
    modules: &ModuleTable,
    owner: TypeDeclId,
    name: &Name,
    receiver_kind: TypeMethodReceiver,
) -> bool {
    modules.type_methods(owner).iter().any(|method| {
        method.vis != poly::expr::Vis::My
            && method.name == *name
            && method.receiver_kind == receiver_kind
    })
}

fn register_declared_act_methods(session: &mut AnalysisSession, modules: &ModuleTable) {
    for method in modules.all_act_methods() {
        if method.vis == poly::expr::Vis::My {
            continue;
        }
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let effect = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        session.register_effect_method(effect, method.name.0.clone(), method.def);
    }
}

fn register_declared_companion_local_methods(session: &mut AnalysisSession, modules: &ModuleTable) {
    for method in modules.all_type_methods() {
        let Some(scope) = modules.type_companion(method.owner) else {
            continue;
        };
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let receiver = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        match method.receiver_kind {
            TypeMethodReceiver::Value => {
                session.register_local_value_type_method(
                    scope,
                    receiver,
                    method.name.0.clone(),
                    method.def,
                );
            }
            TypeMethodReceiver::Ref => {
                session.register_local_ref_type_method(
                    scope,
                    receiver,
                    method.name.0.clone(),
                    method.def,
                );
            }
        }
    }

    for method in modules.all_act_methods() {
        let Some(scope) = modules.type_companion(method.owner) else {
            continue;
        };
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let effect = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        session.register_local_effect_method(scope, effect, method.name.0.clone(), method.def);
    }

    for method in modules.all_role_methods() {
        let Some(scope) = modules.type_companion(method.owner) else {
            continue;
        };
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let role = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        session.register_local_role_method(scope, role, method.name.0.clone(), method.def);
    }
}

fn register_declared_role_methods(session: &mut AnalysisSession, modules: &ModuleTable) {
    for method in modules.all_role_methods() {
        if method.vis == poly::expr::Vis::My {
            continue;
        }
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let role = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        session.register_role_method(role, method.name.0.clone(), method.def);
    }
}

fn ann_type_builder(
    modules: &ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    self_alias: Option<AnnSelfAlias>,
) -> AnnTypeBuilder<'_> {
    match self_alias {
        Some(self_alias) => AnnTypeBuilder::with_self_alias(modules, module, site, self_alias),
        None => AnnTypeBuilder::new(modules, module, site),
    }
}

fn add_type_var_aliases(builder: &mut AnnTypeBuilder<'_>, aliases: &[(String, String)]) {
    for (alias, target) in aliases {
        builder.add_bare_type_var_alias(alias.clone(), target.clone());
    }
}

fn ann_type_builder_with_aliases<'a>(
    modules: &'a ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    self_alias: Option<AnnSelfAlias>,
    aliases: &[(String, String)],
) -> AnnTypeBuilder<'a> {
    let mut builder = ann_type_builder(modules, module, site, self_alias);
    add_type_var_aliases(&mut builder, aliases);
    builder
}

fn build_signature_type_expr(
    builder: &mut AnnTypeBuilder,
    type_expr: &Cst,
) -> Result<SignatureType, AnnBuildError> {
    builder
        .build_type_expr(type_expr)
        .map(|ann| signature_from_ann_type(&ann))
}

fn role_method_signature_with_receiver(
    receiver: Option<&Name>,
    receiver_type: Option<&String>,
    signature: SignatureType,
) -> SignatureType {
    let (Some(_receiver), Some(receiver_type)) = (receiver, receiver_type) else {
        return signature;
    };
    let param = SignatureType::Var(SignatureVar {
        name: receiver_type.clone(),
    });
    let (ret_eff, ret) = split_effectful_signature(signature);
    SignatureType::Function {
        param: Box::new(param),
        arg_eff: None,
        ret_eff,
        ret: Box::new(ret),
    }
}

fn split_effectful_signature(
    signature: SignatureType,
) -> (Option<SignatureEffectRow>, SignatureType) {
    match signature {
        SignatureType::Effectful { eff, ret } => (Some(eff), *ret),
        signature => (None, signature),
    }
}

fn role_input_variances_from_requirements(
    role_inputs: &[String],
    methods: &[RoleMethodDecl],
    requirements: &FxHashMap<DefId, RoleMethodRequirement>,
) -> Vec<RoleInputVariance> {
    let input_indices = role_inputs
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), index))
        .collect::<FxHashMap<_, _>>();
    let mut variances = vec![RoleInputVariance::Unused; role_inputs.len()];
    for method in methods {
        let Some(requirement) = requirements.get(&method.def) else {
            continue;
        };
        record_role_input_variances_in_signature(
            &requirement.signature,
            &input_indices,
            RoleInputOccurrence::Covariant,
            &mut variances,
        );
    }
    variances
}

fn record_role_input_variances_in_signature(
    signature: &SignatureType,
    input_indices: &FxHashMap<String, usize>,
    occurrence: RoleInputOccurrence,
    variances: &mut [RoleInputVariance],
) {
    match signature {
        SignatureType::Builtin(_) | SignatureType::Named(_) => {}
        SignatureType::Var(var) => {
            if let Some(index) = input_indices.get(&var.name).copied()
                && let Some(slot) = variances.get_mut(index)
            {
                *slot = slot.record(occurrence);
            }
        }
        SignatureType::EffectRow(row) => {
            record_role_input_variances_in_effect_row(row, input_indices, variances);
        }
        SignatureType::Effectful { eff, ret } => {
            record_role_input_variances_in_effect_row(eff, input_indices, variances);
            record_role_input_variances_in_signature(ret, input_indices, occurrence, variances);
        }
        SignatureType::Tuple(items) => {
            for item in items {
                record_role_input_variances_in_signature(
                    item,
                    input_indices,
                    occurrence,
                    variances,
                );
            }
        }
        SignatureType::Apply { callee, args } => {
            record_role_input_variances_in_signature(
                callee,
                input_indices,
                RoleInputOccurrence::Invariant,
                variances,
            );
            for arg in args {
                record_role_input_variances_in_signature(
                    arg,
                    input_indices,
                    RoleInputOccurrence::Invariant,
                    variances,
                );
            }
        }
        SignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            record_role_input_variances_in_signature(
                param,
                input_indices,
                occurrence.flipped(),
                variances,
            );
            if let Some(arg_eff) = arg_eff {
                record_role_input_variances_in_effect_row(arg_eff, input_indices, variances);
            }
            if let Some(ret_eff) = ret_eff {
                record_role_input_variances_in_effect_row(ret_eff, input_indices, variances);
            }
            record_role_input_variances_in_signature(ret, input_indices, occurrence, variances);
        }
    }
}

fn record_role_input_variances_in_effect_row(
    row: &SignatureEffectRow,
    input_indices: &FxHashMap<String, usize>,
    variances: &mut [RoleInputVariance],
) {
    for item in &row.items {
        match item {
            SignatureEffectAtom::Type(ty) => record_role_input_variances_in_signature(
                ty,
                input_indices,
                RoleInputOccurrence::Invariant,
                variances,
            ),
            SignatureEffectAtom::Wildcard => {}
        }
    }
    if let Some(tail) = &row.tail
        && let Some(index) = input_indices.get(&tail.name).copied()
        && let Some(slot) = variances.get_mut(index)
    {
        *slot = slot.record(RoleInputOccurrence::Invariant);
    }
}

fn operation_signature_with_effect(
    signature: SignatureType,
    effect: SignatureType,
) -> Option<SignatureType> {
    let SignatureType::Function {
        param,
        arg_eff,
        ret_eff,
        ret,
    } = signature
    else {
        return None;
    };
    Some(SignatureType::Function {
        param,
        arg_eff,
        ret_eff: Some(operation_return_effect_row(ret_eff, effect)),
        ret,
    })
}

fn operation_return_effect_row(
    ret_eff: Option<SignatureEffectRow>,
    effect: SignatureType,
) -> SignatureEffectRow {
    let mut row = ret_eff.unwrap_or(SignatureEffectRow {
        items: Vec::new(),
        tail: None,
    });
    row.items.insert(0, SignatureEffectAtom::Type(effect));
    row
}

fn signature_from_ann_type(ann: &AnnType) -> SignatureType {
    match ann {
        AnnType::Builtin(builtin) => SignatureType::Builtin(*builtin),
        AnnType::Named(id) => SignatureType::Named(*id),
        AnnType::Var(var) => SignatureType::Var(SignatureVar {
            name: var.name.clone(),
        }),
        AnnType::Wildcard(var) => SignatureType::Var(SignatureVar {
            name: var.name.clone(),
        }),
        AnnType::EffectRow(row) => SignatureType::EffectRow(signature_effect_row_from_ann(row)),
        AnnType::Effectful { eff, ret } => SignatureType::Effectful {
            eff: signature_effect_row_from_ann(eff),
            ret: Box::new(signature_from_ann_type(ret)),
        },
        AnnType::Tuple(items) => SignatureType::Tuple(
            items
                .iter()
                .map(signature_from_ann_type)
                .collect::<Vec<_>>(),
        ),
        AnnType::Apply { callee, args } => SignatureType::Apply {
            callee: Box::new(signature_from_ann_type(callee)),
            args: args.iter().map(signature_from_ann_type).collect(),
        },
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => SignatureType::Function {
            param: Box::new(signature_from_ann_type(param)),
            arg_eff: arg_eff.as_ref().map(signature_effect_row_from_ann),
            ret_eff: ret_eff.as_ref().map(signature_effect_row_from_ann),
            ret: Box::new(signature_from_ann_type(ret)),
        },
    }
}

fn signature_effect_row_from_ann(row: &crate::annotation::AnnEffectRow) -> SignatureEffectRow {
    SignatureEffectRow {
        items: row
            .items
            .iter()
            .map(|atom| match atom {
                crate::annotation::AnnEffectAtom::Type(ty) => {
                    SignatureEffectAtom::Type(signature_from_ann_type(ty))
                }
                crate::annotation::AnnEffectAtom::Wildcard => SignatureEffectAtom::Wildcard,
            })
            .collect(),
        tail: row.tail.as_ref().map(|tail| SignatureVar {
            name: tail.name.clone(),
        }),
    }
}

struct NegSignatureBuilder<'a> {
    modules: &'a ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    self_alias: Option<SignatureSelfAlias>,
}

impl<'a> NegSignatureBuilder<'a> {
    fn with_self_alias(
        modules: &'a ModuleTable,
        module: ModuleId,
        site: ModuleOrder,
        self_alias: SignatureSelfAlias,
    ) -> Self {
        Self {
            modules,
            module,
            site,
            self_alias: Some(self_alias),
        }
    }

    fn build_type_expr(&self, type_expr: &Cst) -> Result<NegSignature, NegSignatureBuildError> {
        self.build_signature_type_expr(type_expr)
            .map(NegSignature::new)
    }

    fn build_signature_type_expr(
        &self,
        type_expr: &Cst,
    ) -> Result<SignatureType, NegSignatureBuildError> {
        if type_expr.kind() != SyntaxKind::TypeExpr {
            return Err(NegSignatureBuildError::ExpectedTypeExpr {
                kind: type_expr.kind(),
            });
        }
        if let Some(arrow) = type_expr
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeArrow)
        {
            let param = self.build_type_head(type_expr)?;
            let arg_eff = arrow
                .children()
                .find(|child| child.kind() == SyntaxKind::TypeRow)
                .map(|row| self.build_effect_row(&row))
                .transpose()?;
            let ret = arrow
                .children()
                .find(|child| child.kind() == SyntaxKind::TypeExpr)
                .ok_or(NegSignatureBuildError::MissingFunctionReturn)?;
            let (ret_eff, ret) = split_effectful_signature(self.build_signature_type_expr(&ret)?);
            return Ok(SignatureType::Function {
                param: Box::new(param),
                arg_eff,
                ret_eff,
                ret: Box::new(ret),
            });
        }

        self.build_type_head(type_expr)
    }

    fn build_type_head(&self, type_expr: &Cst) -> Result<SignatureType, NegSignatureBuildError> {
        let items = type_expr
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .filter(|item| {
                !matches!(item, NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeArrow)
            })
            .collect::<Vec<_>>();

        let Some(first) = items.first() else {
            return Err(NegSignatureBuildError::EmptyTypeExpr);
        };

        if let NodeOrToken::Node(row) = first
            && row.kind() == SyntaxKind::TypeRow
        {
            let ret_items = &items[1..];
            let Some(ret_first) = ret_items.first() else {
                return Err(NegSignatureBuildError::EmptyEffectfulType);
            };
            let (ret, next) = self.build_type_base(ret_items, ret_first)?;
            return Ok(SignatureType::Effectful {
                eff: self.build_effect_row(row)?,
                ret: Box::new(self.build_type_applications(ret, &ret_items[next..])?),
            });
        }

        let (base, next) = self.build_type_base(&items, first)?;
        self.build_type_applications(base, &items[next..])
    }

    fn build_type_base(
        &self,
        items: &[CstItem],
        first: &CstItem,
    ) -> Result<(SignatureType, usize), NegSignatureBuildError> {
        match first {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident => {
                let (path, next) = parse_signature_path_prefix(items)?;
                Ok((self.resolve_signature_path(path)?, next))
            }
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::SigilIdent => {
                Ok((SignatureType::Var(signature_var(token.text())), 1))
            }
            NodeOrToken::Token(token) => {
                Err(NegSignatureBuildError::UnsupportedSyntax { kind: token.kind() })
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeParenGroup => {
                Ok((self.build_type_paren_group(node)?, 1))
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeEffectRow => Ok((
                SignatureType::EffectRow(self.build_type_effect_row(node)?),
                1,
            )),
            NodeOrToken::Node(node) => {
                Err(NegSignatureBuildError::UnsupportedSyntax { kind: node.kind() })
            }
        }
    }

    fn build_type_applications(
        &self,
        base: SignatureType,
        suffixes: &[CstItem],
    ) -> Result<SignatureType, NegSignatureBuildError> {
        let mut args = Vec::new();
        for item in suffixes {
            let NodeOrToken::Node(node) = item else {
                let kind = item
                    .as_token()
                    .map(|token| token.kind())
                    .unwrap_or(SyntaxKind::TypeExpr);
                return Err(NegSignatureBuildError::UnsupportedSyntax { kind });
            };
            match node.kind() {
                SyntaxKind::TypeApply => args.push(self.build_single_type_arg(node)?),
                SyntaxKind::TypeCall => {
                    let call_args = node
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
                        .map(|child| self.build_signature_type_expr(&child))
                        .collect::<Result<Vec<_>, _>>()?;
                    if call_args.is_empty() {
                        return Err(NegSignatureBuildError::UnsupportedSyntax {
                            kind: node.kind(),
                        });
                    }
                    args.extend(call_args);
                }
                _ => {
                    return Err(NegSignatureBuildError::UnsupportedSyntax { kind: node.kind() });
                }
            }
        }

        if args.is_empty() {
            Ok(base)
        } else {
            Ok(SignatureType::Apply {
                callee: Box::new(base),
                args,
            })
        }
    }

    fn build_single_type_arg(&self, apply: &Cst) -> Result<SignatureType, NegSignatureBuildError> {
        let children = apply
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        let [child] = children.as_slice() else {
            return Err(NegSignatureBuildError::UnsupportedSyntax { kind: apply.kind() });
        };
        self.build_signature_type_expr(child)
    }

    fn build_type_paren_group(&self, group: &Cst) -> Result<SignatureType, NegSignatureBuildError> {
        let children = group
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        match children.as_slice() {
            [] => Ok(SignatureType::Builtin(BuiltinType::Unit)),
            [child] => self.build_signature_type_expr(child),
            _ => children
                .iter()
                .map(|child| self.build_signature_type_expr(child))
                .collect::<Result<Vec<_>, _>>()
                .map(SignatureType::Tuple),
        }
    }

    fn build_type_effect_row(
        &self,
        effect_row: &Cst,
    ) -> Result<SignatureEffectRow, NegSignatureBuildError> {
        let row = effect_row
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeRow)
            .ok_or(NegSignatureBuildError::MissingEffectRow)?;
        self.build_effect_row(&row)
    }

    fn build_effect_row(&self, row: &Cst) -> Result<SignatureEffectRow, NegSignatureBuildError> {
        let mut items = Vec::new();
        let mut tail = None;
        let mut seen_tail_separator = false;

        for item in row
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
        {
            match item {
                NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeExpr => {
                    if !seen_tail_separator && is_wildcard_type_expr(&node) {
                        items.push(SignatureEffectAtom::Wildcard);
                        continue;
                    }
                    let ty = self.build_signature_type_expr(&node)?;
                    if seen_tail_separator {
                        let SignatureType::Var(var) = ty else {
                            return Err(NegSignatureBuildError::InvalidEffectRowTail { ty });
                        };
                        tail = Some(var);
                    } else {
                        items.push(SignatureEffectAtom::Type(ty));
                    }
                }
                NodeOrToken::Node(node)
                    if node.kind() == SyntaxKind::Separator && separator_has_semicolon(&node) =>
                {
                    seen_tail_separator = true;
                }
                NodeOrToken::Node(node) if node.kind() == SyntaxKind::Separator => {}
                NodeOrToken::Node(node) => {
                    return Err(NegSignatureBuildError::UnsupportedSyntax { kind: node.kind() });
                }
                NodeOrToken::Token(token) => match token.kind() {
                    SyntaxKind::BracketL | SyntaxKind::BracketR | SyntaxKind::Comma => {}
                    SyntaxKind::Semicolon => seen_tail_separator = true,
                    kind => return Err(NegSignatureBuildError::UnsupportedSyntax { kind }),
                },
            }
        }

        if !seen_tail_separator
            && tail.is_none()
            && items.len() == 1
            && let SignatureEffectAtom::Type(SignatureType::Var(var)) = &items[0]
        {
            return Ok(SignatureEffectRow {
                items: Vec::new(),
                tail: Some(var.clone()),
            });
        }

        Ok(SignatureEffectRow { items, tail })
    }

    fn resolve_signature_path(
        &self,
        path: Vec<Name>,
    ) -> Result<SignatureType, NegSignatureBuildError> {
        if let [name] = path.as_slice() {
            if name.0 == "self"
                && let Some(ty) = self.self_alias_type()
            {
                return Ok(ty);
            }
            if let Some(builtin) = BuiltinType::from_surface_name(name.0.as_str()) {
                return Ok(SignatureType::Builtin(builtin));
            }
            if let Some(decl) = self.modules.lexical_type_at(self.module, name, self.site) {
                return Ok(SignatureType::Named(decl.id));
            }
            return Err(NegSignatureBuildError::UnresolvedTypeName { path });
        }

        let Some((last, prefix)) = path.split_last() else {
            return Err(NegSignatureBuildError::EmptyTypeExpr);
        };
        let Some(module) = self.resolve_module_prefix(prefix) else {
            return Err(NegSignatureBuildError::UnresolvedTypeName { path });
        };
        let Some(decl) = self
            .modules
            .type_at(module, last, signature_module_path_site())
        else {
            return Err(NegSignatureBuildError::UnresolvedTypeName { path });
        };
        Ok(SignatureType::Named(decl.id))
    }

    fn self_alias_type(&self) -> Option<SignatureType> {
        let alias = self.self_alias.as_ref()?;
        let args = alias
            .type_vars
            .iter()
            .map(|name| SignatureType::Var(SignatureVar { name: name.clone() }))
            .collect::<Vec<_>>();
        if args.is_empty() {
            Some(SignatureType::Named(alias.owner))
        } else {
            Some(SignatureType::Apply {
                callee: Box::new(SignatureType::Named(alias.owner)),
                args,
            })
        }
    }

    fn resolve_module_prefix(&self, path: &[Name]) -> Option<ModuleId> {
        let (first, rest) = path.split_first()?;
        let mut current = self
            .modules
            .lexical_module_at(self.module, first, self.site)?;
        for segment in rest {
            current = self
                .modules
                .module_at(current, segment, signature_module_path_site())?;
        }
        Some(current)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NegSignatureBuildError {
    ExpectedTypeExpr { kind: SyntaxKind },
    EmptyTypeExpr,
    EmptyEffectfulType,
    MissingFunctionReturn,
    MissingEffectRow,
    InvalidEffectRowTail { ty: SignatureType },
    UnresolvedTypeName { path: Vec<Name> },
    UnsupportedSyntax { kind: SyntaxKind },
}

fn parse_signature_path_prefix(
    items: &[CstItem],
) -> Result<(Vec<Name>, usize), NegSignatureBuildError> {
    let Some(NodeOrToken::Token(head)) = items.first() else {
        return Err(NegSignatureBuildError::EmptyTypeExpr);
    };
    if head.kind() != SyntaxKind::Ident {
        return Err(NegSignatureBuildError::UnsupportedSyntax { kind: head.kind() });
    }

    let mut segments = vec![Name(head.text().to_string())];
    let mut next = 1;
    for item in &items[1..] {
        let NodeOrToken::Node(path_sep) = item else {
            break;
        };
        if path_sep.kind() != SyntaxKind::PathSep {
            break;
        }

        let Some(segment) = path_sep
            .children_with_tokens()
            .filter_map(|item| item.into_token())
            .find(|token| token.kind() == SyntaxKind::Ident)
        else {
            return Err(NegSignatureBuildError::UnsupportedSyntax {
                kind: path_sep.kind(),
            });
        };
        segments.push(Name(segment.text().to_string()));
        next += 1;
    }

    Ok((segments, next))
}

fn signature_var(text: &str) -> SignatureVar {
    SignatureVar {
        name: text.trim_start_matches('\'').to_string(),
    }
}

fn is_wildcard_type_expr(node: &Cst) -> bool {
    let items = node
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
        .collect::<Vec<_>>();
    let [NodeOrToken::Token(token)] = items.as_slice() else {
        return false;
    };
    token.kind() == SyntaxKind::Ident && token.text() == "_"
}

fn separator_has_semicolon(node: &Cst) -> bool {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|token| token.kind() == SyntaxKind::Semicolon)
}

fn signature_module_path_site() -> ModuleOrder {
    module_path_lookup_site()
}

fn module_path_lookup_site() -> ModuleOrder {
    ModuleOrder::from_index(u32::MAX)
}

struct ActCopyLoweringContext {
    body: Cst,
    type_var_aliases: Vec<(String, String)>,
}

/// expression lowering の入口。
///
/// 1つの owner def の body を lower する間だけ作る。`module` / `site` は module-level lookup の
/// 基準で、`parent` は参照 use-site から SCC edge を張る元になる。
pub struct ExprLowerer<'a> {
    session: &'a mut AnalysisSession,
    modules: &'a ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    parent: poly::expr::DefId,
    labels: Option<&'a mut DumpLabels>,
    self_alias: Option<AnnSelfAlias>,
    type_var_aliases: Vec<(String, String)>,
    local_method_scope: Option<ModuleId>,
    synthetic_var_acts: Vec<SyntheticVarActUse>,
    synthetic_var_act_cursor: usize,
    known_ref_targets: FxHashMap<RefId, DefId>,
    locals: Vec<LocalBinding>,
    effect_views: Vec<LocalEffect>,
    function_frames: Vec<FunctionPredicateFrame>,
    local_generalize_boundary: TypeLevel,
}

enum BuiltinOpTypePath {
    Builtin(BuiltinType),
    Named(Vec<String>),
}

impl<'a> ExprLowerer<'a> {
    pub fn new(
        session: &'a mut AnalysisSession,
        modules: &'a ModuleTable,
        module: ModuleId,
        site: ModuleOrder,
        parent: poly::expr::DefId,
    ) -> Self {
        let local_generalize_boundary = session.infer.current_level();
        let synthetic_var_acts = modules.synthetic_var_act_uses(parent).to_vec();
        Self {
            session,
            modules,
            module,
            site,
            parent,
            labels: None,
            self_alias: None,
            type_var_aliases: Vec::new(),
            local_method_scope: None,
            synthetic_var_acts,
            synthetic_var_act_cursor: 0,
            known_ref_targets: FxHashMap::default(),
            locals: Vec::new(),
            effect_views: Vec::new(),
            function_frames: Vec::new(),
            local_generalize_boundary,
        }
    }

    pub fn with_labels(
        session: &'a mut AnalysisSession,
        modules: &'a ModuleTable,
        module: ModuleId,
        site: ModuleOrder,
        parent: poly::expr::DefId,
        labels: &'a mut DumpLabels,
    ) -> Self {
        let local_generalize_boundary = session.infer.current_level();
        let synthetic_var_acts = modules.synthetic_var_act_uses(parent).to_vec();
        Self {
            session,
            modules,
            module,
            site,
            parent,
            labels: Some(labels),
            self_alias: None,
            type_var_aliases: Vec::new(),
            local_method_scope: None,
            synthetic_var_acts,
            synthetic_var_act_cursor: 0,
            known_ref_targets: FxHashMap::default(),
            locals: Vec::new(),
            effect_views: Vec::new(),
            function_frames: Vec::new(),
            local_generalize_boundary,
        }
    }

    pub fn with_self_alias(mut self, self_alias: Option<AnnSelfAlias>) -> Self {
        self.self_alias = self_alias;
        self
    }

    pub fn with_type_var_aliases(mut self, aliases: &[(String, String)]) -> Self {
        self.type_var_aliases = aliases.to_vec();
        self
    }

    pub fn with_local_method_scope(mut self, scope: Option<ModuleId>) -> Self {
        self.local_method_scope = scope;
        self
    }

    /// CST expression を `poly::Expr` と `Computation` に lower する。
    ///
    /// まだ対応していない suffix / atom は `LoweringError::UnsupportedSyntax` として返す。
    /// fallback の unit 化で IR を捏造しないため、未対応範囲は呼び出し側が診断へ変換する。
    pub fn lower_expr(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        self.lower_expr_with_lambda_scope(node, LambdaScope::Anonymous)
    }

    pub fn lower_binding_body_expr(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        self.lower_expr_with_lambda_scope(node, LambdaScope::Defined)
    }

    pub fn lower_binding_body_with_args(
        &mut self,
        arg_patterns: &[Cst],
        body: &Cst,
        result_type_expr: Option<&Cst>,
    ) -> Result<Computation, LoweringError> {
        self.lower_binding_body_with_args_with_self(arg_patterns, body, result_type_expr, None)
    }

    pub fn lower_binding_body_with_args_to_self(
        &mut self,
        arg_patterns: &[Cst],
        body: &Cst,
        result_type_expr: Option<&Cst>,
        self_value: TypeVar,
    ) -> Result<Computation, LoweringError> {
        self.lower_binding_body_with_args_with_self(
            arg_patterns,
            body,
            result_type_expr,
            Some(self_value),
        )
    }

    fn lower_binding_body_with_args_with_self(
        &mut self,
        arg_patterns: &[Cst],
        body: &Cst,
        result_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
    ) -> Result<Computation, LoweringError> {
        if arg_patterns.is_empty() {
            return self.lower_binding_body_expr(body);
        }
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();
        self.lower_lambda_params(
            arg_patterns,
            body,
            LambdaScope::Defined,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr,
            self_value,
        )
    }

    fn lower_destructured_binding_component(
        &mut self,
        pattern: &Cst,
        hidden_def: DefId,
        name: Name,
    ) -> Result<Computation, LoweringError> {
        let pattern_value = self.fresh_type_var();
        let hidden = self.lower_resolved_value_ref("#destructure".to_string(), hidden_def);
        let pat = self.lower_match_pattern(pattern, pattern_value)?;
        self.subtype_var_to_var(hidden.value, pattern_value);
        self.subtype_var_to_var(pattern_value, hidden.value);
        let target = self.lower_name(name)?;
        Ok(self.prepend_block(
            LoweredLocalStmt {
                stmt: Stmt::Let(Vis::My, pat, hidden.expr),
                effect: hidden.effect,
            },
            target,
        ))
    }

    fn lower_type_method_body_expr(
        &mut self,
        node: &Cst,
        arg_patterns: &[Cst],
        receiver: Name,
        receiver_kind: TypeMethodReceiver,
        owner: TypeDeclId,
        type_vars: &[String],
        result_type_expr: Option<Cst>,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        let self_ann = ann_builder.type_decl_application(owner, type_vars);
        let mut ann_solver_vars = FxHashMap::default();

        let receiver_value = self.fresh_type_var();
        self.connect_type_method_receiver(
            receiver_value,
            receiver_kind,
            &self_ann,
            &mut ann_solver_vars,
        )?;

        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr.as_ref(),
            &[],
        );
        let frame = self
            .function_frames
            .pop()
            .expect("method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Defined, Vec::new(), frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_act_method_body_expr(
        &mut self,
        node: &Cst,
        arg_patterns: &[Cst],
        receiver: Name,
        owner: TypeDeclId,
        result_type_expr: Option<Cst>,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();

        let receiver_value = self.fresh_type_var();
        let receiver_effect = self.fresh_type_var();
        let receiver_subtract = self.connect_act_method_receiver_effect(receiver_effect, owner)?;
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr.as_ref(),
            &[],
        );
        let frame = self
            .function_frames
            .pop()
            .expect("method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.alloc_neg(Neg::Var(receiver_effect));
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Defined, vec![receiver_subtract], frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_role_method_body_expr(
        &mut self,
        node: &Cst,
        arg_patterns: &[Cst],
        receiver: Option<Name>,
        role_path: Vec<String>,
        role_inputs: &[String],
        role_associated: &[String],
        result_type_expr: Option<Cst>,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        for name in role_inputs.iter().chain(role_associated.iter()) {
            ann_builder.add_bare_type_var(name.clone());
        }
        if let Some(first) = role_inputs.first() {
            ann_builder.add_bare_type_var_alias("self", first.clone());
        }
        let role_arg_names = role_inputs
            .iter()
            .chain(role_associated.iter())
            .cloned()
            .collect::<Vec<_>>();
        let role_arg_anns = role_arg_names
            .iter()
            .map(|name| AnnType::Var(ann_builder.ann_type_var_for_role(name)))
            .collect::<Vec<_>>();

        let mut ann_solver_vars = FxHashMap::default();
        let receiver_value = self.fresh_type_var();
        self.connect_role_method_receiver_and_constraint(
            receiver.as_ref(),
            receiver_value,
            role_path,
            role_inputs,
            role_associated,
            &role_arg_anns,
            &mut ann_solver_vars,
        )?;

        let Some(receiver) = receiver else {
            return self.lower_lambda_params(
                arg_patterns,
                node,
                LambdaScope::Defined,
                &mut ann_builder,
                &mut ann_solver_vars,
                result_type_expr.as_ref(),
                None,
            );
        };

        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr.as_ref(),
            &[],
        );
        let frame = self
            .function_frames
            .pop()
            .expect("role method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Defined, Vec::new(), frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_impl_method_body_expr(
        &mut self,
        node: &Cst,
        arg_patterns: &[Cst],
        receiver: Option<Name>,
        receiver_ann: &AnnType,
        result_type_expr: Option<Cst>,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        requirement: Option<&ResolvedRoleMethodRequirement>,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        ann_builder.seed_type_var_bindings(type_var_bindings);

        let Some(receiver) = receiver else {
            let body = self.lower_lambda_params(
                arg_patterns,
                node,
                LambdaScope::Defined,
                &mut ann_builder,
                ann_solver_vars,
                result_type_expr.as_ref(),
                None,
            )?;
            if let Some(requirement) = requirement {
                self.connect_impl_method_requirement(
                    body.value,
                    requirement,
                    type_var_bindings,
                    ann_solver_vars,
                )?;
            }
            return Ok(body);
        };

        let receiver_value = self.fresh_type_var();
        self.connect_type_method_value_annotation(receiver_value, receiver_ann, ann_solver_vars)?;
        let param_uppers = match requirement {
            Some(requirement) => self.impl_method_param_uppers(
                &requirement.signature,
                arg_patterns.len(),
                type_var_bindings,
                ann_solver_vars,
            )?,
            None => Vec::new(),
        };
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            ann_solver_vars,
            result_type_expr.as_ref(),
            &param_uppers,
        );
        let frame = self
            .function_frames
            .pop()
            .expect("impl method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Defined, Vec::new(), frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        if let Some(requirement) = requirement {
            self.connect_impl_method_requirement(
                value,
                requirement,
                type_var_bindings,
                ann_solver_vars,
            )?;
        }

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    /// requirement（impl 入力を代入済みの role method シグネチャ）の引数列を、
    /// member の各 param の上界として引き上げる。`value <: requirement` だけだと
    /// 引数側には下界しか流れず、subject の釘付け（discharge / 共起併合の前提）が
    /// 引数経由の demand に届かない。先頭の Function は receiver なので飛ばす。
    fn impl_method_param_uppers(
        &mut self,
        requirement: &SignatureType,
        param_count: usize,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<Vec<Option<NegId>>, LoweringError> {
        let mut spine = signature_function_step(requirement).map(|(_, ret)| ret);
        let seed = signature_vars_from_ann_vars(type_var_bindings, ann_solver_vars);
        // 足場の区間変数（`Bounds(int|v, v&int)` の v）が root level で生まれると
        // simplify の level 保護で永久に残るので、def の現在 level で lower する。
        let level = self.session.infer.current_level();
        let mut lowerer = SignatureLowerer::with_vars_at_level(
            &mut self.session.infer,
            self.modules,
            seed,
            level,
        );
        let mut uppers = Vec::with_capacity(param_count);
        for _ in 0..param_count {
            let Some((param, ret)) = spine.and_then(signature_function_step) else {
                uppers.push(None);
                continue;
            };
            uppers.push(Some(
                lowerer
                    .lower_neg(param)
                    .map_err(|error| LoweringError::SignatureConstraint { error })?,
            ));
            spine = Some(ret);
        }
        Ok(uppers)
    }

    fn connect_impl_method_requirement(
        &mut self,
        value: TypeVar,
        requirement: &ResolvedRoleMethodRequirement,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        let signature = &requirement.signature;
        self.check_impl_method_requirement_shape(value, signature)?;
        self.check_impl_method_requirement_concrete_type(value, signature)?;
        let seed = signature_vars_from_ann_vars(type_var_bindings, ann_solver_vars);
        let level = self.session.infer.current_level();
        let (upper, summary_root, summary_role) = {
            let mut lowerer = SignatureLowerer::with_vars_at_level(
                &mut self.session.infer,
                self.modules,
                seed,
                level,
            );
            let upper = lowerer
                .lower_neg(signature)
                .map_err(|error| LoweringError::SignatureConstraint { error })?;
            let summary_root = lowerer.fresh_type_var();
            let summary_lower = lowerer
                .lower_pos(signature)
                .map_err(|error| LoweringError::SignatureConstraint { error })?;
            let summary_upper = lowerer.alloc_neg(Neg::Var(summary_root));
            lowerer.infer.subtype(summary_lower, summary_upper);
            let summary_role = lower_impl_requirement_role_constraint(&mut lowerer, requirement)?;
            (upper, summary_root, summary_role)
        };
        let lower = self.session.infer.alloc_pos(Pos::Var(value));
        self.session.infer.subtype(lower, upper);
        self.register_impl_requirement_simplification(summary_root, summary_role);
        Ok(())
    }

    fn register_impl_requirement_simplification(&mut self, root: TypeVar, role: RoleConstraint) {
        let compact = compact_type_var(self.session.infer.constraints(), root);
        let role_predicate = compact_role_constraint(self.session.infer.constraints(), &role);
        let generalized = generalize_prepared_compact_root_with_roles(
            self.session.infer.constraints(),
            TypeLevel::root(),
            compact,
            vec![role_predicate],
            &FxHashSet::default(),
        );
        self.session.register_role_impl_member_simplification(
            self.parent,
            CompactSimplification {
                substitutions: generalized.substitutions,
                sandwiches: generalized.sandwiches,
            },
        );
    }

    fn check_impl_method_requirement_concrete_type(
        &self,
        value: TypeVar,
        requirement: &SignatureType,
    ) -> Result<(), LoweringError> {
        let compact = compact_type_var(self.session.infer.constraints(), value);
        if compact_type_matches_signature(&compact.root, requirement, self.modules) {
            return Ok(());
        }
        Err(LoweringError::SignatureTypeMismatch {
            expected: SignatureShape::of(requirement),
        })
    }

    fn check_impl_method_requirement_shape(
        &self,
        value: TypeVar,
        requirement: &SignatureType,
    ) -> Result<(), LoweringError> {
        let mut visited = Vec::new();
        if self.var_has_signature_shape(value, requirement, &mut visited) {
            return Ok(());
        }
        Err(LoweringError::SignatureShapeMismatch {
            expected: SignatureShape::of(requirement),
        })
    }

    fn var_has_signature_shape(
        &self,
        var: TypeVar,
        requirement: &SignatureType,
        visited: &mut Vec<TypeVar>,
    ) -> bool {
        if visited.contains(&var) {
            return true;
        }
        visited.push(var);
        let Some(bounds) = self.session.infer.constraints().bounds().of(var) else {
            return true;
        };
        let lowers = bounds.lowers();
        lowers.is_empty()
            || lowers
                .iter()
                .any(|bound| self.pos_has_signature_shape(bound.pos, requirement, visited))
    }

    fn pos_has_signature_shape(
        &self,
        pos: PosId,
        requirement: &SignatureType,
        visited: &mut Vec<TypeVar>,
    ) -> bool {
        let required_shape = SignatureShape::of(requirement);
        match self.session.infer.constraints().types().pos(pos) {
            Pos::Bot => true,
            Pos::Var(var) => self.var_has_signature_shape(*var, requirement, visited),
            Pos::Con(_, _) => required_shape != SignatureShape::Function,
            Pos::Fun { ret, .. } => match requirement {
                SignatureType::Function { ret: expected, .. }
                    if SignatureShape::of(expected) == SignatureShape::Function =>
                {
                    self.pos_has_signature_shape(*ret, expected, visited)
                }
                SignatureType::Function { .. } | SignatureType::Var(_) => true,
                _ => false,
            },
            Pos::Record(_) => true,
            Pos::RecordTailSpread { .. } | Pos::RecordHeadSpread { .. } => true,
            Pos::PolyVariant(_) => required_shape != SignatureShape::Function,
            Pos::Tuple(items) => match requirement {
                SignatureType::Var(_) => true,
                _ => items.is_empty() && required_shape != SignatureShape::Function,
            },
            Pos::Row(_) => matches!(
                required_shape,
                SignatureShape::Any | SignatureShape::EffectRow
            ),
            Pos::NonSubtract(inner, _) => {
                self.pos_has_signature_shape(*inner, requirement, visited)
            }
            Pos::Stack { inner, .. } => self.pos_has_signature_shape(*inner, requirement, visited),
            Pos::Union(left, right) => {
                self.pos_has_signature_shape(*left, requirement, visited)
                    || self.pos_has_signature_shape(*right, requirement, visited)
            }
        }
    }

    fn connect_role_method_receiver_and_constraint(
        &mut self,
        receiver: Option<&Name>,
        receiver_value: TypeVar,
        role_path: Vec<String>,
        role_inputs: &[String],
        role_associated: &[String],
        role_arg_anns: &[AnnType],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        let receiver_ann = receiver.and_then(|_| role_arg_anns.first());
        let vars = std::mem::take(ann_solver_vars);
        let mut lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        if let Some(receiver_ann) = receiver_ann.as_ref() {
            lowerer
                .connect_value(receiver_value, receiver_ann)
                .map_err(|error| LoweringError::AnnotationConstraint { error })?;
        }
        let mut role_args = Vec::with_capacity(role_arg_anns.len());
        for ann in role_arg_anns {
            role_args.push(
                lowerer
                    .lower_role_arg(ann)
                    .map_err(|error| LoweringError::AnnotationConstraint { error })?,
            );
        }
        *ann_solver_vars = lowerer.into_vars();

        let inputs = role_args[..role_inputs.len()].to_vec();
        let associated = role_associated
            .iter()
            .cloned()
            .zip(role_args[role_inputs.len()..].iter().copied())
            .map(|(name, value)| RoleAssociatedConstraint { name, value })
            .collect();
        self.session.roles.insert(
            self.parent,
            RoleConstraint {
                role: role_path,
                inputs,
                associated,
            },
        );
        Ok(())
    }

    fn connect_act_method_receiver_effect(
        &mut self,
        effect: TypeVar,
        owner: TypeDeclId,
    ) -> Result<SubtractId, LoweringError> {
        let owner =
            self.modules
                .type_decl_by_id(owner)
                .ok_or(LoweringError::AnnotationConstraint {
                    error: AnnConstraintError::MissingTypeDecl { id: owner },
                })?;
        let path = self
            .modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let subtract = self.session.infer.fresh_subtract_id();
        let inner = self.fresh_type_var();
        let subtractability = Subtractability::Set(path, Vec::new());
        self.session
            .infer
            .declared_subtract_fact(inner, subtract, subtractability.clone());
        let inner_pos = self.alloc_pos(Pos::Var(inner));
        let stacked = self.alloc_pos(Pos::Stack {
            inner: inner_pos,
            weight: StackWeight::push(subtract, subtractability),
        });
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        self.session.infer.subtype(stacked, effect_upper);
        Ok(subtract)
    }

    fn connect_type_method_receiver(
        &mut self,
        receiver_value: TypeVar,
        receiver_kind: TypeMethodReceiver,
        self_ann: &AnnType,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        match receiver_kind {
            TypeMethodReceiver::Value => {
                self.connect_type_method_value_annotation(receiver_value, self_ann, ann_solver_vars)
            }
            TypeMethodReceiver::Ref => {
                let payload = self.fresh_type_var();
                self.connect_type_method_value_annotation(payload, self_ann, ann_solver_vars)?;
                let effect = self.fresh_type_var();
                let effect_arg = self.invariant_var_arg(effect);
                let payload_arg = self.invariant_var_arg(payload);
                self.constrain_lower(
                    receiver_value,
                    Pos::Con(
                        crate::std_paths::control_var_ref_type(),
                        vec![effect_arg, payload_arg],
                    ),
                );
                self.constrain_upper(
                    receiver_value,
                    Neg::Con(
                        crate::std_paths::control_var_ref_type(),
                        vec![effect_arg, payload_arg],
                    ),
                );
                Ok(())
            }
        }
    }

    fn connect_type_method_value_annotation(
        &mut self,
        value: TypeVar,
        ann: &AnnType,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        let vars = std::mem::take(ann_solver_vars);
        let mut lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        let result = lowerer
            .connect_value(value, ann)
            .map(|_| ())
            .map_err(|error| LoweringError::AnnotationConstraint { error });
        *ann_solver_vars = lowerer.into_vars();
        result
    }

    fn connect_type_method_result_annotation(
        &mut self,
        body: Computation,
        type_expr: &Cst,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        let ann = ann_builder
            .build_type_expr(type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let vars = std::mem::take(ann_solver_vars);
        let mut lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        let result = lowerer
            .connect_computation(
                AnnComputationTarget {
                    value: body.value,
                    effect: body.effect,
                },
                &ann,
            )
            .map(|_| ())
            .map_err(|error| LoweringError::AnnotationConstraint { error });
        *ann_solver_vars = lowerer.into_vars();
        result
    }

    fn invariant_var_arg(&mut self, var: TypeVar) -> poly::types::NeuId {
        let lower = self.alloc_pos(Pos::Var(var));
        let upper = self.alloc_neg(Neg::Var(var));
        self.session.infer.alloc_neu(Neu::Bounds(lower, upper))
    }

    fn lower_expr_with_lambda_scope(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::Expr => self.lower_expr_chain(node, lambda_scope),
            _ => self.lower_atom_with_lambda_scope(node, lambda_scope),
        }
    }

    fn lower_expr_chain(
        &mut self,
        node: &Cst,
        head_lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        if let Some(with_block) = node
            .children()
            .find(|child| child.kind() == SyntaxKind::WithBlock)
        {
            return self.lower_with_expr_chain(node, &with_block, head_lambda_scope, None);
        }
        self.lower_expr_chain_prefix(node, head_lambda_scope, false)
    }

    fn lower_expr_chain_prefix(
        &mut self,
        node: &Cst,
        head_lambda_scope: LambdaScope,
        stop_at_with: bool,
    ) -> Result<Computation, LoweringError> {
        self.lower_expr_chain_prefix_with_pipe_arg(node, head_lambda_scope, stop_at_with, None)
    }

    fn lower_expr_chain_prefix_with_pipe_arg(
        &mut self,
        node: &Cst,
        head_lambda_scope: LambdaScope,
        stop_at_with: bool,
        pipe_arg: Option<PipeArg>,
    ) -> Result<Computation, LoweringError> {
        self.lower_expr_chain_prefix_with_pipe_arg_until(
            node,
            head_lambda_scope,
            stop_at_with,
            pipe_arg,
            None,
        )
    }

    fn lower_expr_chain_prefix_with_pipe_arg_until(
        &mut self,
        node: &Cst,
        head_lambda_scope: LambdaScope,
        stop_at_with: bool,
        pipe_arg: Option<PipeArg>,
        stop_kind: Option<SyntaxKind>,
    ) -> Result<Computation, LoweringError> {
        let items = node
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .collect::<Vec<_>>();
        let Some(head) = items.first() else {
            return Ok(self.unit_expr());
        };

        if let Some(name) = expr_symbol_head_name(head) {
            return self.lower_poly_variant_expr_chain(
                name,
                &items,
                1,
                stop_at_with,
                pipe_arg,
                stop_kind,
            );
        }

        let (mut acc, tail_start) = match expr_path_prefix(&items) {
            Some((path, consumed)) if path.len() > 1 => (self.lower_path_name(&path)?, consumed),
            _ => (self.lower_head(head.clone(), head_lambda_scope)?, 1),
        };
        if let Some(pipe_arg) = pipe_arg {
            acc = self.make_app(acc, pipe_arg.expr);
        }
        for item in items.into_iter().skip(tail_start) {
            match item {
                NodeOrToken::Node(child)
                    if should_stop_expr_tail(child.kind(), stop_at_with, stop_kind) =>
                {
                    break;
                }
                NodeOrToken::Node(child) => acc = self.lower_tail_node(acc, &child)?,
                NodeOrToken::Token(token) => {
                    return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
                }
            }
        }
        Ok(acc)
    }

    fn lower_poly_variant_expr_chain(
        &mut self,
        name: String,
        items: &[NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>],
        mut tail_start: usize,
        stop_at_with: bool,
        pipe_arg: Option<PipeArg>,
        stop_kind: Option<SyntaxKind>,
    ) -> Result<Computation, LoweringError> {
        let mut payloads = Vec::new();
        while let Some(NodeOrToken::Node(node)) = items.get(tail_start) {
            if !matches!(node.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC) {
                break;
            }
            let args = node
                .children()
                .filter(|child| child.kind() == SyntaxKind::Expr)
                .collect::<Vec<_>>();
            if args.is_empty() {
                payloads.push(self.unit_expr());
            } else {
                for arg in args {
                    payloads.push(self.lower_expr(&arg)?);
                }
            }
            tail_start += 1;
        }

        let result_value = self.fresh_type_var();
        let expansive = payloads.iter().any(|payload| payload.is_expansive());
        let result_effect = if expansive {
            self.fresh_type_var()
        } else {
            self.fresh_exact_pure_effect()
        };
        let mut pos_payloads = Vec::with_capacity(payloads.len());
        let mut neg_payloads = Vec::with_capacity(payloads.len());
        let mut expr_payloads = Vec::with_capacity(payloads.len());
        for payload in payloads {
            self.subtype_var_to_var(payload.effect, result_effect);
            pos_payloads.push(self.alloc_pos(Pos::Var(payload.value)));
            neg_payloads.push(self.alloc_neg(Neg::Var(payload.value)));
            expr_payloads.push(payload.expr);
        }
        self.constrain_lower(
            result_value,
            Pos::PolyVariant(vec![(name.clone(), pos_payloads)]),
        );
        self.constrain_upper(
            result_value,
            Neg::PolyVariant(vec![(name.clone(), neg_payloads)]),
        );
        let expr = self
            .session
            .poly
            .add_expr(Expr::PolyVariant(name, expr_payloads));
        let mut acc = Computation::new(
            expr,
            result_value,
            result_effect,
            if expansive {
                Evaluation::Computation
            } else {
                Evaluation::Value
            },
        );
        if let Some(pipe_arg) = pipe_arg {
            acc = self.make_app(acc, pipe_arg.expr);
        }

        for item in items.iter().skip(tail_start) {
            match item {
                NodeOrToken::Node(child)
                    if should_stop_expr_tail(child.kind(), stop_at_with, stop_kind) =>
                {
                    break;
                }
                NodeOrToken::Node(child) => acc = self.lower_tail_node(acc, child)?,
                NodeOrToken::Token(token) => {
                    return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
                }
            }
        }
        Ok(acc)
    }

    fn lower_with_expr_chain(
        &mut self,
        node: &Cst,
        with_block: &Cst,
        head_lambda_scope: LambdaScope,
        pipe_arg: Option<PipeArg>,
    ) -> Result<Computation, LoweringError> {
        let items = with_block_lowering_items(with_block);
        let public_names = with_public_binding_names(&items);
        let before_locals = self.locals.len();
        let prefix = self.lower_block_items(items.as_slice())?;
        let public_locals = self.locals[before_locals..]
            .iter()
            .filter(|local| public_names.iter().any(|name| name == &local.name))
            .cloned()
            .collect::<Vec<_>>();
        self.locals.truncate(before_locals);
        self.locals.extend(public_locals);
        let tail =
            self.lower_expr_chain_prefix_with_pipe_arg(node, head_lambda_scope, true, pipe_arg);
        self.locals.truncate(before_locals);
        let tail = tail?;
        Ok(self.prepend_block(
            LoweredLocalStmt {
                stmt: Stmt::Expr(prefix.expr),
                effect: prefix.effect,
            },
            tail,
        ))
    }

    fn lower_head(
        &mut self,
        head: NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        match head {
            NodeOrToken::Token(token) => match token.kind() {
                SyntaxKind::Ident => self.lower_name(Name(token.text().to_string())),
                SyntaxKind::SigilIdent => self.lower_sigil_name(token.text()),
                SyntaxKind::Number => self.lower_number(token.text()),
                SyntaxKind::YadaYada => Ok(self.lower_yada_yada_expr()),
                SyntaxKind::Nullfix => self.lower_nullfix_op_use(token.text()),
                _ => Err(LoweringError::UnsupportedSyntax { kind: token.kind() }),
            },
            NodeOrToken::Node(node) => self.lower_atom_with_lambda_scope(&node, lambda_scope),
        }
    }

    fn lower_atom_with_lambda_scope(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::Expr => self.lower_expr_chain(node, lambda_scope),
            SyntaxKind::LambdaExpr => self.lower_lambda(node, lambda_scope),
            SyntaxKind::MethodLambdaExpr => self.lower_method_lambda(node, lambda_scope),
            SyntaxKind::RecursiveLambdaExpr => self.lower_recursive_lambda(node, lambda_scope),
            SyntaxKind::CaseLambdaExpr => self.lower_case_lambda(node, lambda_scope),
            SyntaxKind::CatchLambdaExpr => self.lower_catch_lambda(node, lambda_scope),
            SyntaxKind::IfExpr => self.lower_if(node),
            SyntaxKind::CaseExpr => self.lower_case(node, lambda_scope),
            SyntaxKind::CatchExpr => self.lower_catch(node, lambda_scope),
            SyntaxKind::Number => self.lower_number(&node.text().to_string()),
            SyntaxKind::YadaYada => Ok(self.lower_yada_yada_expr()),
            SyntaxKind::RuleLit => self.lower_rule_lit(node),
            SyntaxKind::RuleExpr => self.lower_rule_expr(node),
            SyntaxKind::StringLit => self.lower_string_lit(node),
            SyntaxKind::Paren => self.lower_paren(node, lambda_scope),
            SyntaxKind::Bracket => self.lower_list_literal(node),
            SyntaxKind::PrefixNode => self.lower_prefix_op_use(node),
            SyntaxKind::BraceGroup if brace_group_is_record_literal(node) => {
                self.lower_record_literal(node)
            }
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup => self.lower_expr_block(node),
            _ => Err(LoweringError::UnsupportedSyntax { kind: node.kind() }),
        }
    }

    fn lower_lambda(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let patterns = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::Pattern)
            .collect::<Vec<_>>();
        let Some(body) = node
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
                )
            })
            .last()
        else {
            return Err(LoweringError::MissingLambdaBody);
        };
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();
        self.lower_lambda_params(
            patterns.as_slice(),
            &body,
            lambda_scope,
            &mut ann_builder,
            &mut ann_solver_vars,
            None,
            None,
        )
    }

    fn lower_recursive_lambda(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let Some(label) = recursive_lambda_label_name(node) else {
            return self.lower_lambda(node, lambda_scope);
        };

        let boundary = self.local_generalize_boundary;
        let previous_level = self.session.infer.enter_child_level();
        let before_locals = self.locals.len();
        let result = (|| {
            let value = self.fresh_type_var();
            let (pat, def) = self.bind_let_local_with_def(
                label.clone(),
                value,
                LocalCallReturnEffect::Annotated,
                None,
            );
            let body = self.lower_lambda(node, lambda_scope)?;
            self.subtype_var_to_var(body.value, value);
            self.subtype_var_to_var(value, body.value);
            self.set_local_let_body(def, body.expr);
            self.generalize_local_binding(
                def,
                value,
                boundary,
                BindingFetch::from_evaluation(body.evaluation),
            );
            let tail = self.lower_name(label)?;
            Ok(self.prepend_block(
                LoweredLocalStmt {
                    stmt: Stmt::Let(Vis::My, pat, body.expr),
                    effect: body.effect,
                },
                tail,
            ))
        })();
        self.locals.truncate(before_locals);
        self.session.infer.restore_level(previous_level);
        result
    }

    fn lower_method_lambda(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let receiver_name = Name("#method-receiver".to_string());
        let receiver_value = self.fresh_type_var();
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver_name.clone(),
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let receiver = self
            .locals
            .last()
            .cloned()
            .expect("method lambda receiver should be the last local");

        self.function_frames
            .push(FunctionPredicateFrame::new(lambda_scope));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_method_lambda_body(node, receiver);
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("method lambda predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts = self.lambda_predicate_subtracts(lambda_scope, Vec::new(), frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_method_lambda_body(
        &mut self,
        node: &Cst,
        receiver: LocalBinding,
    ) -> Result<Computation, LoweringError> {
        let mut acc = self.lower_local_name(receiver.name.clone(), receiver);
        for child in node.children() {
            acc = self.lower_tail_node(acc, &child)?;
        }
        Ok(acc)
    }

    fn lower_lambda_params(
        &mut self,
        patterns: &[Cst],
        body: &Cst,
        lambda_scope: LambdaScope,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        body_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
    ) -> Result<Computation, LoweringError> {
        if lambda_scope == LambdaScope::Defined && !patterns.is_empty() {
            return self.lower_defined_lambda_params(
                patterns,
                body,
                ann_builder,
                ann_solver_vars,
                body_type_expr,
                self_value,
                &[],
            );
        }

        let Some((pattern, rest)) = patterns.split_first() else {
            let body = self.lower_expr(body)?;
            if let Some(type_expr) = body_type_expr {
                self.connect_type_method_result_annotation(
                    body,
                    type_expr,
                    ann_builder,
                    ann_solver_vars,
                )?;
            }
            return Ok(body);
        };

        let param_value = self.fresh_type_var();
        let annotation = self.connect_lambda_pattern_annotation(
            pattern,
            param_value,
            ann_builder,
            ann_solver_vars,
        )?;
        let before_locals = self.locals.len();
        let pat = self.lower_lambda_pattern(
            pattern,
            param_value,
            annotation.local_effect.clone(),
            annotation.call_return_effect,
        )?;
        self.function_frames
            .push(FunctionPredicateFrame::new(lambda_scope));
        let previous_level = self.session.infer.enter_child_level();
        let previous_local_generalize_boundary = self.local_generalize_boundary;
        self.local_generalize_boundary = previous_level;
        let body_result = self.lower_lambda_params(
            rest,
            body,
            lambda_scope,
            ann_builder,
            ann_solver_vars,
            body_type_expr,
            None,
        );
        self.local_generalize_boundary = previous_local_generalize_boundary;
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("lambda predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(param_value));
        let arg_eff = annotation.arg_eff;
        let predicate_subtracts =
            self.lambda_predicate_subtracts(lambda_scope, annotation.subtracts, frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_defined_tail_after_receiver(
        &mut self,
        patterns: &[Cst],
        body: &Cst,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        body_type_expr: Option<&Cst>,
        param_uppers: &[Option<NegId>],
    ) -> Result<Computation, LoweringError> {
        if !patterns.is_empty() {
            return self.lower_defined_lambda_params(
                patterns,
                body,
                ann_builder,
                ann_solver_vars,
                body_type_expr,
                None,
                param_uppers,
            );
        }

        let previous_level = self.session.infer.enter_child_level();
        let previous_local_generalize_boundary = self.local_generalize_boundary;
        self.local_generalize_boundary = previous_level;
        let body_result = (|| {
            let body = self.lower_expr(body)?;
            if let Some(type_expr) = body_type_expr {
                self.connect_type_method_result_annotation(
                    body,
                    type_expr,
                    ann_builder,
                    ann_solver_vars,
                )?;
            }
            Ok(body)
        })();
        self.local_generalize_boundary = previous_local_generalize_boundary;
        self.session.infer.restore_level(previous_level);
        body_result
    }

    fn lower_defined_lambda_params(
        &mut self,
        patterns: &[Cst],
        body: &Cst,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        body_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
        param_uppers: &[Option<NegId>],
    ) -> Result<Computation, LoweringError> {
        let before_locals = self.locals.len();
        let before_frames = self.function_frames.len();
        let mut params = Vec::with_capacity(patterns.len());

        for (param_index, pattern) in patterns.iter().enumerate() {
            let param_value = self.fresh_type_var();
            if let Some(Some(upper)) = param_uppers.get(param_index) {
                let lower = self.alloc_pos(Pos::Var(param_value));
                self.session.infer.subtype(lower, *upper);
            }
            let annotation = match self.connect_lambda_pattern_annotation(
                pattern,
                param_value,
                ann_builder,
                ann_solver_vars,
            ) {
                Ok(annotation) => annotation,
                Err(error) => {
                    self.locals.truncate(before_locals);
                    self.function_frames.truncate(before_frames);
                    return Err(error);
                }
            };
            let pat = match self.lower_lambda_pattern(
                pattern,
                param_value,
                annotation.local_effect.clone(),
                annotation.call_return_effect,
            ) {
                Ok(pat) => pat,
                Err(error) => {
                    self.locals.truncate(before_locals);
                    self.function_frames.truncate(before_frames);
                    return Err(error);
                }
            };
            self.function_frames
                .push(FunctionPredicateFrame::new(LambdaScope::Defined));
            params.push(LoweredLambdaParam {
                pat,
                value: param_value,
                annotation,
            });
        }

        let skeleton =
            self_value.map(|target| self.constrain_defined_lambda_skeleton(&params, target));

        let previous_level = self.session.infer.enter_child_level();
        let previous_local_generalize_boundary = self.local_generalize_boundary;
        self.local_generalize_boundary = previous_level;
        let body_result = (|| {
            let mut body = self.lower_expr(body)?;
            if let Some(skeleton) = &skeleton {
                self.subtype_var_to_var(body.effect, skeleton.body_effect);
                self.subtype_var_to_var(body.value, skeleton.body_value);
                body = Computation::new(
                    body.expr,
                    skeleton.body_value,
                    skeleton.body_effect,
                    body.evaluation,
                );
            }
            if let Some(type_expr) = body_type_expr {
                self.connect_type_method_result_annotation(
                    body,
                    type_expr,
                    ann_builder,
                    ann_solver_vars,
                )?;
            }
            Ok(body)
        })();
        self.local_generalize_boundary = previous_local_generalize_boundary;
        self.session.infer.restore_level(previous_level);

        let mut body = match body_result {
            Ok(body) => body,
            Err(error) => {
                self.locals.truncate(before_locals);
                self.function_frames.truncate(before_frames);
                return Err(error);
            }
        };

        for param in params.into_iter().rev() {
            let frame = self
                .function_frames
                .pop()
                .expect("lambda predicate frame should be balanced");
            body = self.wrap_lambda_param(LambdaScope::Defined, param, frame, body);
        }
        self.locals.truncate(before_locals);
        Ok(body)
    }

    fn wrap_lambda_param(
        &mut self,
        lambda_scope: LambdaScope,
        param: LoweredLambdaParam,
        frame: FunctionPredicateFrame,
        body: Computation,
    ) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(param.value));
        let predicate_subtracts =
            self.lambda_predicate_subtracts(lambda_scope, param.annotation.subtracts, frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff: param.annotation.arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self
            .session
            .poly
            .add_expr(Expr::Lambda(param.pat, body.expr));
        Computation::value(expr, value, effect)
    }

    fn constrain_defined_lambda_skeleton(
        &mut self,
        params: &[LoweredLambdaParam],
        target: TypeVar,
    ) -> DefinedLambdaSkeleton {
        let body_effect = self.fresh_type_var();
        let body_value = self.fresh_type_var();
        let mut current_effect = body_effect;
        let mut current_value = body_value;

        for param in params.iter().rev() {
            let value = self.fresh_type_var();
            let effect = self.fresh_exact_pure_effect();
            let arg = self.alloc_neg(Neg::Var(param.value));
            let predicate_subtracts = self.lambda_predicate_subtracts(
                LambdaScope::Defined,
                param.annotation.subtracts.clone(),
                FunctionPredicateFrame::new(LambdaScope::Defined),
            );
            let (ret_eff, ret) = self.lambda_output_predicate_vars(
                current_effect,
                current_value,
                &predicate_subtracts,
            );
            self.constrain_lower(
                value,
                Pos::Fun {
                    arg,
                    arg_eff: param.annotation.skeleton_arg_eff,
                    ret_eff,
                    ret,
                },
            );
            current_effect = effect;
            current_value = value;
        }

        self.subtype_var_to_var(current_value, target);
        DefinedLambdaSkeleton {
            body_effect,
            body_value,
        }
    }

    fn connect_lambda_pattern_annotation(
        &mut self,
        pattern: &Cst,
        value: TypeVar,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<LambdaPatternAnnotation, LoweringError> {
        let Some(type_expr) = pattern_type_expr(pattern) else {
            return Ok(LambdaPatternAnnotation {
                arg_eff: self.never_neg(),
                skeleton_arg_eff: self.never_neg(),
                local_effect: None,
                subtracts: Vec::new(),
                call_return_effect: LocalCallReturnEffect::Unannotated,
            });
        };
        let ann = ann_builder
            .build_type_expr(&type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let (effect, arg_eff) = self.lambda_param_effect_slot(&ann);
        let vars = std::mem::take(ann_solver_vars);
        let mut lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        let connection = lowerer
            .connect_computation_detailed(AnnComputationTarget { value, effect }, &ann)
            .map_err(|error| LoweringError::AnnotationConstraint { error });
        *ann_solver_vars = lowerer.into_vars();
        let connection = connection?;
        let skeleton_arg_eff = match connection.effect_stack {
            Some(ref effect_stack) => self.alloc_neg(Neg::Var(effect_stack.inner)),
            None => arg_eff,
        };
        let local_effect = connection
            .effect_stack
            .clone()
            .map(|effect_stack| LocalEffect::Stack {
                inner: effect_stack.inner,
                weight: effect_stack.weight,
            })
            .or_else(|| {
                matches!(ann, AnnType::Effectful { .. }).then_some(LocalEffect::Var(effect))
            });
        Ok(LambdaPatternAnnotation {
            arg_eff,
            skeleton_arg_eff,
            local_effect,
            subtracts: connection.subtracts,
            call_return_effect: LocalCallReturnEffect::Annotated,
        })
    }

    fn lambda_param_effect_slot(&mut self, ann: &AnnType) -> (TypeVar, NegId) {
        if matches!(ann, AnnType::Effectful { .. }) {
            let effect = self.fresh_type_var();
            return (effect, self.alloc_neg(Neg::Var(effect)));
        }

        (self.fresh_exact_pure_effect(), self.never_neg())
    }

    fn lower_paren(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let exprs = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .collect::<Vec<_>>();
        match exprs.as_slice() {
            [] => Ok(self.unit_expr()),
            [expr] => self.lower_expr_with_lambda_scope(expr, lambda_scope),
            _ => {
                let item_lowers = exprs
                    .iter()
                    .map(|expr| self.lower_expr(expr))
                    .collect::<Result<Vec<_>, _>>()?;
                let items = item_lowers
                    .iter()
                    .map(|computation| computation.expr)
                    .collect::<Vec<_>>();
                let value = self.fresh_type_var();
                let expansive = item_lowers.iter().any(|item| item.is_expansive());
                let effect = if expansive {
                    self.fresh_type_var()
                } else {
                    self.fresh_exact_pure_effect()
                };
                let expr = self.session.poly.add_expr(Expr::Tuple(items));
                let item_values = item_lowers
                    .iter()
                    .map(|item| self.alloc_pos(Pos::Var(item.value)))
                    .collect::<Vec<_>>();
                for item in &item_lowers {
                    self.subtype_var_to_var(item.effect, effect);
                }
                self.constrain_lower(value, Pos::Tuple(item_values));
                Ok(Computation::new(
                    expr,
                    value,
                    effect,
                    if expansive {
                        Evaluation::Computation
                    } else {
                        Evaluation::Value
                    },
                ))
            }
        }
    }

    fn lower_expr_block(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let before_locals = self.locals.len();
        let items = block_lowering_items(node);
        let result = self.lower_block_items(items.as_slice());
        self.locals.truncate(before_locals);
        result
    }

    fn lower_block_items(&mut self, items: &[Cst]) -> Result<Computation, LoweringError> {
        let Some((head, rest)) = items.split_first() else {
            return Ok(self.unit_expr());
        };

        match head.kind() {
            SyntaxKind::Binding if local_var_binding_source(head).is_some() => {
                self.lower_local_var_binding(head, rest)
            }
            SyntaxKind::Binding => {
                let lowered = self.lower_local_binding_stmt(head)?;
                let tail = self.lower_block_items(rest)?;
                Ok(self.prepend_block(lowered, tail))
            }
            SyntaxKind::Expr => {
                let head = self.lower_expr(head)?;
                if rest.is_empty() {
                    Ok(head)
                } else {
                    let stmt = LoweredLocalStmt {
                        stmt: Stmt::Expr(head.expr),
                        effect: head.effect,
                    };
                    let tail = self.lower_block_items(rest)?;
                    Ok(self.prepend_block(stmt, tail))
                }
            }
            SyntaxKind::ForStmt => {
                let head = self.lower_for_stmt(head)?;
                if rest.is_empty() {
                    Ok(head)
                } else {
                    let stmt = LoweredLocalStmt {
                        stmt: Stmt::Expr(head.expr),
                        effect: head.effect,
                    };
                    let tail = self.lower_block_items(rest)?;
                    Ok(self.prepend_block(stmt, tail))
                }
            }
            kind => Err(LoweringError::UnsupportedSyntax { kind }),
        }
    }

    fn lower_for_stmt(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let label = for_label(node)
            .map(|label| {
                for_label_name(&label).ok_or(LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::ForLabel,
                })
            })
            .transpose()?;
        let has_label = label.is_some();
        let iter_node = for_iter_expr(node).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::ForHeader,
        })?;
        let body = for_body_expr(node).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::ForBody,
        })?;
        let pattern = for_pattern(node).ok_or(LoweringError::UnsupportedPatternSyntax {
            kind: SyntaxKind::ForHeader,
        })?;

        let iter = self.lower_expr(&iter_node)?;
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();
        let body = match label {
            Some(label) => self.lower_labeled_for_body(
                label,
                pattern,
                &body,
                &mut ann_builder,
                &mut ann_solver_vars,
            )?,
            None => self.lower_lambda_params(
                &[pattern],
                &body,
                LambdaScope::Anonymous,
                &mut ann_builder,
                &mut ann_solver_vars,
                None,
                None,
            )?,
        };
        let for_in = if has_label {
            self.lower_std_value_ref(crate::std_paths::control_flow_label_loop_for_in_value())?
        } else {
            self.lower_std_value_ref(crate::std_paths::control_flow_loop_for_in_value())?
        };
        let applied_iter = self.make_app(for_in, iter);
        Ok(self.make_app(applied_iter, body))
    }

    fn lower_labeled_for_body(
        &mut self,
        label: Name,
        item_pattern: Cst,
        body: &Cst,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<Computation, LoweringError> {
        let label_value = self.fresh_type_var();
        let before_locals = self.locals.len();
        let pat =
            self.bind_pattern_local(label, label_value, None, LocalCallReturnEffect::Annotated);

        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Anonymous));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_lambda_params(
            &[item_pattern],
            body,
            LambdaScope::Anonymous,
            ann_builder,
            ann_solver_vars,
            None,
            None,
        );
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("labeled for lambda predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(label_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Anonymous, Vec::new(), frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_local_binding_stmt(&mut self, node: &Cst) -> Result<LoweredLocalStmt, LoweringError> {
        let arg_patterns = binding_arg_patterns(node);
        if arg_patterns.is_empty() && !crate::binding_has_single_head_pattern(node) {
            return self.lower_local_pattern_binding_stmt(node);
        }

        let name = crate::binding_name(node).ok_or(LoweringError::MissingLocalBindingName)?;
        let body = binding_body_expr(node).ok_or(LoweringError::MissingLocalBindingBody)?;
        let boundary = self.local_generalize_boundary;
        let previous_level = self.session.infer.enter_child_level();
        let result = (|| {
            let value = self.fresh_type_var();
            let call_return_effect = local_binding_call_return_effect(node);
            let (pat, def) = self.bind_let_local_with_def(name, value, call_return_effect, None);
            let body = self.lower_local_binding_body(node, &body, Some(value))?;
            self.subtype_var_to_var(body.value, value);
            self.connect_local_binding_annotation(node, value, body)?;
            self.set_local_let_body(def, body.expr);
            self.generalize_local_binding(
                def,
                value,
                boundary,
                BindingFetch::from_evaluation(body.evaluation),
            );

            Ok(LoweredLocalStmt {
                stmt: Stmt::Let(Vis::My, pat, body.expr),
                effect: body.effect,
            })
        })();
        self.session.infer.restore_level(previous_level);
        result
    }

    fn lower_local_pattern_binding_stmt(
        &mut self,
        node: &Cst,
    ) -> Result<LoweredLocalStmt, LoweringError> {
        let pattern = crate::binding_pattern(node).ok_or(LoweringError::MissingLocalBindingName)?;
        let body_node = binding_body_expr(node).ok_or(LoweringError::MissingLocalBindingBody)?;
        let previous_level = self.session.infer.enter_child_level();
        let result = (|| {
            let body = self.lower_expr(&body_node)?;
            let value = self.fresh_type_var();
            let pat = self.lower_lambda_pattern(
                &pattern,
                value,
                None,
                local_binding_call_return_effect(node),
            )?;
            self.subtype_var_to_var(body.value, value);
            self.subtype_var_to_var(value, body.value);
            self.connect_local_binding_annotation(node, value, body)?;
            Ok(LoweredLocalStmt {
                stmt: Stmt::Let(Vis::My, pat, body.expr),
                effect: body.effect,
            })
        })();
        self.session.infer.restore_level(previous_level);
        result
    }

    fn lower_local_var_binding(
        &mut self,
        node: &Cst,
        rest: &[Cst],
    ) -> Result<Computation, LoweringError> {
        let source =
            local_var_binding_source(node).ok_or(LoweringError::MissingLocalBindingName)?;
        let init_name = var_init_name(&source).ok_or(LoweringError::MissingLocalBindingName)?;
        let reference_name =
            var_reference_name(&source).ok_or(LoweringError::MissingLocalBindingName)?;
        let local_act = self.next_synthetic_var_act(&reference_name)?;
        let body = binding_body_expr(node).ok_or(LoweringError::MissingLocalBindingBody)?;
        let boundary = self.local_generalize_boundary;
        let init_value = self.fresh_type_var();
        let init = self.lower_local_binding_body(node, &body, None)?;
        self.subtype_var_to_var(init.value, init_value);

        let (init_pat, init_def) = self.bind_let_local_with_def(
            init_name.clone(),
            init_value,
            LocalCallReturnEffect::Annotated,
            Some(init.expr),
        );
        self.generalize_local_binding(
            init_def,
            init_value,
            boundary,
            BindingFetch::from_evaluation(init.evaluation),
        );
        let init_stmt = LoweredLocalStmt {
            stmt: Stmt::Let(Vis::My, init_pat, init.expr),
            effect: init.effect,
        };

        let reference = self.lower_var_ref_constructor(&local_act, init_value)?;
        let reference_value = self.fresh_type_var();
        self.subtype_var_to_var(reference.value, reference_value);
        self.constrain_local_ref_value(reference_value, init_value);
        let (reference_pat, reference_def) = self.bind_let_local_with_def(
            reference_name.clone(),
            reference_value,
            LocalCallReturnEffect::Annotated,
            Some(reference.expr),
        );
        self.generalize_local_binding(
            reference_def,
            reference_value,
            boundary,
            BindingFetch::from_evaluation(reference.evaluation),
        );
        let reference_stmt = LoweredLocalStmt {
            stmt: Stmt::Let(Vis::My, reference_pat, reference.expr),
            effect: reference.effect,
        };

        let tail = self.lower_block_items(rest)?;
        let wrapped = self.wrap_var_binding_run(&local_act, init_name, init_value, tail)?;
        let with_reference = self.prepend_block(reference_stmt, wrapped);
        Ok(self.prepend_block(init_stmt, with_reference))
    }

    fn next_synthetic_var_act(
        &mut self,
        reference_name: &Name,
    ) -> Result<SyntheticVarActUse, LoweringError> {
        let Some(next) = self
            .synthetic_var_acts
            .get(self.synthetic_var_act_cursor)
            .cloned()
        else {
            return Err(LoweringError::MissingLocalVarAct {
                name: reference_name.clone(),
            });
        };
        if next.source != *reference_name {
            return Err(LoweringError::MissingLocalVarAct {
                name: reference_name.clone(),
            });
        }
        self.synthetic_var_act_cursor += 1;
        Ok(next)
    }

    fn lower_local_binding_body(
        &mut self,
        binding: &Cst,
        body: &Cst,
        self_value: Option<TypeVar>,
    ) -> Result<Computation, LoweringError> {
        let arg_patterns = binding_arg_patterns(binding);
        if arg_patterns.is_empty() {
            return self.lower_expr(body);
        }
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();
        let result_type_expr = binding_type_expr(binding);
        self.lower_lambda_params(
            arg_patterns.as_slice(),
            body,
            LambdaScope::Defined,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr.as_ref(),
            self_value,
        )
    }

    fn connect_local_binding_annotation(
        &mut self,
        node: &Cst,
        value: TypeVar,
        computation: Computation,
    ) -> Result<(), LoweringError> {
        let Some(type_expr) = binding_type_expr(node) else {
            return Ok(());
        };
        let mut builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        let ann = builder
            .build_type_expr(&type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        AnnConstraintLowerer::new(&mut self.session.infer, self.modules)
            .connect_computation(
                AnnComputationTarget {
                    value,
                    effect: computation.effect,
                },
                &ann,
            )
            .map(|_| ())
            .map_err(|error| LoweringError::AnnotationConstraint { error })
    }

    fn lower_var_ref_constructor(
        &mut self,
        act: &SyntheticVarActUse,
        payload: TypeVar,
    ) -> Result<Computation, LoweringError> {
        let var_ref = self.lower_var_act_member(act, "var_ref")?;
        let unit = self.unit_expr();
        let reference = self.make_app(var_ref, unit);
        self.constrain_local_ref_value(reference.value, payload);
        Ok(reference)
    }

    fn wrap_var_binding_run(
        &mut self,
        act: &SyntheticVarActUse,
        init_name: Name,
        init_value: TypeVar,
        body: Computation,
    ) -> Result<Computation, LoweringError> {
        let run = self.lower_var_act_member(act, "run")?;
        let init = self.lower_name(init_name)?;
        self.subtype_var_to_var(init.value, init_value);
        let run_with_init = self.make_app(run, init);
        Ok(self.make_app(run_with_init, body))
    }

    fn lower_var_act_member(
        &mut self,
        act: &SyntheticVarActUse,
        member: &str,
    ) -> Result<Computation, LoweringError> {
        let member_name = Name(member.to_string());
        let target = self
            .modules
            .type_companion(act.act)
            .and_then(|companion| {
                self.modules
                    .value_decls(companion, &member_name)
                    .first()
                    .map(|decl| decl.def)
            })
            .ok_or_else(|| LoweringError::UnresolvedName {
                name: Name(format!("{}::{member}", act.source.0)),
            })?;
        Ok(self.lower_resolved_value_ref(format!("{}::{member}", act.source.0), target))
    }

    fn lower_resolved_value_ref(&mut self, label: String, target: DefId) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let reference = self.session.poly.add_ref();
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, label);
        }
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value,
            },
        );
        self.known_ref_targets.insert(reference, target);
        self.session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: reference,
            target,
        });

        let expr = self.session.poly.add_expr(Expr::Var(reference));
        Computation::value(expr, value, effect)
    }

    fn constrain_local_ref_value(&mut self, reference: TypeVar, payload: TypeVar) {
        let effect = self.fresh_type_var();
        let effect_arg = self.invariant_var_arg(effect);
        let payload_arg = self.invariant_var_arg(payload);
        let args = vec![effect_arg, payload_arg];
        self.constrain_lower(
            reference,
            Pos::Con(crate::std_paths::control_var_ref_type(), args.clone()),
        );
        self.constrain_upper(
            reference,
            Neg::Con(crate::std_paths::control_var_ref_type(), args),
        );
    }

    fn bind_let_local_with_def(
        &mut self,
        name: Name,
        value: TypeVar,
        call_return_effect: LocalCallReturnEffect,
        body: Option<poly::expr::ExprId>,
    ) -> (PatId, DefId) {
        let def = self.session.poly.defs.fresh();
        self.session.poly.defs.set(
            def,
            Def::Let {
                vis: Vis::My,
                scheme: None,
                body,
                children: Vec::new(),
            },
        );
        if let Some(labels) = self.labels.as_mut() {
            labels.set_def_label(def, name.0.clone());
        }
        self.locals.push(LocalBinding {
            name,
            def,
            value,
            effect: None,
            call_return_effect,
            scheme: None,
        });
        (self.session.poly.add_pat(Pat::Var(def)), def)
    }

    fn set_local_let_body(&mut self, def: DefId, body_expr: poly::expr::ExprId) {
        let Some(Def::Let { body, .. }) = self.session.poly.defs.get_mut(def) else {
            unreachable!("local binding def should be a let");
        };
        *body = Some(body_expr);
    }

    fn set_local_let_scheme(&mut self, def: DefId, new_scheme: Scheme) {
        let Some(Def::Let { scheme, .. }) = self.session.poly.defs.get_mut(def) else {
            unreachable!("local binding def should be a let");
        };
        *scheme = Some(new_scheme);
    }

    fn prepend_block(&mut self, head: LoweredLocalStmt, tail: Computation) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_type_var();
        self.subtype_var_to_var(head.effect, effect);
        self.subtype_var_to_var(tail.effect, effect);
        self.subtype_var_to_var(tail.value, value);
        let expr = self
            .session
            .poly
            .add_expr(Expr::Block(vec![head.stmt], Some(tail.expr)));
        Computation::computation(expr, value, effect)
    }

    fn lower_number(&mut self, text: &str) -> Result<Computation, LoweringError> {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let (lit, primitive) = parse_number_lit(text)?;

        self.constrain_lower(value, primitive_type(primitive));
        let expr = self.session.poly.add_expr(Expr::Lit(lit));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_yada_yada_expr(&mut self) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(value, Pos::Bot);
        self.constrain_upper(value, Neg::Bot);
        let expr = self
            .session
            .poly
            .add_expr(Expr::PrimitiveOp(PrimitiveOp::YadaYada));
        Computation::value(expr, value, effect)
    }

    fn lower_bool(&mut self, value: bool) -> Computation {
        let slot = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(slot, primitive_type("bool"));
        let expr = self.session.poly.add_expr(Expr::Lit(Lit::Bool(value)));
        Computation::value(expr, slot, effect)
    }

    fn lower_string_lit(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        if node
            .children()
            .all(|child| child.kind() != SyntaxKind::StringInterp)
        {
            return self.lower_plain_string_lit(node);
        }

        self.lower_string_lit_parts(string_lit_parts(node)?)
    }

    fn lower_string_lit_parts(
        &mut self,
        parts: Vec<StringLitPart>,
    ) -> Result<Computation, LoweringError> {
        let mut acc = None;
        for part in parts {
            let part = match part {
                StringLitPart::Text(text) => self.string_value(text),
                StringLitPart::Interp(part) => self.lower_string_interp_part(part)?,
            };
            acc = Some(match acc {
                Some(left) => self.concat_string_values(left, part)?,
                None => part,
            });
        }
        Ok(acc.unwrap_or_else(|| self.string_value(String::new())))
    }

    fn lower_string_interp_part(
        &mut self,
        part: StringInterpPart,
    ) -> Result<Computation, LoweringError> {
        let value = self.lower_expr(&part.expr)?;
        if !part.format.has_layout() {
            return Ok(self.lower_format_kind_selection(value, part.format.kind));
        }

        let format_spec = self.format_spec_value(&part.format)?;
        let formatter = self.lower_std_value_ref(crate::std_paths::core_fmt_value(
            part.format.kind.format_function_name(),
        ))?;
        let formatter = self.make_app(formatter, format_spec);
        Ok(self.make_app(formatter, value))
    }

    fn lower_format_kind_selection(&mut self, value: Computation, kind: FormatKind) -> Computation {
        self.lower_synthetic_selection(value, kind.method_name().to_string())
    }

    fn format_spec_value(&mut self, spec: &FormatSpec) -> Result<Computation, LoweringError> {
        let fields = vec![
            ("kind".to_string(), self.format_kind_value(spec.kind)?),
            (
                "align".to_string(),
                self.optional_format_align_value(spec.align)?,
            ),
            (
                "sign".to_string(),
                self.optional_format_sign_value(spec.sign)?,
            ),
            (
                "fill".to_string(),
                self.optional_string_value(spec.fill.clone())?,
            ),
            ("width".to_string(), self.optional_int_value(spec.width)?),
            (
                "precision".to_string(),
                self.optional_int_value(spec.precision)?,
            ),
            ("alternate".to_string(), self.lower_bool(spec.alternate)),
            ("zero_pad".to_string(), self.lower_bool(spec.zero_pad)),
        ];
        let record = self.synthetic_record_value(fields);
        let constructor =
            self.lower_std_value_ref(crate::std_paths::core_fmt_value("format_spec"))?;
        Ok(self.make_app(constructor, record))
    }

    fn format_kind_value(&mut self, kind: FormatKind) -> Result<Computation, LoweringError> {
        self.lower_std_value_ref(crate::std_paths::core_fmt_format_kind_value(
            kind.variant_name(),
        ))
    }

    fn optional_format_align_value(
        &mut self,
        align: Option<FormatAlign>,
    ) -> Result<Computation, LoweringError> {
        match align {
            Some(align) => {
                let value = self.lower_std_value_ref(
                    crate::std_paths::core_fmt_format_align_value(align.variant_name()),
                )?;
                self.some_value(value)
            }
            None => self.none_value(),
        }
    }

    fn optional_format_sign_value(
        &mut self,
        sign: Option<FormatSign>,
    ) -> Result<Computation, LoweringError> {
        match sign {
            Some(sign) => {
                let value = self.lower_std_value_ref(
                    crate::std_paths::core_fmt_format_sign_value(sign.variant_name()),
                )?;
                self.some_value(value)
            }
            None => self.none_value(),
        }
    }

    fn optional_string_value(
        &mut self,
        value: Option<String>,
    ) -> Result<Computation, LoweringError> {
        match value {
            Some(value) => {
                let value = self.string_value(value);
                self.some_value(value)
            }
            None => self.none_value(),
        }
    }

    fn optional_int_value(&mut self, value: Option<i64>) -> Result<Computation, LoweringError> {
        match value {
            Some(value) => {
                let value = self.int_value(value);
                self.some_value(value)
            }
            None => self.none_value(),
        }
    }

    fn some_value(&mut self, value: Computation) -> Result<Computation, LoweringError> {
        let some = self.lower_std_value_ref(crate::std_paths::data_opt_value("just"))?;
        Ok(self.make_app(some, value))
    }

    fn none_value(&mut self) -> Result<Computation, LoweringError> {
        self.lower_std_value_ref(crate::std_paths::data_opt_value("nil"))
    }

    fn concat_string_values(
        &mut self,
        left: Computation,
        right: Computation,
    ) -> Result<Computation, LoweringError> {
        let concat = self.lower_std_value_ref(crate::std_paths::text_str_concat_value())?;
        let partial = self.make_app(concat, left);
        Ok(self.make_app(partial, right))
    }

    fn lower_plain_string_lit(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let text = plain_string_lit_text(node)?;
        Ok(self.string_value(text))
    }

    fn string_value(&mut self, text: String) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(
            value,
            Pos::Con(crate::std_paths::text_str_type(), Vec::new()),
        );
        let expr = self.session.poly.add_expr(Expr::Lit(Lit::Str(text)));
        Computation::value(expr, value, effect)
    }

    fn int_value(&mut self, number: i64) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(value, primitive_type("int"));
        let expr = self.session.poly.add_expr(Expr::Lit(Lit::Int(number)));
        Computation::value(expr, value, effect)
    }

    fn synthetic_record_value(&mut self, fields: Vec<(String, Computation)>) -> Computation {
        let result_value = self.fresh_type_var();
        let expansive = fields.iter().any(|(_, value)| value.is_expansive());
        let result_effect = if expansive {
            self.fresh_type_var()
        } else {
            self.fresh_exact_pure_effect()
        };
        let record_fields = fields
            .iter()
            .map(|(name, value)| RecordField {
                name: name.clone(),
                value: self.alloc_pos(Pos::Var(value.value)),
                optional: false,
            })
            .collect::<Vec<_>>();
        for (_, value) in &fields {
            self.subtype_var_to_var(value.effect, result_effect);
        }
        self.constrain_lower(result_value, Pos::Record(record_fields));

        let expr_fields = fields
            .into_iter()
            .map(|(name, value)| (name, value.expr))
            .collect();
        let expr = self.session.poly.add_expr(Expr::Record {
            fields: expr_fields,
            spread: RecordSpread::None,
        });
        Computation::new(
            expr,
            result_value,
            result_effect,
            if expansive {
                Evaluation::Computation
            } else {
                Evaluation::Value
            },
        )
    }

    fn lower_rule_lit(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        if let Some(text) = plain_rule_lit_text(node) {
            return self.rule_token_parser(text);
        }

        let before_locals = self.locals.len();
        let result = (|| {
            let body = self.lower_rule_lit_sequence(rule_lit_parts(node)?)?;
            Ok(self.thunk_computation(body))
        })();
        self.locals.truncate(before_locals);
        result
    }

    fn lower_rule_expr(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let before_locals = self.locals.len();
        let result = (|| {
            let body = self.rule_expr_body(node)?;
            Ok(self.thunk_computation(body.expr))
        })();
        self.locals.truncate(before_locals);
        result
    }

    fn lower_rule_lit_sequence(
        &mut self,
        parts: Vec<RuleLitPart>,
    ) -> Result<Computation, LoweringError> {
        let mut stmts = Vec::new();
        let mut fields = Vec::new();
        for part in parts {
            match part {
                RuleLitPart::Token(text) => {
                    if !text.is_empty() {
                        let parser = self.rule_token_parser(text)?;
                        let run = self.run_rule_parser(parser);
                        stmts.push(LoweredLocalStmt {
                            stmt: Stmt::Expr(run.expr),
                            effect: run.effect,
                        });
                    }
                }
                RuleLitPart::Parser(parser) => {
                    let parser = self.lower_rule_item(&parser)?.parser;
                    let run = self.run_rule_parser(parser);
                    stmts.push(LoweredLocalStmt {
                        stmt: Stmt::Expr(run.expr),
                        effect: run.effect,
                    });
                }
                RuleLitPart::CaptureWord(name) => {
                    let parser = self.rule_word_parser()?;
                    let run = self.run_rule_parser(parser);
                    let (stmt, captured) = self.bind_rule_capture(name.clone(), run);
                    stmts.push(stmt);
                    fields.push((name, captured));
                }
                RuleLitPart::CaptureParser { name, parser } => {
                    let parser = self.lower_expr(&parser)?;
                    let run = self.run_rule_parser(parser);
                    let (stmt, captured) = self.bind_rule_capture(name.clone(), run);
                    stmts.push(stmt);
                    fields.push((name, captured));
                }
            }
        }

        let tail = if fields.is_empty() {
            self.unit_expr()
        } else {
            self.rule_record_expr(fields)
        };
        Ok(self.rule_block_expr(stmts, tail))
    }

    fn rule_expr_body(&mut self, node: &Cst) -> Result<RuleLowered, LoweringError> {
        let group = node
            .children()
            .find(|child| child.kind() == SyntaxKind::BraceGroup)
            .ok_or(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::RuleExpr,
            })?;
        self.lower_rule_container_body(&group)
    }

    fn lower_rule_container_body(&mut self, node: &Cst) -> Result<RuleLowered, LoweringError> {
        let mut lowered = rule_branches(node)
            .into_iter()
            .map(|branch| self.lower_rule_sequence(branch))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter();
        let Some(first) = lowered.next() else {
            return Ok(RuleLowered {
                expr: self.unit_expr(),
                semantic: RuleSemantic::Unit,
            });
        };
        lowered.try_fold(first, |left, right| {
            let choice = self.std_parse_ref("choice")?;
            let left_parser = self.thunk_computation(left.expr);
            let right_parser = self.thunk_computation(right.expr);
            let partial = self.make_app(choice, left_parser);
            let expr = self.make_app(partial, right_parser);
            let semantic =
                if left.semantic == RuleSemantic::Unit && right.semantic == RuleSemantic::Unit {
                    RuleSemantic::Unit
                } else {
                    RuleSemantic::Value
                };
            Ok(RuleLowered { expr, semantic })
        })
    }

    fn lower_rule_sequence(&mut self, items: Vec<Cst>) -> Result<RuleLowered, LoweringError> {
        let mut stmts = Vec::new();
        let mut fields = Vec::new();
        let mut value = None;

        for item in items {
            if let Some((name, parser)) = rule_expr_capture(&item) {
                let parser = self.lower_expr(&parser)?;
                let unit = self.unit_expr();
                let run = self.make_app(parser, unit);
                let (stmt, captured) = self.bind_rule_capture(name.clone(), run);
                stmts.push(stmt);
                fields.push((name, captured));
                continue;
            }

            let lowered = self.lower_rule_item(&item)?;
            let unit = self.unit_expr();
            let run = self.make_app(lowered.parser, unit);
            match lowered.semantic {
                RuleSemantic::Unit => stmts.push(LoweredLocalStmt {
                    stmt: Stmt::Expr(run.expr),
                    effect: run.effect,
                }),
                RuleSemantic::Record | RuleSemantic::Value => {
                    if value.is_some() {
                        return Err(LoweringError::UnsupportedSyntax {
                            kind: SyntaxKind::RuleExpr,
                        });
                    }
                    value = Some(run);
                }
            }
        }

        let (tail, semantic) = if fields.is_empty() {
            match value {
                Some(value) => (value, RuleSemantic::Value),
                None => (self.unit_expr(), RuleSemantic::Unit),
            }
        } else {
            if value.is_some() {
                return Err(LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::RuleExpr,
                });
            }
            (self.rule_record_expr(fields), RuleSemantic::Record)
        };
        Ok(RuleLowered {
            expr: self.rule_block_expr(stmts, tail),
            semantic,
        })
    }

    fn lower_rule_item(&mut self, node: &Cst) -> Result<RuleParserItem, LoweringError> {
        if let Some(quant) = rule_quant(node) {
            return self.lower_rule_quant(node, quant);
        }

        if let Some(text) = plain_string_expr_text(node)? {
            return Ok(RuleParserItem {
                parser: self.rule_token_parser(text)?,
                semantic: RuleSemantic::Unit,
            });
        }

        if let Some(paren) = direct_child(node, SyntaxKind::Paren) {
            let body = self.lower_rule_container_body(&paren)?;
            return Ok(RuleParserItem {
                parser: self.thunk_computation(body.expr),
                semantic: body.semantic,
            });
        }

        Ok(RuleParserItem {
            parser: self.lower_expr(node)?,
            semantic: RuleSemantic::Value,
        })
    }

    fn lower_rule_quant(
        &mut self,
        node: &Cst,
        quant: SyntaxKind,
    ) -> Result<RuleParserItem, LoweringError> {
        let combinator = match quant {
            SyntaxKind::RuleQuantStar => "many",
            SyntaxKind::RuleQuantPlus => "some",
            SyntaxKind::RuleQuantOpt => "optional",
            SyntaxKind::RuleQuantStarLazy | SyntaxKind::RuleQuantPlusLazy => {
                return Err(LoweringError::UnsupportedSyntax { kind: quant });
            }
            _ => {
                return Err(LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::RuleQuant,
                });
            }
        };
        let base = self.lower_rule_quant_base(node)?;
        let combinator = self.std_parse_ref(combinator)?;
        Ok(RuleParserItem {
            parser: self.make_app(combinator, base.parser),
            semantic: if base.semantic == RuleSemantic::Unit {
                RuleSemantic::Unit
            } else {
                RuleSemantic::Value
            },
        })
    }

    fn lower_rule_quant_base(&mut self, node: &Cst) -> Result<RuleParserItem, LoweringError> {
        if let Some(text) = plain_string_expr_text(node)? {
            return Ok(RuleParserItem {
                parser: self.rule_token_parser(text)?,
                semantic: RuleSemantic::Unit,
            });
        }
        if let Some(paren) = direct_child(node, SyntaxKind::Paren) {
            let body = self.lower_rule_container_body(&paren)?;
            return Ok(RuleParserItem {
                parser: self.thunk_computation(body.expr),
                semantic: body.semantic,
            });
        }
        Ok(RuleParserItem {
            parser: self.lower_expr_chain_prefix_with_pipe_arg_until(
                node,
                LambdaScope::Anonymous,
                false,
                None,
                Some(SyntaxKind::RuleQuant),
            )?,
            semantic: RuleSemantic::Value,
        })
    }

    fn rule_token_parser(&mut self, text: String) -> Result<Computation, LoweringError> {
        let token = self.std_parse_ref("token")?;
        let expected = self.string_value(text);
        Ok(self.make_app(token, expected))
    }

    fn rule_word_parser(&mut self) -> Result<Computation, LoweringError> {
        self.std_parse_ref("word")
    }

    fn run_rule_parser(&mut self, parser: Computation) -> Computation {
        let unit = self.unit_expr();
        self.make_app(parser, unit)
    }

    fn std_parse_ref(&mut self, name: &str) -> Result<Computation, LoweringError> {
        self.lower_std_value_ref(crate::std_paths::text_parse_value(name))
    }

    fn bind_rule_capture(
        &mut self,
        name: Name,
        value: Computation,
    ) -> (LoweredLocalStmt, Computation) {
        let pat = self.bind_pattern_local(
            name.clone(),
            value.value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let local = self
            .locals
            .last()
            .cloned()
            .expect("rule capture should be the last local");
        let captured = self.lower_local_name(name, local);
        (
            LoweredLocalStmt {
                stmt: Stmt::Let(Vis::My, pat, value.expr),
                effect: value.effect,
            },
            captured,
        )
    }

    fn rule_record_expr(&mut self, fields: Vec<(Name, Computation)>) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_exact_pure_effect();
        let record_fields = fields
            .iter()
            .map(|(name, value)| RecordField {
                name: name.0.clone(),
                value: self.alloc_pos(Pos::Var(value.value)),
                optional: false,
            })
            .collect::<Vec<_>>();
        for (_, value) in &fields {
            self.subtype_var_to_var(value.effect, result_effect);
        }
        self.constrain_lower(result_value, Pos::Record(record_fields));

        let expr_fields = fields
            .into_iter()
            .map(|(name, value)| (name.0, value.expr))
            .collect();
        let expr = self.session.poly.add_expr(Expr::Record {
            fields: expr_fields,
            spread: RecordSpread::None,
        });
        Computation::value(expr, result_value, result_effect)
    }

    fn rule_block_expr(&mut self, stmts: Vec<LoweredLocalStmt>, tail: Computation) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_type_var();
        let mut ir_stmts = Vec::with_capacity(stmts.len());
        for stmt in stmts {
            self.subtype_var_to_var(stmt.effect, effect);
            ir_stmts.push(stmt.stmt);
        }
        self.subtype_var_to_var(tail.effect, effect);
        self.subtype_var_to_var(tail.value, value);
        let expr = self
            .session
            .poly
            .add_expr(Expr::Block(ir_stmts, Some(tail.expr)));
        Computation::computation(expr, value, effect)
    }

    fn lower_record_literal(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let fields = record_literal_fields(node);
        let mut lowered = Vec::with_capacity(fields.len());
        for field in fields {
            let name = record_field_name(&field).ok_or(LoweringError::MissingRecordFieldName)?;
            let value_node =
                record_field_value(&field).ok_or(LoweringError::MissingRecordFieldValue)?;
            let value = self.lower_expr(&value_node)?;
            lowered.push((name, value));
        }

        let result_value = self.fresh_type_var();
        let expansive = lowered.iter().any(|(_, value)| value.is_expansive());
        let result_effect = if expansive {
            self.fresh_type_var()
        } else {
            self.fresh_exact_pure_effect()
        };
        let record_fields = lowered
            .iter()
            .map(|(name, value)| RecordField {
                name: name.0.clone(),
                value: self.alloc_pos(Pos::Var(value.value)),
                optional: false,
            })
            .collect::<Vec<_>>();
        for (_, value) in &lowered {
            self.subtype_var_to_var(value.effect, result_effect);
        }
        self.constrain_lower(result_value, Pos::Record(record_fields));

        let expr_fields = lowered
            .into_iter()
            .map(|(name, value)| (name.0, value.expr))
            .collect();
        let expr = self.session.poly.add_expr(Expr::Record {
            fields: expr_fields,
            spread: RecordSpread::None,
        });
        Ok(Computation::new(
            expr,
            result_value,
            result_effect,
            if expansive {
                Evaluation::Computation
            } else {
                Evaluation::Value
            },
        ))
    }

    fn lower_path_name(&mut self, path: &[Name]) -> Result<Computation, LoweringError> {
        if let Some(builtin) = builtin_op_from_path(path) {
            return self.lower_builtin_op(builtin);
        }

        let Some(target) = self.modules.value_path_at(self.module, path, self.site) else {
            return Err(LoweringError::UnresolvedName {
                name: Name(path_label(path)),
            });
        };
        Ok(self.lower_resolved_value_ref(path_label(path), target))
    }

    fn lower_std_value_ref(&mut self, path: Vec<String>) -> Result<Computation, LoweringError> {
        let path = path.into_iter().map(Name).collect::<Vec<_>>();
        let Some(target) =
            self.modules
                .value_path_at(self.modules.root_id(), &path, module_path_lookup_site())
        else {
            return Err(LoweringError::UnresolvedName {
                name: Name(path_label(&path)),
            });
        };
        Ok(self.lower_resolved_value_ref(path_label(&path), target))
    }

    fn lower_builtin_op(&mut self, builtin: BuiltinOp) -> Result<Computation, LoweringError> {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_builtin_op_sig(value, builtin.sig)?;
        let expr = self.session.poly.add_expr(Expr::PrimitiveOp(builtin.op));
        Ok(Computation::value(expr, value, effect))
    }

    fn constrain_builtin_op_sig(
        &mut self,
        value: TypeVar,
        sig: BuiltinOpSig,
    ) -> Result<(), LoweringError> {
        if let BuiltinOpSig::Poly { params, ret } = sig {
            return self.constrain_poly_op_sig(value, params, ret);
        }
        let lower = self.builtin_op_pos_sig(sig)?;
        let upper = self.builtin_op_neg_sig(sig)?;
        self.constrain_lower(value, lower);
        self.constrain_upper(value, upper);
        Ok(())
    }

    /// 多相 builtin の signature。量化変数（番号）ごとに型変数を1つ作り、上下界で共有する。
    fn constrain_poly_op_sig(
        &mut self,
        value: TypeVar,
        params: &[SigTy],
        ret: SigTy,
    ) -> Result<(), LoweringError> {
        let mut vars = FxHashMap::default();
        let lower = self.curried_poly_pos(&mut vars, params, ret)?;
        let upper = self.curried_poly_neg(&mut vars, params, ret)?;
        self.constrain_lower(value, lower);
        self.constrain_upper(value, upper);
        Ok(())
    }

    fn poly_sig_var(&mut self, vars: &mut FxHashMap<u8, TypeVar>, index: u8) -> TypeVar {
        if let Some(var) = vars.get(&index) {
            return *var;
        }
        let var = self.fresh_type_var();
        vars.insert(index, var);
        var
    }

    fn curried_poly_pos(
        &mut self,
        vars: &mut FxHashMap<u8, TypeVar>,
        params: &[SigTy],
        ret: SigTy,
    ) -> Result<Pos, LoweringError> {
        let Some((param, rest)) = params.split_first() else {
            return self.poly_sig_pos(ret, vars);
        };
        let arg = self.poly_sig_neg(*param, vars)?;
        let arg = self.alloc_neg(arg);
        let arg_eff = self.never_neg();
        let ret_eff = self.alloc_pos(Pos::Bot);
        let ret = self.curried_poly_pos(vars, rest, ret)?;
        let ret = self.alloc_pos(ret);
        Ok(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn curried_poly_neg(
        &mut self,
        vars: &mut FxHashMap<u8, TypeVar>,
        params: &[SigTy],
        ret: SigTy,
    ) -> Result<Neg, LoweringError> {
        let Some((param, rest)) = params.split_first() else {
            return self.poly_sig_neg(ret, vars);
        };
        let arg = self.poly_sig_pos(*param, vars)?;
        let arg = self.alloc_pos(arg);
        let arg_eff = self.alloc_pos(Pos::Bot);
        let ret_eff = self.never_neg();
        let ret = self.curried_poly_neg(vars, rest, ret)?;
        let ret = self.alloc_neg(ret);
        Ok(Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn poly_sig_pos(
        &mut self,
        ty: SigTy,
        vars: &mut FxHashMap<u8, TypeVar>,
    ) -> Result<Pos, LoweringError> {
        match ty {
            SigTy::Var(index) => Ok(Pos::Var(self.poly_sig_var(vars, index))),
            // 引数なしの Con は builtin（never 等）の特殊形も含むので既存の解決に乗せる。
            SigTy::Con(name, []) => self.builtin_op_pos_type(name),
            SigTy::Con(name, args) => {
                let path = self.builtin_op_con_path(name)?;
                let args = args
                    .iter()
                    .map(|arg| self.poly_sig_neu(*arg, vars))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Pos::Con(path, args))
            }
        }
    }

    fn poly_sig_neg(
        &mut self,
        ty: SigTy,
        vars: &mut FxHashMap<u8, TypeVar>,
    ) -> Result<Neg, LoweringError> {
        match ty {
            SigTy::Var(index) => Ok(Neg::Var(self.poly_sig_var(vars, index))),
            SigTy::Con(name, []) => self.builtin_op_neg_type(name),
            SigTy::Con(name, args) => {
                let path = self.builtin_op_con_path(name)?;
                let args = args
                    .iter()
                    .map(|arg| self.poly_sig_neu(*arg, vars))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Neg::Con(path, args))
            }
        }
    }

    fn poly_sig_neu(
        &mut self,
        ty: SigTy,
        vars: &mut FxHashMap<u8, TypeVar>,
    ) -> Result<poly::types::NeuId, LoweringError> {
        match ty {
            SigTy::Var(index) => {
                let var = self.poly_sig_var(vars, index);
                Ok(self.invariant_var_arg(var))
            }
            SigTy::Con(name, args) => {
                let path = self.builtin_op_con_path(name)?;
                let args = args
                    .iter()
                    .map(|arg| self.poly_sig_neu(*arg, vars))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.session.infer.alloc_neu(Neu::Con(path, args)))
            }
        }
    }

    fn builtin_op_pos_sig(&mut self, sig: BuiltinOpSig) -> Result<Pos, LoweringError> {
        match sig {
            BuiltinOpSig::Nullary { ret } => self.builtin_op_pos_type(ret),
            BuiltinOpSig::Unary { param, ret } => self.curried_pos_fun(&[param], ret),
            BuiltinOpSig::Binary { param, ret } => self.curried_pos_fun(&[param, param], ret),
            BuiltinOpSig::BinaryPredicate { param } => {
                self.curried_pos_fun(&[param, param], "bool")
            }
            BuiltinOpSig::Mixed { params, ret } => self.curried_pos_fun(params, ret),
            BuiltinOpSig::BytesToUtf8Raw => {
                let ret = Pos::Tuple(vec![
                    self.alloc_pos(self.builtin_op_pos_type("str")?),
                    self.alloc_pos(self.builtin_op_pos_type("int")?),
                ]);
                self.curried_pos_fun_with_ret(&["bytes"], ret)
            }
            // Poly は constrain_builtin_op_sig が先に取る。
            BuiltinOpSig::Poly { .. } => unreachable!("poly sigs are constrained directly"),
        }
    }

    fn builtin_op_neg_sig(&mut self, sig: BuiltinOpSig) -> Result<Neg, LoweringError> {
        match sig {
            BuiltinOpSig::Nullary { ret } => self.builtin_op_neg_type(ret),
            BuiltinOpSig::Unary { param, ret } => self.curried_neg_fun(&[param], ret),
            BuiltinOpSig::Binary { param, ret } => self.curried_neg_fun(&[param, param], ret),
            BuiltinOpSig::BinaryPredicate { param } => {
                self.curried_neg_fun(&[param, param], "bool")
            }
            BuiltinOpSig::Mixed { params, ret } => self.curried_neg_fun(params, ret),
            BuiltinOpSig::BytesToUtf8Raw => {
                let ret = Neg::Tuple(vec![
                    self.alloc_neg(self.builtin_op_neg_type("str")?),
                    self.alloc_neg(self.builtin_op_neg_type("int")?),
                ]);
                self.curried_neg_fun_with_ret(&["bytes"], ret)
            }
            // Poly は constrain_builtin_op_sig が先に取る。
            BuiltinOpSig::Poly { .. } => unreachable!("poly sigs are constrained directly"),
        }
    }

    fn curried_pos_fun(
        &mut self,
        params: &[&'static str],
        ret: &'static str,
    ) -> Result<Pos, LoweringError> {
        let ret = self.builtin_op_pos_type(ret)?;
        self.curried_pos_fun_with_ret(params, ret)
    }

    fn curried_pos_fun_with_ret(
        &mut self,
        params: &[&'static str],
        ret: Pos,
    ) -> Result<Pos, LoweringError> {
        let Some((param, rest)) = params.split_first() else {
            return Ok(ret);
        };
        let arg = self.builtin_op_neg_type(param)?;
        let arg = self.alloc_neg(arg);
        let arg_eff = self.never_neg();
        let ret_eff = self.alloc_pos(Pos::Bot);
        let ret = self.curried_pos_fun_with_ret(rest, ret)?;
        let ret = self.alloc_pos(ret);
        Ok(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn curried_neg_fun(
        &mut self,
        params: &[&'static str],
        ret: &'static str,
    ) -> Result<Neg, LoweringError> {
        let ret = self.builtin_op_neg_type(ret)?;
        self.curried_neg_fun_with_ret(params, ret)
    }

    fn curried_neg_fun_with_ret(
        &mut self,
        params: &[&'static str],
        ret: Neg,
    ) -> Result<Neg, LoweringError> {
        let Some((param, rest)) = params.split_first() else {
            return Ok(ret);
        };
        let arg = self.builtin_op_pos_type(param)?;
        let arg = self.alloc_pos(arg);
        let arg_eff = self.alloc_pos(Pos::Bot);
        let ret_eff = self.never_neg();
        let ret = self.curried_neg_fun_with_ret(rest, ret)?;
        let ret = self.alloc_neg(ret);
        Ok(Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn builtin_op_pos_type(&self, name: &'static str) -> Result<Pos, LoweringError> {
        let path = self.builtin_op_type_path(name)?;
        Ok(match path {
            BuiltinOpTypePath::Builtin(BuiltinType::Never) => Pos::Bot,
            BuiltinOpTypePath::Builtin(builtin) => {
                Pos::Con(vec![builtin.surface_name().to_string()], Vec::new())
            }
            BuiltinOpTypePath::Named(path) => Pos::Con(path, Vec::new()),
        })
    }

    fn builtin_op_neg_type(&self, name: &'static str) -> Result<Neg, LoweringError> {
        let path = self.builtin_op_type_path(name)?;
        Ok(match path {
            BuiltinOpTypePath::Builtin(BuiltinType::Never) => Neg::Bot,
            BuiltinOpTypePath::Builtin(builtin) => {
                Neg::Con(vec![builtin.surface_name().to_string()], Vec::new())
            }
            BuiltinOpTypePath::Named(path) => Neg::Con(path, Vec::new()),
        })
    }

    /// 型名を lexical 解決して Con path にする。type 引数付き Con を手で組むとき用。
    fn builtin_op_con_path(&self, name: &'static str) -> Result<Vec<String>, LoweringError> {
        Ok(match self.builtin_op_type_path(name)? {
            BuiltinOpTypePath::Builtin(builtin) => vec![builtin.surface_name().to_string()],
            BuiltinOpTypePath::Named(path) => path,
        })
    }

    fn builtin_op_type_path(&self, name: &'static str) -> Result<BuiltinOpTypePath, LoweringError> {
        if let Some(builtin) = BuiltinType::from_surface_name(name) {
            return Ok(BuiltinOpTypePath::Builtin(builtin));
        }
        let name = Name(name.to_string());
        let Some(decl) = self.modules.lexical_type_at(self.module, &name, self.site) else {
            return Err(LoweringError::AnnotationBuild {
                error: AnnBuildError::UnresolvedTypeName { path: vec![name] },
            });
        };
        Ok(BuiltinOpTypePath::Named(
            self.modules
                .type_decl_path(&decl)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect(),
        ))
    }

    fn lower_name(&mut self, name: Name) -> Result<Computation, LoweringError> {
        if let Some(local) = self.local_binding(&name) {
            return Ok(self.lower_local_name(name, local));
        }

        match name.0.as_str() {
            "true" => return Ok(self.lower_bool(true)),
            "false" => return Ok(self.lower_bool(false)),
            _ => {}
        }

        let Some(target) = self.modules.lexical_value_at(self.module, &name, self.site) else {
            return Err(LoweringError::UnresolvedName { name });
        };
        let label = name.0.clone();
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let reference = self.session.poly.add_ref();
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, label);
        }
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value,
            },
        );
        self.known_ref_targets.insert(reference, target);
        self.session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: reference,
            target,
        });

        let expr = self.session.poly.add_expr(Expr::Var(reference));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_sigil_name(&mut self, text: &str) -> Result<Computation, LoweringError> {
        let Some(reference_name) = var_read_reference_name(text) else {
            return self.lower_name(Name(text.to_string()));
        };
        let reference = self.lower_name(reference_name)?;
        let get = self.lower_synthetic_selection(reference, "get".to_string());
        let unit = self.unit_expr();
        Ok(self.make_app(get, unit))
    }

    fn lower_local_name(&mut self, name: Name, local: LocalBinding) -> Computation {
        let (effect, effect_view) = self.local_effect_slot(local.effect.clone());
        let value = self.instantiate_local_value(&local);
        let reference = self.session.poly.add_ref();
        self.session.poly.resolve_ref(reference, local.def);
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, name.0);
        }
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Var(reference));
        let computation = Computation::value(expr, value, effect);
        match effect_view {
            Some(view) => computation.with_effect_view(view),
            None => computation,
        }
    }

    fn local_effect_slot(
        &mut self,
        effect: Option<LocalEffect>,
    ) -> (TypeVar, Option<EffectViewId>) {
        match effect {
            Some(LocalEffect::Var(effect)) => (effect, None),
            Some(effect @ LocalEffect::Stack { inner, .. }) => {
                let view = self.add_effect_view(effect);
                (inner, Some(view))
            }
            None => (self.fresh_exact_pure_effect(), None),
        }
    }

    fn add_effect_view(&mut self, effect: LocalEffect) -> EffectViewId {
        let id = EffectViewId(self.effect_views.len() as u32);
        self.effect_views.push(effect);
        id
    }

    fn effect_view(&self, id: EffectViewId) -> &LocalEffect {
        &self.effect_views[id.0 as usize]
    }

    fn subtype_var_to_local_effect(&mut self, source: TypeVar, target: &LocalEffect) {
        match target {
            LocalEffect::Var(target) => self.subtype_var_to_var(source, *target),
            LocalEffect::Stack { inner, weight } => {
                let lower = self.alloc_pos(Pos::Var(source));
                let inner = self.alloc_neg(Neg::Var(*inner));
                let upper = self.alloc_neg(Neg::Stack {
                    inner,
                    weight: weight.clone(),
                });
                self.session.infer.subtype(lower, upper);
            }
        }
    }

    fn local_binding(&self, name: &Name) -> Option<LocalBinding> {
        self.locals
            .iter()
            .rev()
            .find(|local| &local.name == name)
            .cloned()
    }

    fn lower_tail_node(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::ApplyML | SyntaxKind::ApplyC | SyntaxKind::ApplyColon => {
                self.apply_arguments(acc, node)
            }
            SyntaxKind::Field => self.lower_field_selection(acc, node),
            SyntaxKind::Index => self.lower_index_selection(acc, node),
            SyntaxKind::Assign => self.lower_ref_assignment(acc, node),
            SyntaxKind::InfixNode => self.lower_infix_op_use(acc, node),
            SyntaxKind::SuffixNode => self.lower_suffix_op_use(acc, node),
            SyntaxKind::PipeNode => self.lower_pipe_node(acc, node),
            SyntaxKind::TypeAnn => self.lower_type_annotation_tail(acc, node),
            kind => Err(LoweringError::UnsupportedSyntax { kind }),
        }
    }

    fn lower_pipe_node(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let rhs = node
            .children()
            .find(|child| child.kind() == SyntaxKind::Expr)
            .ok_or(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::PipeNode,
            })?;
        let pipe_arg = Some(PipeArg { expr: acc });
        if let Some(with_block) = rhs
            .children()
            .find(|child| child.kind() == SyntaxKind::WithBlock)
        {
            return self.lower_with_expr_chain(&rhs, &with_block, LambdaScope::Anonymous, pipe_arg);
        }
        self.lower_expr_chain_prefix_with_pipe_arg(&rhs, LambdaScope::Anonymous, false, pipe_arg)
    }

    fn lower_type_annotation_tail(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let type_expr = node
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeExpr)
            .ok_or(LoweringError::AnnotationBuild {
                error: AnnBuildError::ExpectedTypeExpr { kind: node.kind() },
            })?;
        let mut builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
        );
        let ann = builder
            .build_type_expr(&type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        AnnConstraintLowerer::new(&mut self.session.infer, self.modules)
            .connect_computation(
                AnnComputationTarget {
                    value: acc.value,
                    effect: acc.effect,
                },
                &ann,
            )
            .map(|_| acc)
            .map_err(|error| LoweringError::AnnotationConstraint { error })
    }

    fn apply_arguments(
        &mut self,
        mut callee: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let args = self.apply_argument_exprs(callee, node);
        if args.is_empty() {
            let unit = self.unit_expr();
            return Ok(self.make_app(callee, unit));
        }
        for arg in args {
            let lowered_arg = self.lower_expr(&arg)?;
            callee = self.make_app(callee, lowered_arg);
        }
        Ok(callee)
    }

    fn apply_argument_exprs(&self, callee: Computation, node: &Cst) -> Vec<Cst> {
        let args = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .collect::<Vec<_>>();
        let Some(arity) = self.declared_constructor_payload_arity(callee) else {
            return args;
        };
        declared_constructor_expr_payloads(args, arity)
    }

    fn declared_constructor_payload_arity(&self, callee: Computation) -> Option<usize> {
        let Expr::Var(reference) = self.session.poly.expr(callee.expr) else {
            return None;
        };
        let target = self
            .known_ref_targets
            .get(reference)
            .copied()
            .or_else(|| self.session.poly.ref_target(*reference))?;
        let constructor = self.modules.constructor_by_def(target)?;
        Some(constructor_payload_arity(&constructor.payload))
    }

    fn lower_field_selection(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let name = field_name(node).ok_or(LoweringError::MissingFieldName)?;
        Ok(self.lower_synthetic_selection(receiver, name))
    }

    fn lower_index_selection(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let arg_node = index_expr(node).ok_or(LoweringError::MissingIndexArgument)?;
        let index = self.lower_expr(&arg_node)?;
        let selection = self.lower_synthetic_selection(receiver, "index".to_string());
        Ok(self.make_app(selection, index))
    }

    fn lower_ref_assignment(
        &mut self,
        reference: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let value = match assignment_value_expr(node) {
            Some(expr) => self.lower_expr(&expr)?,
            None => self.unit_expr(),
        };
        Ok(self.make_ref_set(reference, value))
    }

    fn make_ref_set(&mut self, reference: Computation, value: Computation) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let ref_effect = self.fresh_type_var();
        let expected_value = self.fresh_type_var();

        self.constrain_exact_primitive(result_value, "unit");
        self.subtype_var_to_var(reference.effect, result_effect);
        self.subtype_var_to_var(value.effect, result_effect);
        self.subtype_var_to_var(ref_effect, result_effect);
        self.subtype_var_to_var(value.value, expected_value);

        let effect_arg = self.invariant_var_arg(ref_effect);
        let value_arg = self.invariant_var_arg(expected_value);
        let args = vec![effect_arg, value_arg];
        self.constrain_lower(
            reference.value,
            Pos::Con(crate::std_paths::control_var_ref_type(), args.clone()),
        );
        self.constrain_upper(
            reference.value,
            Neg::Con(crate::std_paths::control_var_ref_type(), args),
        );

        let expr = self
            .session
            .poly
            .add_expr(Expr::RefSet(reference.expr, value.expr));
        Computation::computation(expr, result_value, result_effect)
    }

    fn lower_synthetic_selection(&mut self, receiver: Computation, name: String) -> Computation {
        let method_value = self.fresh_type_var();
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let call_effect = self.fresh_type_var();
        let method = self.alloc_pos(Pos::Var(method_value));
        let receiver_value = self.alloc_pos(Pos::Var(receiver.value));
        let receiver_effect = self.alloc_pos(Pos::Var(receiver.effect));
        let ret_eff = self.alloc_neg(Neg::Var(call_effect));
        let ret = self.alloc_neg(Neg::Var(result_value));
        let method_upper = self.alloc_neg(Neg::Fun {
            arg: receiver_value,
            arg_eff: receiver_effect,
            ret_eff,
            ret,
        });
        self.session.infer.subtype(method, method_upper);
        self.subtype_var_to_var(receiver.effect, result_effect);
        self.subtype_var_to_var(call_effect, result_effect);

        let select = self.session.poly.add_select(name);
        self.session.register_selection_use(
            select,
            SelectionUse {
                parent: self.parent,
                method_value,
                receiver_value: receiver.value,
                local_method_scope: self.local_method_scope,
            },
        );
        let expr = self
            .session
            .poly
            .add_expr(Expr::Select(receiver.expr, select));
        Computation::new(expr, result_value, result_effect, receiver.evaluation)
    }

    /// `[a, b, ...]` を empty / singleton / merge の list primitive で組む。
    /// 要素型は literal 全体で1つの型変数を共有する。
    fn lower_list_literal(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let mut items = Vec::new();
        for child in node.children() {
            match child.kind() {
                SyntaxKind::Expr => items.push(ListLiteralItem::Single(child)),
                SyntaxKind::ExprSpread => {
                    let expr = child
                        .children()
                        .find(|child| child.kind() == SyntaxKind::Expr)
                        .ok_or(LoweringError::UnsupportedSyntax {
                            kind: SyntaxKind::ExprSpread,
                        })?;
                    items.push(ListLiteralItem::Spread(expr));
                }
                _ => {}
            }
        }
        let item = self.fresh_type_var();
        let list_path = self.builtin_op_con_path("list")?;
        self.build_list_literal(item, &list_path, &items)
    }

    fn build_list_literal(
        &mut self,
        item: TypeVar,
        list_path: &[String],
        items: &[ListLiteralItem],
    ) -> Result<Computation, LoweringError> {
        if items.is_empty() {
            let empty = self.list_empty_callee(item, list_path);
            let unit = self.unit_expr();
            return Ok(self.make_app(empty, unit));
        }
        if let [single] = items {
            return self.lower_list_literal_part(item, list_path, single);
        }
        let mid = items.len() / 2;
        let left = self.build_list_literal(item, list_path, &items[..mid])?;
        let right = self.build_list_literal(item, list_path, &items[mid..])?;
        let merge = self.list_merge_callee(item, list_path);
        let applied = self.make_app(merge, left);
        Ok(self.make_app(applied, right))
    }

    fn lower_list_literal_part(
        &mut self,
        item: TypeVar,
        list_path: &[String],
        part: &ListLiteralItem,
    ) -> Result<Computation, LoweringError> {
        match part {
            ListLiteralItem::Single(node) => {
                let value = self.lower_expr(node)?;
                let singleton = self.list_singleton_callee(value.value, list_path);
                Ok(self.make_app(singleton, value))
            }
            ListLiteralItem::Spread(node) => {
                let value = self.lower_expr(node)?;
                self.constrain_list_value(value.value, item, list_path);
                Ok(value)
            }
        }
    }

    fn list_empty_callee(&mut self, item: TypeVar, list_path: &[String]) -> Computation {
        // () -> list 'i
        let pos = {
            let arg = self.alloc_neg(primitive_neg_type("unit"));
            let arg_eff = self.never_neg();
            let ret_eff = self.alloc_pos(Pos::Bot);
            let ret = self.list_con_pos(item, list_path);
            let ret = self.alloc_pos(ret);
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            }
        };
        let neg = {
            let arg = self.alloc_pos(primitive_type("unit"));
            let arg_eff = self.alloc_pos(Pos::Bot);
            let ret_eff = self.never_neg();
            let ret = self.list_con_neg(item, list_path);
            let ret = self.alloc_neg(ret);
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            }
        };
        self.list_primitive_callee(PrimitiveOp::ListEmpty, pos, neg)
    }

    fn list_singleton_callee(&mut self, item: TypeVar, list_path: &[String]) -> Computation {
        // 'i -> list 'i
        let pos = {
            let arg = self.alloc_neg(Neg::Var(item));
            let arg_eff = self.never_neg();
            let ret_eff = self.alloc_pos(Pos::Bot);
            let ret = self.list_con_pos(item, list_path);
            let ret = self.alloc_pos(ret);
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            }
        };
        let neg = {
            let arg = self.alloc_pos(Pos::Var(item));
            let arg_eff = self.alloc_pos(Pos::Bot);
            let ret_eff = self.never_neg();
            let ret = self.list_con_neg(item, list_path);
            let ret = self.alloc_neg(ret);
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            }
        };
        self.list_primitive_callee(PrimitiveOp::ListSingleton, pos, neg)
    }

    fn list_merge_callee(&mut self, item: TypeVar, list_path: &[String]) -> Computation {
        // list 'i -> list 'i -> list 'i
        let pos = {
            let ret = self.list_con_pos(item, list_path);
            let ret = self.alloc_pos(ret);
            let inner_arg = self.list_con_neg(item, list_path);
            let inner_arg = self.alloc_neg(inner_arg);
            let inner_arg_eff = self.never_neg();
            let inner_ret_eff = self.alloc_pos(Pos::Bot);
            let inner = Pos::Fun {
                arg: inner_arg,
                arg_eff: inner_arg_eff,
                ret_eff: inner_ret_eff,
                ret,
            };
            let inner = self.alloc_pos(inner);
            let arg = self.list_con_neg(item, list_path);
            let arg = self.alloc_neg(arg);
            let arg_eff = self.never_neg();
            let ret_eff = self.alloc_pos(Pos::Bot);
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret: inner,
            }
        };
        let neg = {
            let ret = self.list_con_neg(item, list_path);
            let ret = self.alloc_neg(ret);
            let inner_arg = self.list_con_pos(item, list_path);
            let inner_arg = self.alloc_pos(inner_arg);
            let inner_arg_eff = self.alloc_pos(Pos::Bot);
            let inner_ret_eff = self.never_neg();
            let inner = Neg::Fun {
                arg: inner_arg,
                arg_eff: inner_arg_eff,
                ret_eff: inner_ret_eff,
                ret,
            };
            let inner = self.alloc_neg(inner);
            let arg = self.list_con_pos(item, list_path);
            let arg = self.alloc_pos(arg);
            let arg_eff = self.alloc_pos(Pos::Bot);
            let ret_eff = self.never_neg();
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret: inner,
            }
        };
        self.list_primitive_callee(PrimitiveOp::ListMerge, pos, neg)
    }

    fn list_con_pos(&mut self, item: TypeVar, list_path: &[String]) -> Pos {
        let arg = self.invariant_var_arg(item);
        Pos::Con(list_path.to_vec(), vec![arg])
    }

    fn list_con_neg(&mut self, item: TypeVar, list_path: &[String]) -> Neg {
        let arg = self.invariant_var_arg(item);
        Neg::Con(list_path.to_vec(), vec![arg])
    }

    fn constrain_list_value(&mut self, value: TypeVar, item: TypeVar, list_path: &[String]) {
        let lower = self.list_con_pos(item, list_path);
        self.constrain_lower(value, lower);
        let upper = self.list_con_neg(item, list_path);
        self.constrain_upper(value, upper);
    }

    fn list_primitive_callee(&mut self, op: PrimitiveOp, lower: Pos, upper: Neg) -> Computation {
        let value = self.fresh_type_var();
        self.constrain_lower(value, lower);
        self.constrain_upper(value, upper);
        let effect = self.fresh_exact_pure_effect();
        let expr = self.session.poly.add_expr(Expr::PrimitiveOp(op));
        Computation::value(expr, value, effect)
    }

    /// op 使用ノードから symbol を読んで mangled 名で解決する。戻りは (op 参照, lazy)。
    fn resolve_op_use(
        &mut self,
        fixity: &'static str,
        node: &Cst,
    ) -> Result<(Computation, bool), LoweringError> {
        let symbol = node
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .find_map(|item| item.into_token())
            .map(|tok| tok.text().to_string())
            .ok_or(LoweringError::MissingOpName)?;
        self.resolve_op_symbol(fixity, &symbol)
    }

    fn resolve_op_symbol(
        &mut self,
        fixity: &'static str,
        symbol: &str,
    ) -> Result<(Computation, bool), LoweringError> {
        let name = crate::op_value_name(fixity, symbol);
        let Some(target) = self.modules.lexical_value_at(self.module, &name, self.site) else {
            return Err(LoweringError::UnresolvedName { name });
        };
        let lazy = self.modules.is_lazy_op(target);
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let reference = self.session.poly.add_ref();
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, name.0);
        }
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value,
            },
        );
        self.known_ref_targets.insert(reference, target);
        self.session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: reference,
            target,
        });
        let expr = self.session.poly.add_expr(Expr::Var(reference));
        Ok((Computation::value(expr, value, effect), lazy))
    }

    fn lower_infix_op_use(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let (op, lazy) = self.resolve_op_use("infix", node)?;
        let rhs_node = node
            .children()
            .find(|child| child.kind() == SyntaxKind::Expr)
            .ok_or(LoweringError::MissingOpOperand)?;
        let rhs = self.lower_expr(&rhs_node)?;
        let (lhs, rhs) = if lazy {
            (self.thunk_computation(acc), self.thunk_computation(rhs))
        } else {
            (acc, rhs)
        };
        let applied = self.make_app(op, lhs);
        Ok(self.make_app(applied, rhs))
    }

    fn lower_suffix_op_use(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let (op, lazy) = self.resolve_op_use("suffix", node)?;
        let arg = if lazy {
            self.thunk_computation(acc)
        } else {
            acc
        };
        Ok(self.make_app(op, arg))
    }

    fn lower_prefix_op_use(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let (op, lazy) = self.resolve_op_use("prefix", node)?;
        let operand_node = node
            .children()
            .find(|child| child.kind() == SyntaxKind::Expr)
            .ok_or(LoweringError::MissingOpOperand)?;
        let operand = self.lower_expr(&operand_node)?;
        let arg = if lazy {
            self.thunk_computation(operand)
        } else {
            operand
        };
        Ok(self.make_app(op, arg))
    }

    fn lower_nullfix_op_use(&mut self, symbol: &str) -> Result<Computation, LoweringError> {
        let (op, _lazy) = self.resolve_op_symbol("nullfix", symbol)?;
        let unit = self.unit_expr();
        Ok(self.make_app(op, unit))
    }

    /// `\() -> body` の thunk。lazy op の被演算子と nullfix op の本体に使う。
    fn thunk_computation(&mut self, body: Computation) -> Computation {
        let pat = self.session.poly.add_pat(Pat::Lit(Lit::Unit));
        let param = self.fresh_type_var();
        self.constrain_exact_primitive(param, "unit");
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(param));
        let arg_eff = self.never_neg();
        let ret_eff = self.alloc_pos(Pos::Var(body.effect));
        let ret = self.alloc_pos(Pos::Var(body.value));
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Computation::value(expr, value, effect)
    }

    fn make_app(&mut self, callee: Computation, arg: Computation) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let call_effect = self.fresh_type_var();

        let arg_value = self.alloc_pos(Pos::Var(arg.value));
        let arg_effect = self.alloc_pos(Pos::Var(arg.effect));
        let return_effect = self.unannotated_local_callee_return_effect(&callee, call_effect);
        let return_value = self.alloc_neg(Neg::Var(result_value));
        let callee_upper = self.alloc_neg(Neg::Fun {
            arg: arg_value,
            arg_eff: arg_effect,
            ret_eff: return_effect.upper,
            ret: return_value,
        });
        self.subtype(Pos::Var(callee.value), callee_upper);
        self.subtype_var_to_var(callee.effect, result_effect);
        self.subtype_pos_to_var(return_effect.lower, result_effect);

        let expr = self.session.poly.add_expr(Expr::App(callee.expr, arg.expr));
        Computation::computation(expr, result_value, result_effect)
    }

    fn unit_expr(&mut self) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(value, primitive_type("unit"));
        let expr = self.session.poly.add_expr(Expr::Lit(Lit::Unit));
        Computation::value(expr, value, effect)
    }

    fn fresh_type_var(&mut self) -> TypeVar {
        self.session.infer.fresh_type_var()
    }

    fn unannotated_local_callee_return_effect(
        &mut self,
        callee: &Computation,
        call_effect: TypeVar,
    ) -> ApplicationReturnEffect {
        let bare = self.alloc_neg(Neg::Var(call_effect));
        let lower = self.alloc_pos(Pos::Var(call_effect));
        if !self
            .function_frames
            .last()
            .is_some_and(|frame| frame.scope == LambdaScope::Defined)
        {
            return ApplicationReturnEffect { upper: bare, lower };
        }
        let Some(def) = self.local_callee_def(callee) else {
            return ApplicationReturnEffect { upper: bare, lower };
        };
        let Some(local) = self.local_binding_by_def(def) else {
            return ApplicationReturnEffect { upper: bare, lower };
        };
        if !matches!(self.session.poly.defs.get(local.def), Some(Def::Arg)) {
            return ApplicationReturnEffect { upper: bare, lower };
        }
        if local.call_return_effect != LocalCallReturnEffect::Unannotated {
            return ApplicationReturnEffect { upper: bare, lower };
        }

        let subtract = self.session.infer.fresh_subtract_id();
        let frame = self
            .function_frames
            .last_mut()
            .expect("checked that function frame exists");
        frame.subtracts.push(subtract);
        let weight = StackWeight::push(subtract, Subtractability::Empty);
        let effect_pos = self.alloc_pos(Pos::Var(call_effect));
        let lower = self.alloc_pos(Pos::Stack {
            inner: effect_pos,
            weight: weight.clone(),
        });
        let upper = self.alloc_neg(Neg::Stack {
            inner: bare,
            weight,
        });
        ApplicationReturnEffect { upper, lower }
    }

    fn local_callee_def(&self, callee: &Computation) -> Option<DefId> {
        let Expr::Var(reference) = self.session.poly.expr(callee.expr) else {
            return None;
        };
        self.session.poly.ref_target(*reference)
    }

    fn local_binding_by_def(&self, def: DefId) -> Option<&LocalBinding> {
        self.locals.iter().rev().find(|local| local.def == def)
    }

    fn instantiate_local_value(&mut self, local: &LocalBinding) -> TypeVar {
        let Some(scheme) = local.scheme.as_ref() else {
            return local.value;
        };
        let value = self.fresh_type_var();
        let level = self.session.infer.current_level();
        let predicate = crate::instantiate::instantiate_scheme(
            &self.session.poly.typ,
            &mut self.session.infer,
            level,
            scheme,
        );
        let upper = self.alloc_neg(Neg::Var(value));
        self.session.infer.subtype(predicate, upper);
        value
    }

    fn generalize_local_binding(
        &mut self,
        def: DefId,
        value: TypeVar,
        boundary: TypeLevel,
        fetch: BindingFetch,
    ) {
        let non_generic = self.local_non_generic_vars(def);
        let generalized = generalize_type_var_with_boundaries(
            self.session.infer.constraints(),
            value,
            fetch.generalize_boundary(boundary),
            boundary.child(),
            &non_generic,
        );
        let finalized = crate::generalize::finalize_generalized_compact_root(
            &mut self.session.poly.typ,
            self.session.infer.constraints(),
            &generalized,
        );
        self.set_local_let_scheme(def, finalized.scheme.clone());
        if let Some(local) = self.locals.iter_mut().rev().find(|local| local.def == def) {
            local.scheme = Some(finalized.scheme);
        }
    }

    fn local_non_generic_vars(&self, exclude: DefId) -> FxHashSet<TypeVar> {
        let mut vars = FxHashSet::default();
        let machine = self.session.infer.constraints();
        for local in &self.locals {
            if local.def == exclude {
                continue;
            }
            vars.insert(local.value);
            if let Some(effect) = local.effect.as_ref() {
                effect.collect_vars(&mut vars);
            }
            let Some(bounds) = machine.bounds().of(local.value) else {
                continue;
            };
            for lower in bounds.lowers() {
                collect_pos_id_vars(machine.types(), lower.pos, &mut vars);
            }
            for upper in bounds.uppers() {
                collect_neg_id_vars(machine.types(), upper.neg, &mut vars);
            }
        }
        vars
    }

    fn lambda_predicate_subtracts(
        &mut self,
        lambda_scope: LambdaScope,
        mut annotation_subtracts: Vec<SubtractId>,
        mut frame: FunctionPredicateFrame,
    ) -> Vec<SubtractId> {
        if lambda_scope != LambdaScope::Defined {
            return Vec::new();
        }
        annotation_subtracts.append(&mut frame.subtracts);
        annotation_subtracts.sort_by_key(|id| id.0);
        annotation_subtracts.dedup();
        annotation_subtracts
    }

    fn lambda_output_predicate(
        &mut self,
        body: &Computation,
        subtracts: &[SubtractId],
    ) -> (PosId, PosId) {
        self.lambda_output_predicate_vars(body.effect, body.value, subtracts)
    }

    fn lambda_output_predicate_vars(
        &mut self,
        body_effect: TypeVar,
        body_value: TypeVar,
        subtracts: &[SubtractId],
    ) -> (PosId, PosId) {
        if subtracts.is_empty() {
            let ret_eff = self.alloc_pos(Pos::Var(body_effect));
            let ret = self.alloc_pos(Pos::Var(body_value));
            return (ret_eff, ret);
        }

        let effect = self.fresh_type_var();
        let value = self.fresh_type_var();
        self.subtype_var_to_var(body_effect, effect);
        self.subtype_var_to_var(body_value, value);

        let ret_eff = self.alloc_pos(Pos::Var(effect));
        let ret = self.alloc_pos(Pos::Var(value));
        (
            self.wrap_pos_with_subtracts(ret_eff, subtracts),
            self.wrap_pos_with_subtracts(ret, subtracts),
        )
    }

    fn fresh_exact_pure_effect(&mut self) -> TypeVar {
        let effect = self.fresh_type_var();
        let bot = self.alloc_pos(Pos::Bot);
        let empty = self.empty_neg_row();
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        let effect_lower = self.alloc_pos(Pos::Var(effect));
        self.session.infer.subtype(bot, effect_upper);
        self.session.infer.subtype(effect_lower, empty);
        effect
    }

    fn empty_neg_row(&mut self) -> NegId {
        let top = self.alloc_neg(Neg::Top);
        self.alloc_neg(Neg::Row(Vec::new(), top))
    }

    fn never_neg(&mut self) -> NegId {
        self.alloc_neg(Neg::Bot)
    }

    fn constrain_lower(&mut self, var: TypeVar, lower: Pos) {
        let lower = self.alloc_pos(lower);
        let upper = self.alloc_neg(Neg::Var(var));
        self.session.infer.subtype(lower, upper);
    }

    fn constrain_upper(&mut self, var: TypeVar, upper: Neg) {
        let lower = self.alloc_pos(Pos::Var(var));
        let upper = self.alloc_neg(upper);
        self.session.infer.subtype(lower, upper);
    }

    fn constrain_exact_primitive(&mut self, var: TypeVar, name: &str) {
        self.constrain_lower(var, primitive_type(name));
        self.constrain_upper(var, primitive_neg_type(name));
    }

    fn subtype_var_to_var(&mut self, lower: TypeVar, upper: TypeVar) {
        let upper = self.alloc_neg(Neg::Var(upper));
        self.subtype(Pos::Var(lower), upper);
    }

    fn subtype_pos_to_var(&mut self, lower: PosId, upper: TypeVar) {
        let upper = self.alloc_neg(Neg::Var(upper));
        self.session.infer.subtype(lower, upper);
    }

    fn subtype(&mut self, lower: Pos, upper: NegId) {
        let lower = self.alloc_pos(lower);
        self.session.infer.subtype(lower, upper);
    }

    fn wrap_pos_with_subtracts(&mut self, pos: PosId, subtracts: &[SubtractId]) -> PosId {
        subtracts.iter().fold(pos, |inner, subtract| {
            self.alloc_pos(Pos::Stack {
                inner,
                weight: StackWeight::pop(*subtract),
            })
        })
    }

    fn alloc_pos(&mut self, pos: Pos) -> poly::types::PosId {
        self.session.infer.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.session.infer.alloc_neg(neg)
    }
}

#[derive(Clone)]
struct LocalBinding {
    name: Name,
    def: DefId,
    value: TypeVar,
    effect: Option<LocalEffect>,
    call_return_effect: LocalCallReturnEffect,
    scheme: Option<Scheme>,
}

#[derive(Clone)]
enum LocalEffect {
    Var(TypeVar),
    Stack { inner: TypeVar, weight: StackWeight },
}

impl LocalEffect {
    fn collect_vars(&self, vars: &mut FxHashSet<TypeVar>) {
        match self {
            LocalEffect::Var(effect) | LocalEffect::Stack { inner: effect, .. } => {
                vars.insert(*effect);
            }
        }
    }
}

struct LoweredLocalStmt {
    stmt: Stmt,
    effect: TypeVar,
}

struct ApplicationReturnEffect {
    upper: NegId,
    lower: PosId,
}

struct LoweredLambdaParam {
    pat: PatId,
    value: TypeVar,
    annotation: LambdaPatternAnnotation,
}

struct DefinedLambdaSkeleton {
    body_effect: TypeVar,
    body_value: TypeVar,
}

#[derive(Clone)]
enum ListLiteralItem {
    Single(Cst),
    Spread(Cst),
}

fn collect_pos_id_vars(types: &TypeArena, id: PosId, out: &mut FxHashSet<TypeVar>) {
    match types.pos(id) {
        Pos::Bot => {}
        Pos::Var(var) => {
            out.insert(*var);
        }
        Pos::Con(_, args) => collect_neu_ids_vars(types, args, out),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neg_id_vars(types, *arg, out);
            collect_neg_id_vars(types, *arg_eff, out);
            collect_pos_id_vars(types, *ret_eff, out);
            collect_pos_id_vars(types, *ret, out);
        }
        Pos::Record(fields) => {
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
        }
        Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { tail, fields } => {
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
            collect_pos_id_vars(types, *tail, out);
        }
        Pos::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_pos_id_vars(types, *payload, out);
                }
            }
        }
        Pos::Tuple(items) | Pos::Row(items) => {
            for item in items {
                collect_pos_id_vars(types, *item, out);
            }
        }
        Pos::Stack { inner, .. } => collect_pos_id_vars(types, *inner, out),
        Pos::NonSubtract(pos, _) => collect_pos_id_vars(types, *pos, out),
        Pos::Union(lhs, rhs) => {
            collect_pos_id_vars(types, *lhs, out);
            collect_pos_id_vars(types, *rhs, out);
        }
    }
}

fn collect_neg_id_vars(types: &TypeArena, id: NegId, out: &mut FxHashSet<TypeVar>) {
    match types.neg(id) {
        Neg::Top | Neg::Bot => {}
        Neg::Var(var) => {
            out.insert(*var);
        }
        Neg::Con(_, args) => collect_neu_ids_vars(types, args, out),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_pos_id_vars(types, *arg, out);
            collect_pos_id_vars(types, *arg_eff, out);
            collect_neg_id_vars(types, *ret_eff, out);
            collect_neg_id_vars(types, *ret, out);
        }
        Neg::Record(fields) => {
            for field in fields {
                collect_neg_id_vars(types, field.value, out);
            }
        }
        Neg::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_neg_id_vars(types, *payload, out);
                }
            }
        }
        Neg::Tuple(items) => {
            for item in items {
                collect_neg_id_vars(types, *item, out);
            }
        }
        Neg::Row(items, tail) => {
            for item in items {
                collect_neg_id_vars(types, *item, out);
            }
            collect_neg_id_vars(types, *tail, out);
        }
        Neg::Stack { inner, .. } => collect_neg_id_vars(types, *inner, out),
        Neg::Intersection(lhs, rhs) => {
            collect_neg_id_vars(types, *lhs, out);
            collect_neg_id_vars(types, *rhs, out);
        }
    }
}

fn collect_neu_ids_vars(types: &TypeArena, ids: &[NeuId], out: &mut FxHashSet<TypeVar>) {
    for id in ids {
        collect_neu_id_vars(types, *id, out);
    }
}

fn collect_neu_id_vars(types: &TypeArena, id: NeuId, out: &mut FxHashSet<TypeVar>) {
    match types.neu(id) {
        Neu::Bounds(lower, upper) => {
            collect_pos_id_vars(types, *lower, out);
            collect_neg_id_vars(types, *upper, out);
        }
        Neu::Con(_, args) => collect_neu_ids_vars(types, args, out),
        Neu::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neu_id_vars(types, *arg, out);
            collect_neu_id_vars(types, *arg_eff, out);
            collect_neu_id_vars(types, *ret_eff, out);
            collect_neu_id_vars(types, *ret, out);
        }
        Neu::Record(fields) => {
            for field in fields {
                collect_neu_id_vars(types, field.value, out);
            }
        }
        Neu::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_neu_id_vars(types, *payload, out);
                }
            }
        }
        Neu::Tuple(items) => collect_neu_ids_vars(types, items, out),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LocalCallReturnEffect {
    Unannotated,
    Annotated,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LambdaScope {
    Defined,
    Anonymous,
}

enum ConstructorSignaturePayload {
    Unit,
    Tuple(Vec<ConstructorSignaturePayloadItem>),
    Record(Vec<ConstructorSignatureRecordPayloadField>),
}

struct ConstructorSignaturePayloadItem {
    signature: Option<NegSignature>,
}

struct ConstructorSignatureRecordPayloadField {
    name: Name,
    signature: Option<NegSignature>,
}

enum ConstructorArg {
    Value {
        value: TypeVar,
        signature: Option<NegSignature>,
    },
    Record {
        value: TypeVar,
        fields: Vec<ConstructorRecordField>,
    },
}

impl ConstructorArg {
    fn value(&self) -> TypeVar {
        match self {
            ConstructorArg::Value { value, .. } | ConstructorArg::Record { value, .. } => *value,
        }
    }
}

struct ConstructorRecordField {
    name: String,
    value: TypeVar,
    signature: Option<NegSignature>,
}

struct PipeArg {
    expr: Computation,
}

enum StringLitPart {
    Text(String),
    Interp(StringInterpPart),
}

struct StringInterpPart {
    format: FormatSpec,
    expr: Cst,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FormatSpec {
    kind: FormatKind,
    align: Option<FormatAlign>,
    sign: Option<FormatSign>,
    fill: Option<String>,
    width: Option<i64>,
    precision: Option<i64>,
    alternate: bool,
    zero_pad: bool,
}

impl FormatSpec {
    fn display() -> Self {
        Self {
            kind: FormatKind::Display,
            align: None,
            sign: None,
            fill: None,
            width: None,
            precision: None,
            alternate: false,
            zero_pad: false,
        }
    }

    fn has_layout(&self) -> bool {
        self.align.is_some()
            || self.sign.is_some()
            || self.fill.is_some()
            || self.width.is_some()
            || self.precision.is_some()
            || self.alternate
            || self.zero_pad
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormatKind {
    Display,
    Debug,
    LowerHex,
    UpperHex,
}

impl FormatKind {
    fn method_name(self) -> &'static str {
        match self {
            Self::Display => "show",
            Self::Debug => "debug",
            Self::LowerHex => "lower_hex",
            Self::UpperHex => "upper_hex",
        }
    }

    fn format_function_name(self) -> &'static str {
        match self {
            Self::Display => "format_display",
            Self::Debug => "format_debug",
            Self::LowerHex => "format_lower_hex",
            Self::UpperHex => "format_upper_hex",
        }
    }

    fn variant_name(self) -> &'static str {
        match self {
            Self::Display => "display",
            Self::Debug => "debug",
            Self::LowerHex => "lower_hex",
            Self::UpperHex => "upper_hex",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormatAlign {
    Left,
    Right,
    Center,
}

impl FormatAlign {
    fn from_marker(marker: char) -> Option<Self> {
        match marker {
            '<' => Some(Self::Left),
            '>' => Some(Self::Right),
            '^' => Some(Self::Center),
            _ => None,
        }
    }

    fn variant_name(self) -> &'static str {
        match self {
            Self::Left => "left",
            Self::Right => "right",
            Self::Center => "center",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormatSign {
    Plus,
    Minus,
}

impl FormatSign {
    fn variant_name(self) -> &'static str {
        match self {
            Self::Plus => "plus",
            Self::Minus => "minus",
        }
    }
}

enum RuleLitPart {
    Token(String),
    Parser(Cst),
    CaptureWord(Name),
    CaptureParser { name: Name, parser: Cst },
}

struct RuleParserItem {
    parser: Computation,
    semantic: RuleSemantic,
}

struct RuleLowered {
    expr: Computation,
    semantic: RuleSemantic,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RuleSemantic {
    Unit,
    Record,
    Value,
}

struct CastScheme {
    source: Vec<String>,
    target: Vec<String>,
    scheme: Scheme,
}

struct CastSchemeBuilder<'a> {
    arena: &'a mut poly::expr::Arena,
    modules: &'a ModuleTable,
    vars: FxHashMap<AnnTypeVarId, TypeVar>,
    quantifiers: Vec<TypeVar>,
}

impl<'a> CastSchemeBuilder<'a> {
    fn new(arena: &'a mut poly::expr::Arena, modules: &'a ModuleTable) -> Self {
        Self {
            arena,
            modules,
            vars: FxHashMap::default(),
            quantifiers: Vec::new(),
        }
    }

    fn build(mut self, source: &AnnType, target: &AnnType) -> Result<CastScheme, LoweringError> {
        let source_path = self.constructor_path(source)?;
        let target_path = self.constructor_path(target)?;
        let arg = self.lower_neg(source)?;
        let arg_eff = self.arena.typ.alloc_neg(Neg::Bot);
        let ret_eff = self.arena.typ.alloc_pos(Pos::Bot);
        let ret = self.lower_pos(target)?;
        let predicate = self.arena.typ.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        Ok(CastScheme {
            source: source_path,
            target: target_path,
            scheme: Scheme {
                quantifiers: self.quantifiers,
                role_predicates: Vec::new(),
                recursive_bounds: Vec::new(),
                stack_quantifiers: Vec::new(),
                predicate,
            },
        })
    }

    fn constructor_path(&self, ann: &AnnType) -> Result<Vec<String>, LoweringError> {
        match ann {
            AnnType::Builtin(builtin) => Ok(vec![builtin.surface_name().to_string()]),
            AnnType::Named(id) => self.type_decl_path(*id),
            AnnType::Apply { callee, .. } => self.constructor_path(callee),
            ty => Err(LoweringError::AnnotationConstraint {
                error: AnnConstraintError::InvalidConstructorCallee { ty: ty.clone() },
            }),
        }
    }

    fn lower_pos(&mut self, ann: &AnnType) -> Result<PosId, LoweringError> {
        match ann {
            AnnType::Builtin(BuiltinType::Never) => Ok(self.arena.typ.alloc_pos(Pos::Bot)),
            AnnType::Builtin(builtin) => Ok(self.arena.typ.alloc_pos(Pos::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            ))),
            AnnType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.arena.typ.alloc_pos(Pos::Con(path, Vec::new())))
            }
            AnnType::Apply { callee, args } => {
                let path = self.constructor_path(callee)?;
                let args = args
                    .iter()
                    .map(|arg| self.lower_neu(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.typ.alloc_pos(Pos::Con(path, args)))
            }
            AnnType::Var(var) | AnnType::Wildcard(var) => {
                let var = self.type_var(var.id);
                Ok(self.arena.typ.alloc_pos(Pos::Var(var)))
            }
            AnnType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_pos(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.typ.alloc_pos(Pos::Tuple(items)))
            }
            ty => Err(LoweringError::AnnotationConstraint {
                error: AnnConstraintError::InvalidConstructorCallee { ty: ty.clone() },
            }),
        }
    }

    fn lower_neg(&mut self, ann: &AnnType) -> Result<NegId, LoweringError> {
        match ann {
            AnnType::Builtin(BuiltinType::Never) => Ok(self.arena.typ.alloc_neg(Neg::Bot)),
            AnnType::Builtin(builtin) => Ok(self.arena.typ.alloc_neg(Neg::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            ))),
            AnnType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.arena.typ.alloc_neg(Neg::Con(path, Vec::new())))
            }
            AnnType::Apply { callee, args } => {
                let path = self.constructor_path(callee)?;
                let args = args
                    .iter()
                    .map(|arg| self.lower_neu(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.typ.alloc_neg(Neg::Con(path, args)))
            }
            AnnType::Var(var) | AnnType::Wildcard(var) => {
                let var = self.type_var(var.id);
                Ok(self.arena.typ.alloc_neg(Neg::Var(var)))
            }
            AnnType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_neg(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.typ.alloc_neg(Neg::Tuple(items)))
            }
            ty => Err(LoweringError::AnnotationConstraint {
                error: AnnConstraintError::InvalidConstructorCallee { ty: ty.clone() },
            }),
        }
    }

    fn lower_neu(&mut self, ann: &AnnType) -> Result<NeuId, LoweringError> {
        let lower = self.lower_pos(ann)?;
        let upper = self.lower_neg(ann)?;
        Ok(self.arena.typ.alloc_neu(Neu::Bounds(lower, upper)))
    }

    fn type_var(&mut self, id: AnnTypeVarId) -> TypeVar {
        if let Some(var) = self.vars.get(&id) {
            return *var;
        }
        let var = self.arena.fresh_type_var();
        self.vars.insert(id, var);
        self.quantifiers.push(var);
        var
    }

    fn type_decl_path(&self, id: TypeDeclId) -> Result<Vec<String>, LoweringError> {
        let decl = self
            .modules
            .type_decl_by_id(id)
            .ok_or(LoweringError::AnnotationConstraint {
                error: AnnConstraintError::MissingTypeDecl { id },
            })?;
        Ok(self
            .modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect())
    }
}

fn build_cast_scheme_from_ann(
    arena: &mut poly::expr::Arena,
    modules: &ModuleTable,
    source: &AnnType,
    target: &AnnType,
) -> Result<CastScheme, LoweringError> {
    CastSchemeBuilder::new(arena, modules).build(source, target)
}

fn prepare_constructor_args(
    infer: &mut crate::Arena,
    payload: ConstructorSignaturePayload,
) -> Vec<ConstructorArg> {
    match payload {
        ConstructorSignaturePayload::Unit => Vec::new(),
        ConstructorSignaturePayload::Tuple(items) => items
            .into_iter()
            .map(|item| prepare_constructor_value_arg(infer, item))
            .collect(),
        ConstructorSignaturePayload::Record(fields) => {
            let record = infer.fresh_type_var();
            let fields = fields
                .into_iter()
                .map(|field| {
                    let value = infer.fresh_type_var();
                    ConstructorRecordField {
                        name: field.name.0,
                        value,
                        signature: field.signature,
                    }
                })
                .collect::<Vec<_>>();
            vec![ConstructorArg::Record {
                value: record,
                fields,
            }]
        }
    }
}

fn constructor_payload_arity(payload: &ConstructorPayload) -> usize {
    match payload {
        ConstructorPayload::Unit => 0,
        ConstructorPayload::Tuple(items) => items.len(),
        ConstructorPayload::Record(_) => 1,
    }
}

fn declared_constructor_expr_payloads(payloads: Vec<Cst>, arity: usize) -> Vec<Cst> {
    if arity == 1 || payloads.len() != 1 {
        return payloads;
    }

    let Some(group) = single_expr_paren_group_payload(&payloads[0]) else {
        return payloads;
    };
    let grouped = group
        .children()
        .filter(|child| child.kind() == SyntaxKind::Expr)
        .collect::<Vec<_>>();
    if grouped.len() == arity {
        grouped
    } else {
        payloads
    }
}

fn single_expr_paren_group_payload(payload: &Cst) -> Option<Cst> {
    let children = payload.children().collect::<Vec<_>>();
    let [group] = children.as_slice() else {
        return None;
    };
    (group.kind() == SyntaxKind::Paren).then(|| group.clone())
}

fn prepare_constructor_value_arg(
    infer: &mut crate::Arena,
    item: ConstructorSignaturePayloadItem,
) -> ConstructorArg {
    let value = infer.fresh_type_var();
    ConstructorArg::Value {
        value,
        signature: item.signature,
    }
}

fn constrain_constructor_arg_shapes(infer: &mut crate::Arena, args: &[ConstructorArg]) {
    for arg in args {
        let ConstructorArg::Record { value, fields } = arg else {
            continue;
        };
        let lower_fields = fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: infer.alloc_pos(Pos::Var(field.value)),
                optional: false,
            })
            .collect();
        let upper_fields = fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: infer.alloc_neg(Neg::Var(field.value)),
                optional: false,
            })
            .collect();
        let lower = infer.alloc_pos(Pos::Record(lower_fields));
        let upper = infer.alloc_neg(Neg::Record(upper_fields));
        let value_upper = infer.alloc_neg(Neg::Var(*value));
        let value_lower = infer.alloc_pos(Pos::Var(*value));
        infer.subtype(lower, value_upper);
        infer.subtype(value_lower, upper);
    }
}

fn build_constructor_payload_signatures(
    payload: ConstructorPayload,
    builder: &NegSignatureBuilder,
) -> Result<ConstructorSignaturePayload, LoweringError> {
    match payload {
        ConstructorPayload::Unit => Ok(ConstructorSignaturePayload::Unit),
        ConstructorPayload::Tuple(items) => items
            .into_iter()
            .map(|item| {
                let signature = item
                    .ty
                    .map(|ty| builder.build_type_expr(&ty))
                    .transpose()
                    .map_err(|error| LoweringError::NegSignatureBuild { error })?;
                Ok(ConstructorSignaturePayloadItem { signature })
            })
            .collect::<Result<Vec<_>, LoweringError>>()
            .map(ConstructorSignaturePayload::Tuple),
        ConstructorPayload::Record(fields) => fields
            .into_iter()
            .map(|field| {
                let signature = field
                    .ty
                    .map(|ty| builder.build_type_expr(&ty))
                    .transpose()
                    .map_err(|error| LoweringError::NegSignatureBuild { error })?;
                Ok(ConstructorSignatureRecordPayloadField {
                    name: field.name,
                    signature,
                })
            })
            .collect::<Result<Vec<_>, LoweringError>>()
            .map(ConstructorSignaturePayload::Record),
    }
}

fn connect_constructor_arg_signatures(
    infer: &mut crate::Arena,
    modules: &ModuleTable,
    vars: FxHashMap<String, TypeVar>,
    args: &[ConstructorArg],
) -> Result<(), LoweringError> {
    let mut lowerer = SignatureLowerer::with_vars(infer, modules, vars);
    for arg in args {
        match arg {
            ConstructorArg::Value {
                value,
                signature: Some(signature),
            } => {
                let lower = lowerer.alloc_pos(Pos::Var(*value));
                let upper = lowerer
                    .lower_data_neg(signature.as_type())
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                lowerer.infer.subtype(lower, upper);
            }
            ConstructorArg::Value {
                signature: None, ..
            } => {}
            ConstructorArg::Record { fields, .. } => {
                for field in fields {
                    if let Some(signature) = &field.signature {
                        let lower = lowerer.alloc_pos(Pos::Var(field.value));
                        let upper = lowerer
                            .lower_data_neg(signature.as_type())
                            .map_err(|error| LoweringError::SignatureConstraint { error })?;
                        lowerer.infer.subtype(lower, upper);
                    }
                }
            }
        }
    }
    Ok(())
}

fn connect_constructor_pattern_arg_signatures(
    infer: &mut crate::Arena,
    modules: &ModuleTable,
    vars: FxHashMap<String, TypeVar>,
    args: &[ConstructorArg],
) -> Result<(), LoweringError> {
    let mut lowerer = SignatureLowerer::with_vars(infer, modules, vars);
    for arg in args {
        match arg {
            ConstructorArg::Value {
                value,
                signature: Some(signature),
            } => {
                connect_constructor_pattern_value_signature(&mut lowerer, *value, signature)?;
            }
            ConstructorArg::Value {
                signature: None, ..
            } => {}
            ConstructorArg::Record { fields, .. } => {
                for field in fields {
                    if let Some(signature) = &field.signature {
                        connect_constructor_pattern_value_signature(
                            &mut lowerer,
                            field.value,
                            signature,
                        )?;
                    }
                }
            }
        }
    }
    Ok(())
}

fn connect_constructor_pattern_value_signature(
    lowerer: &mut SignatureLowerer<'_>,
    value: TypeVar,
    signature: &NegSignature,
) -> Result<(), LoweringError> {
    let lower = lowerer
        .lower_data_pos(signature.as_type())
        .map_err(|error| LoweringError::SignatureConstraint { error })?;
    let value_upper = lowerer.alloc_neg(Neg::Var(value));
    lowerer.infer.subtype(lower, value_upper);

    let value_lower = lowerer.alloc_pos(Pos::Var(value));
    let upper = lowerer
        .lower_data_neg(signature.as_type())
        .map_err(|error| LoweringError::SignatureConstraint { error })?;
    lowerer.infer.subtype(value_lower, upper);
    Ok(())
}

struct FunctionPredicateFrame {
    scope: LambdaScope,
    subtracts: Vec<SubtractId>,
}

impl FunctionPredicateFrame {
    fn new(scope: LambdaScope) -> Self {
        Self {
            scope,
            subtracts: Vec::new(),
        }
    }
}

struct LambdaPatternAnnotation {
    arg_eff: NegId,
    skeleton_arg_eff: NegId,
    local_effect: Option<LocalEffect>,
    subtracts: Vec<SubtractId>,
    call_return_effect: LocalCallReturnEffect,
}

pub use crate::typing::{BindingFetch, Computation, Evaluation};

#[derive(Debug, Clone, PartialEq, Eq)]
/// expression lowering が構造化して返す失敗。
pub enum LoweringError {
    UnsupportedSyntax { kind: SyntaxKind },
    UnsupportedPatternSyntax { kind: SyntaxKind },
    UnresolvedName { name: Name },
    InvalidNumber { text: String },
    MissingLambdaBody,
    MissingIfCondition,
    MissingIfBody,
    MissingCaseScrutinee,
    MissingCaseArmPattern,
    MissingCaseArmBody,
    MissingCatchScrutinee,
    MissingCatchArmPattern,
    MissingCatchArmBody,
    MissingFieldName,
    MissingOpName,
    MissingOpOperand,
    MissingRecordFieldName,
    MissingRecordFieldValue,
    MissingIndexArgument,
    MissingLocalBindingName,
    MissingLocalBindingBody,
    MissingLocalVarAct { name: Name },
    AnnotationBuild { error: AnnBuildError },
    AnnotationConstraint { error: AnnConstraintError },
    NegSignatureBuild { error: NegSignatureBuildError },
    SignatureConstraint { error: SignatureConstraintError },
    SignatureShapeMismatch { expected: SignatureShape },
    SignatureTypeMismatch { expected: SignatureShape },
    TypeMismatch { actual: String, expected: String },
}

fn item_is_trivia(item: &NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>) -> bool {
    item.as_token()
        .is_some_and(|token| matches!(token.kind(), SyntaxKind::Space | SyntaxKind::LineComment))
}

fn should_stop_expr_tail(
    kind: SyntaxKind,
    stop_at_with: bool,
    stop_kind: Option<SyntaxKind>,
) -> bool {
    (stop_at_with && kind == SyntaxKind::WithBlock) || stop_kind == Some(kind)
}

fn expr_path_prefix(items: &[CstItem]) -> Option<(Vec<Name>, usize)> {
    let Some(NodeOrToken::Token(head)) = items.first() else {
        return None;
    };
    if head.kind() != SyntaxKind::Ident {
        return None;
    }

    let mut path = vec![Name(head.text().to_string())];
    let mut consumed = 1;
    for item in &items[1..] {
        let NodeOrToken::Node(path_sep) = item else {
            break;
        };
        if path_sep.kind() != SyntaxKind::PathSep {
            break;
        }
        let Some(segment) = path_sep_name(path_sep) else {
            break;
        };
        path.push(segment);
        consumed += 1;
    }
    (path.len() > 1).then_some((path, consumed))
}

fn path_sep_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))
}

fn path_label(path: &[Name]) -> String {
    path.iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn builtin_op_from_path(path: &[Name]) -> Option<BuiltinOp> {
    match path {
        [namespace, name] if namespace.0 == "builtin_op" => resolve_builtin_op(&name.0),
        _ => None,
    }
}

fn field_name(node: &Cst) -> Option<String> {
    let token = node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::DotField)?;
    Some(token.text().trim_start_matches('.').to_string())
}

fn brace_group_is_record_literal(node: &Cst) -> bool {
    let fields = record_literal_fields(node);
    !fields.is_empty() && fields.iter().all(is_inline_record_field_expr)
}

fn record_literal_fields(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::Expr)
        .collect()
}

fn is_inline_record_field_expr(node: &Cst) -> bool {
    node.children()
        .any(|child| child.kind() == SyntaxKind::ApplyColon)
}

fn record_field_name(node: &Cst) -> Option<Name> {
    if node
        .children()
        .any(|child| child.kind() == SyntaxKind::PathSep)
    {
        return None;
    }
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent))
        .map(|token| Name(token.text().to_string()))
}

fn record_field_value(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::ApplyColon)?
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

fn block_lowering_items(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Binding | SyntaxKind::Expr | SyntaxKind::ForStmt
            )
        })
        .collect()
}

fn with_block_lowering_items(node: &Cst) -> Vec<Cst> {
    let mut out = Vec::new();
    collect_with_block_lowering_items(node, &mut out);
    out
}

fn collect_with_block_lowering_items(node: &Cst, out: &mut Vec<Cst>) {
    for child in node.children() {
        match child.kind() {
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup | SyntaxKind::WithBlock => {
                collect_with_block_lowering_items(&child, out);
            }
            SyntaxKind::Binding | SyntaxKind::Expr | SyntaxKind::ForStmt => out.push(child),
            _ => {}
        }
    }
}

fn with_public_binding_names(items: &[Cst]) -> Vec<Name> {
    let mut out = Vec::new();
    for item in items {
        if item.kind() != SyntaxKind::Binding || crate::binding_vis(item) == Vis::My {
            continue;
        }
        out.extend(crate::binding_value_names(item));
    }
    out
}

fn index_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::Expr)
        .or_else(|| {
            node.children()
                .find(|child| child.kind() == SyntaxKind::Bracket)
                .and_then(|bracket| {
                    bracket
                        .children()
                        .find(|child| child.kind() == SyntaxKind::Expr)
                })
        })
}

fn assignment_value_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::Expr)
        .last()
}

fn for_label(node: &Cst) -> Option<Cst> {
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ForHeader)?;
    header
        .children()
        .find(|child| child.kind() == SyntaxKind::ForLabel)
}

fn for_label_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent)
        .map(|token| Name(token.text().to_string()))
}

fn for_pattern(node: &Cst) -> Option<Cst> {
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ForHeader)?;
    header.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Pattern | SyntaxKind::PatOr | SyntaxKind::PatAs | SyntaxKind::PatParenGroup
        )
    })
}

fn for_iter_expr(node: &Cst) -> Option<Cst> {
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ForHeader)?;
    header
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

fn for_body_expr(node: &Cst) -> Option<Cst> {
    let body = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ForBody)?;
    body.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup | SyntaxKind::Expr
        )
    })
}

fn var_read_reference_name(text: &str) -> Option<Name> {
    let raw = text.strip_prefix('$')?;
    (!raw.is_empty()).then(|| Name(format!("&{raw}")))
}

fn local_var_binding_source(node: &Cst) -> Option<Name> {
    let source = crate::binding_name(node)?;
    source.0.starts_with('$').then_some(source)
}

fn var_init_name(source: &Name) -> Option<Name> {
    let raw = source.0.strip_prefix('$')?;
    (!raw.is_empty()).then(|| Name(format!("#{raw}")))
}

fn var_reference_name(source: &Name) -> Option<Name> {
    let raw = source.0.strip_prefix('$')?;
    (!raw.is_empty()).then(|| Name(format!("&{raw}")))
}

fn plain_rule_lit_text(node: &Cst) -> Option<String> {
    if node.children().any(|child| {
        matches!(
            child.kind(),
            SyntaxKind::RuleLazyCapture | SyntaxKind::RuleLitInterp
        )
    }) {
        return None;
    }

    Some(
        node.children_with_tokens()
            .filter_map(|item| item.into_token())
            .filter(|token| token.kind() == SyntaxKind::RuleLitText)
            .map(|token| token.text().to_string())
            .collect(),
    )
}

fn rule_lit_parts(node: &Cst) -> Result<Vec<RuleLitPart>, LoweringError> {
    let mut parts = Vec::new();
    for item in node.children_with_tokens() {
        if item_is_trivia(&item) {
            continue;
        }
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::RuleLitText => {
                parts.push(RuleLitPart::Token(token.text().to_string()));
            }
            NodeOrToken::Token(token)
                if matches!(
                    token.kind(),
                    SyntaxKind::RuleLitStart | SyntaxKind::RuleLitEnd
                ) => {}
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::RuleLazyCapture => {
                let name = lazy_capture_name(&child).ok_or(LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::RuleLazyCapture,
                })?;
                parts.push(RuleLitPart::CaptureWord(name));
            }
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::RuleLitInterp => {
                let parser = single_rule_lit_interp_expr(&child).ok_or(
                    LoweringError::UnsupportedSyntax {
                        kind: SyntaxKind::RuleLitInterp,
                    },
                )?;
                if let Some((name, parser)) = rule_expr_capture(&parser) {
                    parts.push(RuleLitPart::CaptureParser { name, parser });
                } else {
                    parts.push(RuleLitPart::Parser(parser));
                }
            }
            NodeOrToken::Node(child) => {
                return Err(LoweringError::UnsupportedSyntax { kind: child.kind() });
            }
            NodeOrToken::Token(token) => {
                return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
            }
        }
    }
    Ok(parts)
}

fn single_rule_lit_interp_expr(node: &Cst) -> Option<Cst> {
    let mut exprs = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::Expr);
    let expr = exprs.next()?;
    exprs.next().is_none().then_some(expr)
}

fn lazy_capture_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::RuleLitText)
        .map(|token| Name(token.text().to_string()))
}

fn rule_branches(node: &Cst) -> Vec<Vec<Cst>> {
    let mut branches = vec![Vec::new()];
    for child in node.children() {
        match child.kind() {
            SyntaxKind::Expr => {
                if let Some(branch) = branches.last_mut() {
                    branch.push(child);
                }
            }
            SyntaxKind::Separator => branches.push(Vec::new()),
            _ => {}
        }
    }
    branches
}

fn rule_expr_capture(node: &Cst) -> Option<(Name, Cst)> {
    let name = node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))?;
    let parser = node
        .children()
        .find(|child| child.kind() == SyntaxKind::RuleCapture)?
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)?;
    Some((name, parser))
}

fn rule_quant(node: &Cst) -> Option<SyntaxKind> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::RuleQuant)?
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find_map(|token| match token.kind() {
            SyntaxKind::RuleQuantStar
            | SyntaxKind::RuleQuantPlus
            | SyntaxKind::RuleQuantStarLazy
            | SyntaxKind::RuleQuantPlusLazy
            | SyntaxKind::RuleQuantOpt => Some(token.kind()),
            _ => None,
        })
}

fn direct_child(node: &Cst, kind: SyntaxKind) -> Option<Cst> {
    node.children().find(|child| child.kind() == kind)
}

fn plain_string_expr_text(node: &Cst) -> Result<Option<String>, LoweringError> {
    let mut strings = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::StringLit);
    let Some(first) = strings.next() else {
        return Ok(None);
    };
    if strings.next().is_some() {
        return Ok(None);
    }
    plain_string_lit_text(&first).map(Some)
}

fn plain_string_lit_text(node: &Cst) -> Result<String, LoweringError> {
    if node
        .children()
        .any(|child| child.kind() == SyntaxKind::StringInterp)
    {
        return Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::StringInterp,
        });
    }

    let mut text = String::new();
    let mut tokens = node.children_with_tokens().peekable();
    while let Some(item) = tokens.next() {
        let Some(token) = item.into_token() else {
            continue;
        };
        match token.kind() {
            SyntaxKind::StringText => text.push_str(token.text()),
            SyntaxKind::StringEscapeLead => text.push_str(&collect_string_escape_text(&mut tokens)),
            SyntaxKind::StringStart | SyntaxKind::StringEnd => {}
            _ => {}
        }
    }
    Ok(text)
}

fn string_lit_parts(node: &Cst) -> Result<Vec<StringLitPart>, LoweringError> {
    let mut parts = Vec::new();
    let mut tokens = node.children_with_tokens().peekable();
    while let Some(item) = tokens.next() {
        if item_is_trivia(&item) {
            continue;
        }
        match item {
            NodeOrToken::Token(token) => match token.kind() {
                SyntaxKind::StringText => {
                    push_string_lit_text_part(&mut parts, token.text().to_string());
                }
                SyntaxKind::StringEscapeLead => {
                    push_string_lit_text_part(&mut parts, collect_string_escape_text(&mut tokens));
                }
                SyntaxKind::StringStart | SyntaxKind::StringEnd => {}
                _ => return Err(LoweringError::UnsupportedSyntax { kind: token.kind() }),
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::StringInterp => {
                parts.push(string_interp_part(&child)?);
            }
            NodeOrToken::Node(child) => {
                return Err(LoweringError::UnsupportedSyntax { kind: child.kind() });
            }
        }
    }
    Ok(parts)
}

fn string_interp_part(node: &Cst) -> Result<StringLitPart, LoweringError> {
    let format = string_interp_format(node)?;
    let expr = string_interp_body_expr(node).ok_or(LoweringError::UnsupportedSyntax {
        kind: SyntaxKind::StringInterp,
    })?;
    Ok(StringLitPart::Interp(StringInterpPart { format, expr }))
}

fn string_interp_format(node: &Cst) -> Result<FormatSpec, LoweringError> {
    let mut tokens = node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .filter(|token| token.kind() == SyntaxKind::StringInterpFormatText);
    let Some(token) = tokens.next() else {
        return Ok(FormatSpec::display());
    };
    if tokens.next().is_some() {
        return Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::StringInterpFormatText,
        });
    }
    parse_format_spec(token.text())
}

fn parse_format_spec(text: &str) -> Result<FormatSpec, LoweringError> {
    let chars = text.chars().collect::<Vec<_>>();
    let mut index = 0usize;
    let mut spec = FormatSpec::display();

    if let Some((fill, align, next)) = parse_format_align(&chars) {
        spec.fill = fill;
        spec.align = Some(align);
        index = next;
    }

    match chars.get(index).copied() {
        Some('+') => {
            spec.sign = Some(FormatSign::Plus);
            index += 1;
        }
        Some('-') => {
            spec.sign = Some(FormatSign::Minus);
            index += 1;
        }
        _ => {}
    }

    if chars.get(index) == Some(&'#') {
        spec.alternate = true;
        index += 1;
    }

    if chars.get(index) == Some(&'0') {
        spec.zero_pad = true;
        index += 1;
    }

    let (width, next) = parse_format_decimal(&chars, index)?;
    spec.width = width;
    index = next;

    if chars.get(index) == Some(&'.') {
        let (precision, next) = parse_format_decimal(&chars, index + 1)?;
        let Some(precision) = precision else {
            return Err(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::StringInterpFormatText,
            });
        };
        spec.precision = Some(precision);
        index = next;
    }

    match chars.get(index).copied() {
        Some('?') => {
            spec.kind = FormatKind::Debug;
            index += 1;
        }
        Some('x') => {
            spec.kind = FormatKind::LowerHex;
            index += 1;
        }
        Some('X') => {
            spec.kind = FormatKind::UpperHex;
            index += 1;
        }
        Some(_) => {
            return Err(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::StringInterpFormatText,
            });
        }
        None => {}
    }

    if index == chars.len() {
        Ok(spec)
    } else {
        Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::StringInterpFormatText,
        })
    }
}

fn parse_format_align(chars: &[char]) -> Option<(Option<String>, FormatAlign, usize)> {
    if let Some(align) = chars.first().copied().and_then(FormatAlign::from_marker) {
        return Some((None, align, 1));
    }
    let fill = *chars.first()?;
    if fill == '\n' || fill == '\r' {
        return None;
    }
    let align = chars.get(1).copied().and_then(FormatAlign::from_marker)?;
    Some((Some(fill.to_string()), align, 2))
}

fn parse_format_decimal(
    chars: &[char],
    mut index: usize,
) -> Result<(Option<i64>, usize), LoweringError> {
    let start = index;
    let mut value = 0i64;
    while let Some(digit) = chars.get(index).and_then(|ch| ch.to_digit(10)) {
        value = value
            .checked_mul(10)
            .and_then(|value| value.checked_add(i64::from(digit)))
            .ok_or(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::StringInterpFormatText,
            })?;
        index += 1;
    }
    Ok(((index > start).then_some(value), index))
}

fn string_interp_body_expr(node: &Cst) -> Option<Cst> {
    node.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    })
}

fn push_string_lit_text_part(parts: &mut Vec<StringLitPart>, text: String) {
    if text.is_empty() {
        return;
    }
    match parts.last_mut() {
        Some(StringLitPart::Text(existing)) => existing.push_str(&text),
        _ => parts.push(StringLitPart::Text(text)),
    }
}

fn collect_string_escape_text(
    tokens: &mut std::iter::Peekable<rowan::SyntaxElementChildren<YulangLanguage>>,
) -> String {
    let Some(next) = tokens.next().and_then(|item| item.into_token()) else {
        return String::new();
    };
    match next.kind() {
        SyntaxKind::StringEscapeSimple => simple_escape_text(next.text()),
        SyntaxKind::StringEscapeUnicodeStart => collect_unicode_escape_text(tokens),
        _ => next.text().to_string(),
    }
}

fn simple_escape_text(text: &str) -> String {
    match text {
        "n" => "\n".to_string(),
        "r" => "\r".to_string(),
        "t" => "\t".to_string(),
        "\\" => "\\".to_string(),
        "\"" => "\"".to_string(),
        "0" => "\0".to_string(),
        other => other.to_string(),
    }
}

fn collect_unicode_escape_text(
    tokens: &mut std::iter::Peekable<rowan::SyntaxElementChildren<YulangLanguage>>,
) -> String {
    let Some(hex) = tokens.next().and_then(|item| item.into_token()) else {
        return String::new();
    };
    if hex.kind() != SyntaxKind::StringEscapeUnicodeHex {
        return hex.text().to_string();
    }
    let value = u32::from_str_radix(hex.text(), 16)
        .ok()
        .and_then(char::from_u32)
        .unwrap_or(char::REPLACEMENT_CHARACTER);
    if matches!(
        tokens
            .peek()
            .and_then(|item| item.as_token())
            .map(|token| token.kind()),
        Some(SyntaxKind::StringEscapeUnicodeEnd)
    ) {
        tokens.next();
    }
    value.to_string()
}

fn integer_number_token(text: &str) -> bool {
    text.chars().all(|ch| ch.is_ascii_digit())
}

fn parse_number_lit(text: &str) -> Result<(Lit, &'static str), LoweringError> {
    if integer_number_token(text) {
        let parsed = text
            .parse::<i64>()
            .map_err(|_| LoweringError::InvalidNumber {
                text: text.to_string(),
            })?;
        Ok((Lit::Int(parsed), "int"))
    } else {
        let parsed = text
            .parse::<f64>()
            .map_err(|_| LoweringError::InvalidNumber {
                text: text.to_string(),
            })?;
        Ok((Lit::Float(parsed), "float"))
    }
}

fn primitive_type(name: &str) -> Pos {
    Pos::Con(vec![name.into()], Vec::new())
}

fn primitive_neg_type(name: &str) -> Neg {
    Neg::Con(vec![name.into()], Vec::new())
}

fn expr_symbol_head_name(
    head: &NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>,
) -> Option<String> {
    let token = head.as_token()?;
    (token.kind() == SyntaxKind::Symbol).then(|| token.text().trim_start_matches(':').to_string())
}

fn recursive_lambda_label_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('\''))
        .map(|token| Name(token.text().to_string()))
}

fn binding_body_expr(binding: &Cst) -> Option<Cst> {
    crate::child_node(binding, SyntaxKind::BindingBody)?
        .children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
}

fn op_def_body_expr(node: &Cst) -> Option<Cst> {
    crate::child_node(node, SyntaxKind::OpDefBody)?
        .children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
}

fn binding_arg_patterns(binding: &Cst) -> Vec<Cst> {
    let Some(header) = crate::child_node(binding, SyntaxKind::BindingHeader) else {
        return Vec::new();
    };
    let Some(pattern) = crate::child_node(&header, SyntaxKind::Pattern) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    collect_binding_arg_patterns(&pattern, &mut out);
    out
}

fn local_binding_call_return_effect(binding: &Cst) -> LocalCallReturnEffect {
    if binding_type_expr(binding).is_some() {
        LocalCallReturnEffect::Annotated
    } else {
        LocalCallReturnEffect::Unannotated
    }
}

fn collect_binding_arg_patterns(node: &Cst, out: &mut Vec<Cst>) {
    for child in node.children() {
        if !matches!(child.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC) {
            continue;
        }
        collect_binding_arg_patterns(&child, out);
        let args = child
            .children()
            .filter(|item| item.kind() == SyntaxKind::Pattern)
            .collect::<Vec<_>>();
        if args.is_empty() && child.kind() == SyntaxKind::ApplyC {
            out.push(child);
        } else {
            out.extend(args);
        }
    }
}

fn pattern_type_expr(pattern: &Cst) -> Option<Cst> {
    if let Some(type_expr) = crate::direct_pattern_type_expr(pattern) {
        return Some(type_expr);
    }
    if !matches!(
        pattern.kind(),
        SyntaxKind::Pattern | SyntaxKind::PatParenGroup
    ) {
        return None;
    }
    pattern
        .children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern | SyntaxKind::PatParenGroup
            )
        })
        .and_then(|child| pattern_type_expr(&child))
}

fn module_body(module: &Cst) -> Option<Cst> {
    module.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
        )
    })
}

struct RoleImplLoweringContext {
    role: TypeDeclId,
    target_ann: AnnType,
    input_names: Vec<String>,
    input_signatures: Vec<SignatureType>,
    associated_signatures: Vec<(String, SignatureType)>,
    type_var_bindings: Vec<(String, AnnTypeVarId)>,
    ann_solver_vars: FxHashMap<AnnTypeVarId, TypeVar>,
}

#[derive(Clone)]
struct RoleMethodRequirement {
    signature: SignatureType,
}

struct ResolvedRoleMethodRequirement {
    role_method: DefId,
    role: Vec<String>,
    inputs: Vec<SignatureType>,
    associated: Vec<(String, SignatureType)>,
    signature: SignatureType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NegSignature {
    signature: SignatureType,
}

impl NegSignature {
    fn new(signature: SignatureType) -> Self {
        Self { signature }
    }

    fn as_type(&self) -> &SignatureType {
        &self.signature
    }
}

fn owner_signature_type(owner: TypeDeclId, type_vars: &[String]) -> SignatureType {
    let args = type_vars
        .iter()
        .map(|name| SignatureType::Var(SignatureVar { name: name.clone() }))
        .collect::<Vec<_>>();
    if args.is_empty() {
        SignatureType::Named(owner)
    } else {
        SignatureType::Apply {
            callee: Box::new(SignatureType::Named(owner)),
            args,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SignatureSelfAlias {
    owner: TypeDeclId,
    type_vars: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureType {
    Builtin(BuiltinType),
    Named(TypeDeclId),
    Var(SignatureVar),
    EffectRow(SignatureEffectRow),
    Effectful {
        eff: SignatureEffectRow,
        ret: Box<SignatureType>,
    },
    Tuple(Vec<SignatureType>),
    Apply {
        callee: Box<SignatureType>,
        args: Vec<SignatureType>,
    },
    Function {
        param: Box<SignatureType>,
        arg_eff: Option<SignatureEffectRow>,
        ret_eff: Option<SignatureEffectRow>,
        ret: Box<SignatureType>,
    },
}

/// Effectful ラッパを剥がして Function の (param, ret) を返す。
fn signature_function_step(sig: &SignatureType) -> Option<(&SignatureType, &SignatureType)> {
    match sig {
        SignatureType::Effectful { ret, .. } => signature_function_step(ret),
        SignatureType::Function { param, ret, .. } => Some((param.as_ref(), ret.as_ref())),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureEffectRow {
    items: Vec<SignatureEffectAtom>,
    tail: Option<SignatureVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SignatureEffectStack {
    weight: StackWeight,
    ids: Vec<SubtractId>,
}

impl SignatureEffectStack {
    fn empty() -> Self {
        Self {
            weight: StackWeight::empty(),
            ids: Vec::new(),
        }
    }
}

fn signature_subtractability_from_atoms(atoms: Vec<(Vec<String>, Vec<NeuId>)>) -> Subtractability {
    match atoms.as_slice() {
        [] => Subtractability::Empty,
        [(path, args)] => Subtractability::Set(path.clone(), args.clone()),
        _ => Subtractability::SetMany(atoms),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureEffectAtom {
    Type(SignatureType),
    Wildcard,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureVar {
    name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureShape {
    Any,
    Constructor,
    EffectRow,
    Function,
    Tuple,
}

impl SignatureShape {
    fn of(signature: &SignatureType) -> Self {
        match signature {
            SignatureType::Builtin(_) | SignatureType::Named(_) | SignatureType::Apply { .. } => {
                Self::Constructor
            }
            SignatureType::EffectRow(_) => Self::EffectRow,
            SignatureType::Effectful { ret, .. } => Self::of(ret),
            SignatureType::Tuple(_) => Self::Tuple,
            SignatureType::Function { .. } => Self::Function,
            SignatureType::Var(_) => Self::Any,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureConstraintError {
    MissingTypeDecl { id: TypeDeclId },
    InvalidConstructorCallee { ty: SignatureType },
    WildcardEffectRowInTypePosition,
}

fn compact_type_matches_signature(
    actual: &CompactType,
    expected: &SignatureType,
    modules: &ModuleTable,
) -> bool {
    if actual.never {
        return true;
    }
    match expected {
        SignatureType::Var(_) => true,
        SignatureType::Effectful { ret, .. } => {
            compact_type_matches_signature(actual, ret, modules)
        }
        SignatureType::Function { ret, .. } => {
            compact_type_matches_function_signature(actual, ret, modules)
        }
        SignatureType::Tuple(items) => compact_type_matches_tuple_signature(actual, items, modules),
        SignatureType::EffectRow(_) => compact_type_matches_effect_row_signature(actual),
        SignatureType::Builtin(_) | SignatureType::Named(_) | SignatureType::Apply { .. } => {
            let Some(expected) = expected_constructor_signature(expected, modules) else {
                return true;
            };
            compact_type_matches_constructor_signature(actual, &expected, modules)
        }
    }
}

fn compact_type_matches_function_signature(
    actual: &CompactType,
    expected_ret: &SignatureType,
    modules: &ModuleTable,
) -> bool {
    if compact_type_has_concrete_non_function(actual) {
        return false;
    }
    actual
        .funs
        .iter()
        .all(|fun| compact_fun_matches_signature(fun, expected_ret, modules))
}

fn compact_type_matches_tuple_signature(
    actual: &CompactType,
    expected_items: &[SignatureType],
    modules: &ModuleTable,
) -> bool {
    if compact_type_has_concrete_non_tuple(actual) {
        return false;
    }
    actual.tuples.iter().all(|tuple| {
        tuple.items.len() == expected_items.len()
            && tuple
                .items
                .iter()
                .zip(expected_items)
                .all(|(actual, expected)| compact_type_matches_signature(actual, expected, modules))
    })
}

fn compact_fun_matches_signature(
    actual: &CompactFun,
    expected_ret: &SignatureType,
    modules: &ModuleTable,
) -> bool {
    compact_type_matches_signature(&actual.ret, expected_ret, modules)
}

fn compact_type_matches_effect_row_signature(actual: &CompactType) -> bool {
    !actual.never
        && actual.builtins.is_empty()
        && actual.cons.is_empty()
        && actual.funs.is_empty()
        && actual.records.is_empty()
        && actual.record_spreads.is_empty()
        && actual.poly_variants.is_empty()
        && actual.tuples.is_empty()
}

fn compact_type_matches_constructor_signature(
    actual: &CompactType,
    expected: &ExpectedConstructorSignature,
    modules: &ModuleTable,
) -> bool {
    if compact_type_has_concrete_non_constructor(actual) {
        return false;
    }
    let expected_builtin = expected.builtin();
    actual
        .builtins
        .iter()
        .all(|builtin| Some(*builtin) == expected_builtin)
        && actual.cons.iter().all(|(path, args)| {
            path == &expected.path
                && args.len() == expected.args.len()
                && args.iter().zip(&expected.args).all(|(actual, expected)| {
                    compact_bounds_matches_signature(actual, expected, modules)
                })
        })
}

fn compact_type_has_concrete_non_function(actual: &CompactType) -> bool {
    !actual.builtins.is_empty()
        || !actual.cons.is_empty()
        || !actual.records.is_empty()
        || !actual.record_spreads.is_empty()
        || !actual.poly_variants.is_empty()
        || !actual.tuples.is_empty()
        || !actual.rows.is_empty()
}

fn compact_type_has_concrete_non_tuple(actual: &CompactType) -> bool {
    !actual.builtins.is_empty()
        || !actual.cons.is_empty()
        || !actual.funs.is_empty()
        || !actual.records.is_empty()
        || !actual.record_spreads.is_empty()
        || !actual.poly_variants.is_empty()
        || !actual.rows.is_empty()
}

fn compact_type_has_concrete_non_constructor(actual: &CompactType) -> bool {
    !actual.funs.is_empty()
        || !actual.records.is_empty()
        || !actual.record_spreads.is_empty()
        || !actual.poly_variants.is_empty()
        || !actual.tuples.is_empty()
        || !actual.rows.is_empty()
}

fn compact_bounds_matches_signature(
    actual: &CompactBounds,
    expected: &SignatureType,
    modules: &ModuleTable,
) -> bool {
    match actual {
        CompactBounds::Interval { lower, upper, .. } => {
            compact_type_matches_signature(lower, expected, modules)
                && compact_type_matches_signature(upper, expected, modules)
        }
        CompactBounds::Con { path, args } => {
            let Some(expected) = expected_constructor_signature(expected, modules) else {
                return true;
            };
            path == &expected.path
                && args.len() == expected.args.len()
                && args.iter().zip(&expected.args).all(|(actual, expected)| {
                    compact_bounds_matches_signature(actual, expected, modules)
                })
        }
        CompactBounds::Fun { ret, .. } => match expected {
            SignatureType::Function {
                ret: expected_ret, ..
            } => compact_bounds_matches_signature(ret, expected_ret, modules),
            SignatureType::Var(_) => true,
            SignatureType::Effectful { ret: expected, .. } => {
                compact_bounds_matches_signature(actual, expected, modules)
            }
            _ => false,
        },
        CompactBounds::Tuple { items } => match expected {
            SignatureType::Var(_) => true,
            _ => items.is_empty(),
        },
        CompactBounds::Record { .. } | CompactBounds::PolyVariant { .. } => {
            matches!(expected, SignatureType::Var(_))
        }
    }
}

#[derive(Debug, Clone)]
struct ExpectedConstructorSignature {
    path: Vec<String>,
    args: Vec<SignatureType>,
}

impl ExpectedConstructorSignature {
    fn builtin(&self) -> Option<BuiltinType> {
        match self.path.as_slice() {
            [name] if self.args.is_empty() => BuiltinType::from_surface_name(name),
            _ => None,
        }
    }
}

fn expected_constructor_signature(
    expected: &SignatureType,
    modules: &ModuleTable,
) -> Option<ExpectedConstructorSignature> {
    match expected {
        SignatureType::Builtin(builtin) => Some(ExpectedConstructorSignature {
            path: vec![builtin.surface_name().to_string()],
            args: Vec::new(),
        }),
        SignatureType::Named(id) => Some(ExpectedConstructorSignature {
            path: signature_type_decl_path(*id, modules)?,
            args: Vec::new(),
        }),
        SignatureType::Apply { callee, args } => {
            let mut expected = expected_constructor_signature(callee, modules)?;
            expected.args.extend(args.iter().cloned());
            Some(expected)
        }
        SignatureType::Effectful { ret, .. } => expected_constructor_signature(ret, modules),
        SignatureType::Var(_) => None,
        SignatureType::EffectRow(_) | SignatureType::Function { .. } | SignatureType::Tuple(_) => {
            None
        }
    }
}

fn builtin_annotation_mismatch(
    actual: &CompactType,
    expected: &SignatureType,
) -> Option<(BuiltinType, BuiltinType)> {
    let actual = compact_type_single_builtin(actual)?;
    let expected = signature_single_builtin(expected)?;
    (actual != expected && !builtin_annotation_mismatch_can_be_deferred(actual, expected))
        .then_some((actual, expected))
}

fn compact_type_single_builtin(ty: &CompactType) -> Option<BuiltinType> {
    if ty.never
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.poly_variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
    {
        return None;
    }
    let [builtin] = ty.builtins.as_slice() else {
        return None;
    };
    Some(*builtin)
}

fn signature_single_builtin(signature: &SignatureType) -> Option<BuiltinType> {
    match signature {
        SignatureType::Effectful { ret, .. } => signature_single_builtin(ret),
        SignatureType::Builtin(builtin) => Some(*builtin),
        _ => None,
    }
}

fn builtin_annotation_mismatch_can_be_deferred(actual: BuiltinType, expected: BuiltinType) -> bool {
    matches!(
        (actual, expected),
        (BuiltinType::Int, BuiltinType::Float) | (BuiltinType::Float, BuiltinType::Int)
    )
}

fn signature_type_decl_path(id: TypeDeclId, modules: &ModuleTable) -> Option<Vec<String>> {
    let decl = modules.type_decl_by_id(id)?;
    Some(
        modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect(),
    )
}

struct SignatureLowerer<'a> {
    infer: &'a mut crate::Arena,
    modules: &'a ModuleTable,
    vars: FxHashMap<String, TypeVar>,
    new_var_level: Option<TypeLevel>,
}

impl<'a> SignatureLowerer<'a> {
    fn new(infer: &'a mut crate::Arena, modules: &'a ModuleTable) -> Self {
        Self {
            infer,
            modules,
            vars: FxHashMap::default(),
            new_var_level: None,
        }
    }

    fn with_vars(
        infer: &'a mut crate::Arena,
        modules: &'a ModuleTable,
        vars: FxHashMap<String, TypeVar>,
    ) -> Self {
        Self {
            infer,
            modules,
            vars,
            new_var_level: None,
        }
    }

    fn with_vars_at_level(
        infer: &'a mut crate::Arena,
        modules: &'a ModuleTable,
        vars: FxHashMap<String, TypeVar>,
        new_var_level: TypeLevel,
    ) -> Self {
        Self {
            infer,
            modules,
            vars,
            new_var_level: Some(new_var_level),
        }
    }

    fn lower_role_arg(
        &mut self,
        signature: &SignatureType,
    ) -> Result<RoleConstraintArg, SignatureConstraintError> {
        Ok(RoleConstraintArg {
            lower: self.lower_pos(signature)?,
            upper: self.lower_neg(signature)?,
        })
    }

    fn lower_pos(&mut self, signature: &SignatureType) -> Result<PosId, SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => Ok(self.lower_builtin_pos(*builtin)),
            SignatureType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.alloc_pos(Pos::Con(path, Vec::new())))
            }
            SignatureType::Var(var) => {
                let var = self.signature_var(var);
                Ok(self.alloc_pos(Pos::Var(var)))
            }
            SignatureType::EffectRow(row) => self.lower_effect_row_pos(row),
            SignatureType::Effectful { ret, .. } => self.lower_pos(ret),
            SignatureType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_pos(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.alloc_pos(Pos::Tuple(items)))
            }
            SignatureType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(self.alloc_pos(Pos::Con(path, neu_args)))
            }
            SignatureType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.lower_neg(param)?;
                let arg_eff = self.lower_arg_effect_neg(arg_eff.as_ref())?;
                let ret_eff = self.lower_ret_effect_pos(ret_eff.as_ref())?;
                let ret = self.lower_pos(ret)?;
                Ok(self.alloc_pos(Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    fn lower_neg(&mut self, signature: &SignatureType) -> Result<NegId, SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => Ok(self.lower_builtin_neg(*builtin)),
            SignatureType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.alloc_neg(Neg::Con(path, Vec::new())))
            }
            SignatureType::Var(var) => {
                let var = self.signature_var(var);
                Ok(self.alloc_neg(Neg::Var(var)))
            }
            SignatureType::EffectRow(row) => self.lower_subtractable_effect_row_neg(row),
            SignatureType::Effectful { ret, .. } => self.lower_neg(ret),
            SignatureType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_neg(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.alloc_neg(Neg::Tuple(items)))
            }
            SignatureType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(self.alloc_neg(Neg::Con(path, neu_args)))
            }
            SignatureType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.lower_pos(param)?;
                let arg_eff = self.lower_arg_effect_pos(arg_eff.as_ref())?;
                let ret_eff = self.lower_ret_effect_neg(ret_eff.as_ref())?;
                let ret = self.lower_neg(ret)?;
                Ok(self.alloc_neg(Neg::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    fn lower_data_neg(
        &mut self,
        signature: &SignatureType,
    ) -> Result<NegId, SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => Ok(self.lower_builtin_neg(*builtin)),
            SignatureType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.alloc_neg(Neg::Con(path, Vec::new())))
            }
            SignatureType::Var(var) => {
                let var = self.signature_var(var);
                Ok(self.alloc_neg(Neg::Var(var)))
            }
            SignatureType::EffectRow(row) => self.lower_effect_row_neg(row),
            SignatureType::Effectful { ret, .. } => self.lower_data_neg(ret),
            SignatureType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_data_neg(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.alloc_neg(Neg::Tuple(items)))
            }
            SignatureType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(self.alloc_neg(Neg::Con(path, neu_args)))
            }
            SignatureType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.lower_pos(param)?;
                let arg_eff = self.lower_arg_effect_pos(arg_eff.as_ref())?;
                let ret_eff = self.lower_data_ret_effect_neg(ret_eff.as_ref())?;
                let ret = self.lower_data_neg(ret)?;
                Ok(self.alloc_neg(Neg::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    fn lower_data_pos(
        &mut self,
        signature: &SignatureType,
    ) -> Result<PosId, SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => Ok(self.lower_builtin_pos(*builtin)),
            SignatureType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.alloc_pos(Pos::Con(path, Vec::new())))
            }
            SignatureType::Var(var) => {
                let var = self.signature_var(var);
                Ok(self.alloc_pos(Pos::Var(var)))
            }
            SignatureType::EffectRow(row) => self.lower_data_effect_row_pos(row),
            SignatureType::Effectful { ret, .. } => self.lower_data_pos(ret),
            SignatureType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_data_pos(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.alloc_pos(Pos::Tuple(items)))
            }
            SignatureType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(self.alloc_pos(Pos::Con(path, neu_args)))
            }
            SignatureType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.lower_data_neg(param)?;
                let arg_eff = self.lower_arg_effect_neg(arg_eff.as_ref())?;
                let ret_eff = self.lower_data_ret_effect_pos(ret_eff.as_ref())?;
                let ret = self.lower_data_pos(ret)?;
                Ok(self.alloc_pos(Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    fn lower_arg_effect_pos(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<PosId, SignatureConstraintError> {
        row.map(|row| self.lower_effect_row_pos(row))
            .unwrap_or_else(|| Ok(self.alloc_pos(Pos::Bot)))
    }

    fn lower_arg_effect_neg(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<NegId, SignatureConstraintError> {
        row.map(|row| self.lower_subtractable_effect_row_neg(row))
            .unwrap_or_else(|| {
                let top = self.alloc_neg(Neg::Top);
                Ok(self.alloc_neg(Neg::Row(Vec::new(), top)))
            })
    }

    fn lower_ret_effect_pos(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<PosId, SignatureConstraintError> {
        row.map(|row| self.lower_effect_row_pos(row))
            .unwrap_or_else(|| Ok(self.alloc_pos(Pos::Bot)))
    }

    fn lower_data_ret_effect_pos(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<PosId, SignatureConstraintError> {
        row.map(|row| self.lower_data_effect_row_pos(row))
            .unwrap_or_else(|| Ok(self.alloc_pos(Pos::Bot)))
    }

    fn lower_ret_effect_neg(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<NegId, SignatureConstraintError> {
        row.map(|row| self.lower_subtractable_effect_row_neg(row))
            .unwrap_or_else(|| {
                let top = self.alloc_neg(Neg::Top);
                Ok(self.alloc_neg(Neg::Row(Vec::new(), top)))
            })
    }

    fn lower_data_ret_effect_neg(
        &mut self,
        row: Option<&SignatureEffectRow>,
    ) -> Result<NegId, SignatureConstraintError> {
        row.map(|row| self.lower_data_effect_row_neg(row))
            .unwrap_or_else(|| {
                let top = self.alloc_neg(Neg::Top);
                Ok(self.alloc_neg(Neg::Row(Vec::new(), top)))
            })
    }

    fn lower_effect_row_pos(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<PosId, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            let effect = self.fresh_type_var();
            self.connect_effect_tail_lower(effect, row);
            let stack = self.effect_row_stack(row)?;
            self.register_stack_facts(effect, &stack.weight);
            let effect = self.alloc_pos(Pos::Var(effect));
            return Ok(self.wrap_pos_with_stack(effect, &stack.weight));
        }
        let mut items = Vec::with_capacity(row.items.len() + usize::from(row.tail.is_some()));
        for atom in &row.items {
            let SignatureEffectAtom::Type(ty) = atom else {
                unreachable!("wildcard checked above");
            };
            items.push(self.lower_pos(ty)?);
        }
        if let Some(tail) = &row.tail {
            let tail = self.signature_var(tail);
            items.push(self.alloc_pos(Pos::Var(tail)));
        }
        Ok(self.alloc_pos(Pos::Row(items)))
    }

    fn lower_data_effect_row_pos(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<PosId, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            return Err(SignatureConstraintError::WildcardEffectRowInTypePosition);
        }
        let mut items = Vec::with_capacity(row.items.len() + usize::from(row.tail.is_some()));
        for atom in &row.items {
            let SignatureEffectAtom::Type(ty) = atom else {
                unreachable!("wildcard checked above");
            };
            items.push(self.lower_data_pos(ty)?);
        }
        if let Some(tail) = &row.tail {
            let tail = self.signature_var(tail);
            let weight = self.data_effect_tail_stack(tail, row)?;
            let tail = self.alloc_pos(Pos::Var(tail));
            items.push(self.wrap_pos_with_stack(tail, &weight));
        }
        Ok(self.alloc_pos(Pos::Row(items)))
    }

    fn lower_subtractable_effect_row_neg(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<NegId, SignatureConstraintError> {
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let tail = self.signature_var(tail);
            return Ok(self.alloc_neg(Neg::Var(tail)));
        }

        let effect = self.fresh_type_var();
        self.connect_effect_tail_lower(effect, row);
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(effect, &stack.weight);
        let effect = self.alloc_neg(Neg::Var(effect));
        Ok(self.wrap_neg_with_stack(effect, &stack.weight))
    }

    fn lower_data_effect_row_neg(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<NegId, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            return Err(SignatureConstraintError::WildcardEffectRowInTypePosition);
        }
        let items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_neg(atom))
            .collect::<Result<Vec<_>, _>>()?;
        let tail = if let Some(tail) = &row.tail {
            let tail = self.signature_var(tail);
            let weight = self.data_effect_tail_stack(tail, row)?;
            let tail = self.alloc_neg(Neg::Var(tail));
            self.wrap_neg_with_stack(tail, &weight)
        } else {
            self.alloc_neg(Neg::Top)
        };
        Ok(self.alloc_neg(Neg::Row(items, tail)))
    }

    fn lower_effect_row_neg(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<NegId, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            return Err(SignatureConstraintError::WildcardEffectRowInTypePosition);
        }
        let items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_neg(atom))
            .collect::<Result<Vec<_>, _>>()?;
        let tail = if let Some(tail) = &row.tail {
            let tail = self.signature_var(tail);
            self.alloc_neg(Neg::Var(tail))
        } else {
            self.alloc_neg(Neg::Top)
        };
        Ok(self.alloc_neg(Neg::Row(items, tail)))
    }

    fn lower_effect_atom_neg(
        &mut self,
        atom: &SignatureEffectAtom,
    ) -> Result<NegId, SignatureConstraintError> {
        match atom {
            SignatureEffectAtom::Type(ty) => self.lower_data_neg(ty),
            SignatureEffectAtom::Wildcard => {
                Err(SignatureConstraintError::WildcardEffectRowInTypePosition)
            }
        }
    }

    fn data_effect_tail_stack(
        &mut self,
        tail: TypeVar,
        row: &SignatureEffectRow,
    ) -> Result<StackWeight, SignatureConstraintError> {
        let atoms = row
            .items
            .iter()
            .map(|atom| self.effect_atom_con(atom))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if atoms.is_empty() {
            return Ok(StackWeight::empty());
        }

        let id = self.infer.fresh_subtract_id();
        let subtractability = match atoms.as_slice() {
            [(path, _)] => Subtractability::AllExcept(path.clone(), Vec::new()),
            _ => Subtractability::AllExceptMany(
                atoms
                    .into_iter()
                    .map(|(path, _)| (path, Vec::new()))
                    .collect(),
            ),
        };
        // scheme 量化は machine の subtract fact を起点に保存対象を決めるので、
        // データ宣言由来の push は fact も登録しておく。
        self.infer
            .declared_subtract_fact(tail, id, subtractability.clone());
        Ok(StackWeight::push(id, subtractability))
    }

    fn connect_effect_tail_lower(&mut self, effect: TypeVar, row: &SignatureEffectRow) {
        if let Some(tail) = &row.tail {
            let tail = self.signature_var(tail);
            let tail = self.alloc_pos(Pos::Var(tail));
            let effect = self.alloc_neg(Neg::Var(effect));
            self.infer.subtype(tail, effect);
        }
    }

    fn effect_row_stack(
        &mut self,
        row: &SignatureEffectRow,
    ) -> Result<SignatureEffectStack, SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            let id = self.infer.fresh_subtract_id();
            return Ok(SignatureEffectStack {
                weight: StackWeight::push(id, Subtractability::All),
                ids: vec![id],
            });
        }

        let atoms = row
            .items
            .iter()
            .map(|atom| self.effect_atom_con(atom))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if atoms.is_empty() {
            if row.tail.is_none() {
                let id = self.infer.fresh_subtract_id();
                return Ok(SignatureEffectStack {
                    weight: StackWeight::push(id, Subtractability::Empty),
                    ids: vec![id],
                });
            }
            return Ok(SignatureEffectStack::empty());
        }

        let id = self.infer.fresh_subtract_id();
        Ok(SignatureEffectStack {
            weight: StackWeight::push(id, signature_subtractability_from_atoms(atoms)),
            ids: vec![id],
        })
    }

    fn wrap_neg_with_stack(&mut self, neg: NegId, weight: &StackWeight) -> NegId {
        if weight.is_empty() {
            return neg;
        }
        self.alloc_neg(Neg::Stack {
            inner: neg,
            weight: weight.clone(),
        })
    }

    fn register_stack_facts(&mut self, var: TypeVar, weight: &StackWeight) {
        for entry in weight.entries() {
            for subtractability in &entry.stack {
                self.infer
                    .declared_subtract_fact(var, entry.id, subtractability.clone());
            }
        }
    }

    fn wrap_pos_with_stack(&mut self, pos: PosId, weight: &StackWeight) -> PosId {
        if weight.is_empty() {
            return pos;
        }
        self.alloc_pos(Pos::Stack {
            inner: pos,
            weight: weight.clone(),
        })
    }

    fn effect_atom_con(
        &mut self,
        atom: &SignatureEffectAtom,
    ) -> Result<Option<(Vec<String>, Vec<NeuId>)>, SignatureConstraintError> {
        match atom {
            SignatureEffectAtom::Type(SignatureType::Var(_)) => Ok(None),
            SignatureEffectAtom::Type(ty) => self.constructor_path(ty).map(Some),
            SignatureEffectAtom::Wildcard => Ok(None),
        }
    }

    fn lower_invariant_arg(
        &mut self,
        signature: &SignatureType,
    ) -> Result<NeuId, SignatureConstraintError> {
        let lower = self.lower_pos(signature)?;
        let upper = self.lower_neg(signature)?;
        Ok(self.alloc_neu(Neu::Bounds(lower, upper)))
    }

    fn lower_builtin_pos(&mut self, builtin: BuiltinType) -> PosId {
        match builtin {
            BuiltinType::Never => self.alloc_pos(Pos::Bot),
            BuiltinType::Int
            | BuiltinType::Float
            | BuiltinType::Bool
            | BuiltinType::FileHandle
            | BuiltinType::Unit => self.alloc_pos(Pos::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            )),
        }
    }

    fn lower_builtin_neg(&mut self, builtin: BuiltinType) -> NegId {
        match builtin {
            BuiltinType::Never => self.alloc_neg(Neg::Bot),
            BuiltinType::Int
            | BuiltinType::Float
            | BuiltinType::Bool
            | BuiltinType::FileHandle
            | BuiltinType::Unit => self.alloc_neg(Neg::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            )),
        }
    }

    fn constructor_path(
        &mut self,
        signature: &SignatureType,
    ) -> Result<(Vec<String>, Vec<NeuId>), SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => {
                Ok((vec![builtin.surface_name().to_string()], Vec::new()))
            }
            SignatureType::Named(id) => Ok((self.type_decl_path(*id)?, Vec::new())),
            SignatureType::Apply { callee, args } => {
                let (path, mut head_args) = self.constructor_path(callee)?;
                for arg in args {
                    head_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok((path, head_args))
            }
            ty => Err(SignatureConstraintError::InvalidConstructorCallee { ty: ty.clone() }),
        }
    }

    fn type_decl_path(&self, id: TypeDeclId) -> Result<Vec<String>, SignatureConstraintError> {
        let decl = self
            .modules
            .type_decl_by_id(id)
            .ok_or(SignatureConstraintError::MissingTypeDecl { id })?;
        Ok(self
            .modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect())
    }

    fn signature_var(&mut self, var: &SignatureVar) -> TypeVar {
        if let Some(found) = self.vars.get(&var.name) {
            return *found;
        }
        let ty = self.fresh_type_var();
        self.vars.insert(var.name.clone(), ty);
        ty
    }

    fn fresh_type_var(&mut self) -> TypeVar {
        if let Some(level) = self.new_var_level {
            self.infer.fresh_type_var_at(level)
        } else {
            self.infer.fresh_type_var()
        }
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.infer.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.infer.alloc_neg(neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.infer.alloc_neu(neu)
    }
}

struct RoleImplAnnSpec {
    role: TypeDeclId,
    target: AnnType,
    inputs: Vec<AnnType>,
}

fn role_impl_ann_spec(
    modules: &ModuleTable,
    head: AnnType,
    description: Option<AnnType>,
) -> Option<RoleImplAnnSpec> {
    if let Some(description) = description {
        let (role, mut inputs) = role_ann_application(modules, description)?;
        let mut all_inputs = Vec::with_capacity(inputs.len() + 1);
        all_inputs.push(head.clone());
        all_inputs.append(&mut inputs);
        return Some(RoleImplAnnSpec {
            role,
            target: head,
            inputs: all_inputs,
        });
    }

    let (role, inputs) = role_ann_application(modules, head.clone())?;
    let target = inputs.first().cloned().unwrap_or(head);
    Some(RoleImplAnnSpec {
        role,
        target,
        inputs,
    })
}

fn role_ann_application(modules: &ModuleTable, ann: AnnType) -> Option<(TypeDeclId, Vec<AnnType>)> {
    match ann {
        AnnType::Named(id) if ann_type_is_role(modules, id) => Some((id, Vec::new())),
        AnnType::Apply { callee, args } => match *callee {
            AnnType::Named(id) if ann_type_is_role(modules, id) => Some((id, args)),
            _ => None,
        },
        _ => None,
    }
}

fn ann_type_is_role(modules: &ModuleTable, id: TypeDeclId) -> bool {
    modules
        .type_decl_by_id(id)
        .is_some_and(|decl| decl.kind == ModuleTypeKind::Role)
}

fn substitute_role_requirement_signature(
    requirement: &RoleMethodRequirement,
    context: &RoleImplLoweringContext,
) -> SignatureType {
    let substitutions = context
        .input_names
        .iter()
        .cloned()
        .zip(context.input_signatures.iter().cloned())
        .chain(context.associated_signatures.iter().cloned())
        .collect::<FxHashMap<_, _>>();
    substitute_signature_vars(&requirement.signature, &substitutions)
}

fn lower_impl_requirement_role_constraint(
    lowerer: &mut SignatureLowerer<'_>,
    requirement: &ResolvedRoleMethodRequirement,
) -> Result<RoleConstraint, LoweringError> {
    let inputs = requirement
        .inputs
        .iter()
        .map(|signature| {
            lowerer
                .lower_role_arg(signature)
                .map_err(|error| LoweringError::SignatureConstraint { error })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let associated = requirement
        .associated
        .iter()
        .map(|(name, signature)| {
            lowerer
                .lower_role_arg(signature)
                .map(|value| RoleAssociatedConstraint {
                    name: name.clone(),
                    value,
                })
                .map_err(|error| LoweringError::SignatureConstraint { error })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(RoleConstraint {
        role: requirement.role.clone(),
        inputs,
        associated,
    })
}

fn substitute_signature_vars(
    signature: &SignatureType,
    substitutions: &FxHashMap<String, SignatureType>,
) -> SignatureType {
    match signature {
        SignatureType::Builtin(_) | SignatureType::Named(_) => signature.clone(),
        SignatureType::Var(var) => substitutions
            .get(&var.name)
            .cloned()
            .unwrap_or_else(|| signature.clone()),
        SignatureType::EffectRow(row) => {
            SignatureType::EffectRow(substitute_signature_effect_row(row, substitutions))
        }
        SignatureType::Effectful { eff, ret } => SignatureType::Effectful {
            eff: substitute_signature_effect_row(eff, substitutions),
            ret: Box::new(substitute_signature_vars(ret, substitutions)),
        },
        SignatureType::Tuple(items) => SignatureType::Tuple(
            items
                .iter()
                .map(|item| substitute_signature_vars(item, substitutions))
                .collect(),
        ),
        SignatureType::Apply { callee, args } => SignatureType::Apply {
            callee: Box::new(substitute_signature_vars(callee, substitutions)),
            args: args
                .iter()
                .map(|arg| substitute_signature_vars(arg, substitutions))
                .collect(),
        },
        SignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => SignatureType::Function {
            param: Box::new(substitute_signature_vars(param, substitutions)),
            arg_eff: arg_eff
                .as_ref()
                .map(|row| substitute_signature_effect_row(row, substitutions)),
            ret_eff: ret_eff
                .as_ref()
                .map(|row| substitute_signature_effect_row(row, substitutions)),
            ret: Box::new(substitute_signature_vars(ret, substitutions)),
        },
    }
}

fn substitute_signature_effect_row(
    row: &SignatureEffectRow,
    substitutions: &FxHashMap<String, SignatureType>,
) -> SignatureEffectRow {
    SignatureEffectRow {
        items: row
            .items
            .iter()
            .map(|atom| match atom {
                SignatureEffectAtom::Type(ty) => {
                    SignatureEffectAtom::Type(substitute_signature_vars(ty, substitutions))
                }
                SignatureEffectAtom::Wildcard => SignatureEffectAtom::Wildcard,
            })
            .collect(),
        tail: row
            .tail
            .as_ref()
            .map(|tail| match substitutions.get(&tail.name) {
                Some(SignatureType::Var(var)) => var.clone(),
                _ => tail.clone(),
            }),
    }
}

fn signature_vars_from_ann_vars(
    bindings: &[(String, AnnTypeVarId)],
    vars: &FxHashMap<AnnTypeVarId, TypeVar>,
) -> FxHashMap<String, TypeVar> {
    bindings
        .iter()
        .filter_map(|(name, id)| vars.get(id).copied().map(|var| (name.clone(), var)))
        .collect()
}

fn impl_head_type_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)
}

fn impl_description_type_expr(node: &Cst) -> Option<Cst> {
    crate::child_node(node, SyntaxKind::ImplDescription)?
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)
}

fn role_impl_associated_type_exprs(node: &Cst) -> FxHashMap<String, Cst> {
    let mut out = FxHashMap::default();
    collect_role_impl_associated_type_exprs(node, &mut out);
    out
}

fn collect_role_impl_associated_type_exprs(node: &Cst, out: &mut FxHashMap<String, Cst>) {
    for child in node.children() {
        match child.kind() {
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup => {
                collect_role_impl_associated_type_exprs(&child, out);
            }
            SyntaxKind::TypeDecl => {
                let Some(name) = crate::type_decl_name(&child) else {
                    continue;
                };
                let Some(type_expr) = type_decl_rhs_type_expr(&child) else {
                    continue;
                };
                out.insert(name.0, type_expr);
            }
            _ => {}
        }
    }
}

fn type_decl_rhs_type_expr(node: &Cst) -> Option<Cst> {
    let mut after_equal = false;
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Equal => {
                after_equal = true;
            }
            NodeOrToken::Node(child) if after_equal && child.kind() == SyntaxKind::TypeExpr => {
                return Some(child);
            }
            NodeOrToken::Node(child)
                if after_equal
                    && matches!(
                        child.kind(),
                        SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
                    ) =>
            {
                return child
                    .children()
                    .find(|child| child.kind() == SyntaxKind::TypeExpr);
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower_module_map;
    use crate::scc::SccEvent;
    use poly::expr::{
        DefId, ExprId, Pat, PrimitiveOp, RecordSpread, RefId, SelectId, SelectResolution, Vis,
    };

    fn parse(src: &str) -> Cst {
        SyntaxNode::new_root(yulang_parser::parse_module_to_green(src))
    }

    fn parse_with_junction_std(src: &str) -> Cst {
        parse(&format!(
            "mod std:\n  pub mod control:\n    pub mod junction:\n      pub mod junction:\n        pub junction x = x\n{src}"
        ))
    }

    fn parse_with_text_parse_std(src: &str) -> Cst {
        parse(&format!(
            "mod std:\n  pub mod text:\n    pub mod parse:\n      pub token expected = expected\n      pub word() = 0\n      pub choice p q = p\n      pub many p = p\n      pub some p = p\n      pub optional p = p\n{src}"
        ))
    }

    fn parse_with_flow_loop_std(src: &str) -> Cst {
        parse(&format!(
            "mod std:\n  pub mod control:\n    pub mod flow:\n      pub act loop:\n        pub for_in xs f = f xs\n{src}"
        ))
    }

    fn parse_with_flow_loop_and_label_std(src: &str) -> Cst {
        parse(&format!(
            concat!(
                "mod std:\n",
                "  pub mod control:\n",
                "    pub mod flow:\n",
                "      pub act loop:\n",
                "        pub for_in xs f = f xs\n",
                "      pub act label_loop:\n",
                "        pub label = 0\n",
                "        pub for_in xs f = f label xs\n",
                "{}"
            ),
            src
        ))
    }

    fn parse_with_text_str_std(src: &str) -> Cst {
        parse(&format!(
            "mod std:\n  pub mod text:\n    pub mod str:\n      pub concat a b = a\n{src}"
        ))
    }

    fn parse_with_text_str_and_format_std(src: &str) -> Cst {
        let mut full = concat!(
            "mod std:\n",
            "  pub mod data:\n",
            "    pub mod opt:\n",
            "      pub enum opt 'a = nil | just 'a\n",
            "  pub mod core:\n",
            "    pub mod fmt:\n",
            "      use std::data::opt::*\n",
            "      pub enum format_kind = display | debug | lower_hex | upper_hex\n",
            "      pub enum format_align = left | right | center\n",
            "      pub enum format_sign = plus | minus\n",
            "      pub struct format_spec {\n",
            "        kind: format_kind,\n",
            "        align: opt format_align,\n",
            "        sign: opt format_sign,\n",
            "        fill: opt str,\n",
            "        width: opt int,\n",
            "        precision: opt int,\n",
            "        alternate: bool,\n",
            "        zero_pad: bool,\n",
            "      }\n",
            "      pub format_display spec value = value\n",
            "      pub format_debug spec value = value\n",
            "      pub format_lower_hex spec value = value\n",
            "      pub format_upper_hex spec value = value\n",
            "  pub mod text:\n",
            "    pub mod str:\n",
            "      pub concat a b = a\n",
        )
        .to_string();
        full.push_str(src);
        parse(&full)
    }

    fn binding_expr(root: &Cst, name: &str) -> Cst {
        binding_node(root, name)
            .and_then(|binding| binding_body_expr(&binding))
            .expect("binding body expr")
    }

    fn binding_node(root: &Cst, name: &str) -> Option<Cst> {
        root.children().find(|child| {
            child.kind() == SyntaxKind::Binding && binding_name(child).as_deref() == Some(name)
        })
    }

    fn binding_name(binding: &Cst) -> Option<String> {
        binding
            .children()
            .find(|child| child.kind() == SyntaxKind::BindingHeader)?
            .children()
            .find(|child| child.kind() == SyntaxKind::Pattern)?
            .children_with_tokens()
            .filter_map(|item| item.into_token())
            .find(|token| token.kind() == SyntaxKind::Ident)
            .map(|token| token.text().to_string())
    }

    fn binding_def_and_order(
        modules: &ModuleTable,
        module: ModuleId,
        name: &str,
    ) -> (DefId, ModuleOrder) {
        let decl = modules.value_decls(module, &Name(name.into()))[0].clone();
        (decl.def, decl.order)
    }

    fn std_junction_def(modules: &ModuleTable) -> DefId {
        let path = crate::std_paths::control_junction_value()
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        modules
            .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
            .expect("std junction value")
    }

    fn text_parse_def(modules: &ModuleTable, name: &str) -> DefId {
        let path = crate::std_paths::text_parse_value(name)
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        modules
            .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
            .unwrap_or_else(|| panic!("std text parse value {name}"))
    }

    fn control_flow_loop_for_in_def(modules: &ModuleTable) -> DefId {
        let path = crate::std_paths::control_flow_loop_for_in_value()
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        modules
            .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
            .expect("std control flow loop for_in")
    }

    fn control_flow_label_loop_for_in_def(modules: &ModuleTable) -> DefId {
        let path = crate::std_paths::control_flow_label_loop_for_in_value()
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        modules
            .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
            .expect("std control flow label_loop for_in")
    }

    fn text_str_concat_def(modules: &ModuleTable) -> DefId {
        let path = crate::std_paths::text_str_concat_value()
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        modules
            .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
            .expect("std text str concat")
    }

    fn core_fmt_def(modules: &ModuleTable, name: &str) -> DefId {
        let path = crate::std_paths::core_fmt_value(name)
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        modules
            .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
            .unwrap_or_else(|| panic!("std core fmt value {name}"))
    }

    fn core_fmt_format_sign_def(modules: &ModuleTable, name: &str) -> DefId {
        let path = crate::std_paths::core_fmt_format_sign_value(name)
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        modules
            .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
            .unwrap_or_else(|| panic!("std core fmt format_sign value {name}"))
    }

    fn assert_junction_app(session: &AnalysisSession, expr: ExprId, junction: DefId) -> ExprId {
        match session.poly.expr(expr) {
            Expr::App(callee, arg) => {
                let reference = expr_ref(session, *callee);
                assert_eq!(session.poly.ref_target(reference), Some(junction));
                *arg
            }
            _ => panic!("expected junction application"),
        }
    }

    fn binding_body_id(output: &BodyLowering, def: DefId) -> ExprId {
        match output.session.poly.defs.get(def) {
            Some(Def::Let {
                body: Some(body), ..
            }) => *body,
            _ => panic!("expected lowered let body"),
        }
    }

    fn def_scheme(output: &BodyLowering, def: DefId) -> &poly::types::Scheme {
        match output.session.poly.defs.get(def) {
            Some(Def::Let {
                scheme: Some(scheme),
                ..
            }) => scheme,
            _ => panic!("expected def scheme"),
        }
    }

    fn build_neg_signature_field_type(
        src: &str,
        type_name: &str,
        field_name: &str,
    ) -> SignatureType {
        let root = parse(src);
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let expected_type_name = Name(type_name.into());
        let expected_field_name = Name(field_name.into());
        let owner_decl = lower.modules.type_decls(module, &expected_type_name)[0].clone();
        let struct_decl = root
            .children()
            .find(|child| {
                child.kind() == SyntaxKind::StructDecl
                    && crate::type_decl_name(child).as_ref() == Some(&expected_type_name)
            })
            .expect("struct declaration should exist");
        let type_vars = crate::type_var_names(&struct_decl);
        let type_expr = crate::struct_field_nodes(&struct_decl)
            .into_iter()
            .find(|field| crate::struct_field_name(field).as_ref() == Some(&expected_field_name))
            .and_then(|field| crate::field_type_expr(&field))
            .expect("field should contain a type expression");
        let builder = NegSignatureBuilder::with_self_alias(
            &lower.modules,
            module,
            owner_decl.order,
            SignatureSelfAlias {
                owner: owner_decl.id,
                type_vars,
            },
        );
        builder
            .build_type_expr(&type_expr)
            .expect("negative signature should build")
            .signature
    }

    #[test]
    fn neg_signature_builder_preserves_effect_row_tail_for_data_representation() {
        let signature = build_neg_signature_field_type(
            "act ref_update 'a;\nstruct Box 'e 'a { update_effect: () -> [ref_update 'a; 'e] () }\n",
            "Box",
            "update_effect",
        );

        let SignatureType::Function {
            param,
            ret_eff: Some(row),
            ret,
            ..
        } = signature
        else {
            panic!("expected function signature with return effect row");
        };

        assert!(matches!(*param, SignatureType::Builtin(BuiltinType::Unit)));
        assert!(matches!(*ret, SignatureType::Builtin(BuiltinType::Unit)));
        assert_eq!(row.tail, Some(SignatureVar { name: "e".into() }));
        let [SignatureEffectAtom::Type(effect)] = row.items.as_slice() else {
            panic!("expected one concrete effect atom");
        };
        let SignatureType::Apply { callee, args } = effect else {
            panic!("expected parameterized effect atom");
        };
        assert!(matches!(callee.as_ref(), SignatureType::Named(_)));
        assert_eq!(
            args,
            &vec![SignatureType::Var(SignatureVar { name: "a".into() })]
        );
    }

    #[test]
    fn struct_constructor_field_signature_records_data_tail_stack() {
        let root = parse(
            "act ref_update 'a;\nstruct Box 'e 'a { update_effect: () -> [ref_update 'a; 'e] () }\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let constructor = lower.modules.value_decls(module, &Name("Box".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let update_effect = constructor_record_field_var(&output, constructor, "update_effect");
        let (items, tail) = function_upper_bound_ret_effect_row(&output.session, update_effect);
        assert!(items.iter().any(|item| {
            matches!(
                output.session.infer.constraints().types().neg(*item),
                Neg::Con(path, args) if path == &vec!["ref_update".to_string()] && args.len() == 1
            )
        }));
        let types = output.session.infer.constraints().types();
        let Neg::Stack { inner, weight } = types.neg(tail) else {
            panic!(
                "expected stacked return effect row tail, got {:?}",
                types.neg(tail)
            );
        };
        assert!(matches!(types.neg(*inner), Neg::Var(_)));
        assert!(weight_has_all_except_path(weight, &["ref_update"]));
    }

    fn assert_method_body_is_receiver_identity(output: &BodyLowering, method: DefId) {
        let body = binding_body_id(output, method);
        let (pat, body) = match output.session.poly.expr(body) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected method receiver lambda"),
        };
        let receiver = match output.session.poly.pat(pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected receiver var pattern"),
        };
        let reference = expr_ref(&output.session, body);

        assert_eq!(output.session.poly.ref_target(reference), Some(receiver));
    }

    fn assert_act_method_receiver_has_self_subtract(
        output: &BodyLowering,
        method: DefId,
        effect_name: &str,
    ) {
        let root = output
            .typing
            .def(method)
            .expect("method def should have a root type");
        let (_, arg_eff, ret_eff, ret) = function_lower_bound(&output.session, root);
        let effect = match output.session.infer.constraints().types().neg(arg_eff) {
            Neg::Var(effect) => *effect,
            other => panic!("expected receiver arg effect var, got {other:?}"),
        };
        // act receiver の保護は fresh な内側変数の push 付き下界として入る。self edge にはしない。
        let bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(effect)
            .expect("receiver effect should receive stacked inner lower bound");
        let subtract = bounds
            .lowers()
            .iter()
            .find_map(|bound| {
                if !matches!(
                    output.session.infer.constraints().types().pos(bound.pos),
                    Pos::Var(var) if *var != effect
                ) {
                    return None;
                }
                weight_set_path_id(&bound.weights.left, &[effect_name])
            })
            .expect("receiver effect should record stacked act family");
        assert_pos_stack_pop_var(&output.session, ret_eff, subtract);
        assert_pos_stack_pop_var(&output.session, ret, subtract);
    }

    fn function_lower_bound(
        session: &AnalysisSession,
        var: TypeVar,
    ) -> (NegId, NegId, PosId, PosId) {
        let mut stack = vec![var];
        let mut visited = Vec::new();
        while let Some(var) = stack.pop() {
            if visited.contains(&var) {
                continue;
            }
            visited.push(var);
            let Some(bounds) = session.infer.constraints().bounds().of(var) else {
                continue;
            };
            for lower in bounds.lowers() {
                match session.infer.constraints().types().pos(lower.pos) {
                    Pos::Fun {
                        arg,
                        arg_eff,
                        ret_eff,
                        ret,
                    } => return (*arg, *arg_eff, *ret_eff, *ret),
                    Pos::Var(next) => stack.push(*next),
                    _ => {}
                }
            }
        }
        panic!("expected function lower bound");
    }

    fn constructor_record_field_var(
        output: &BodyLowering,
        constructor: DefId,
        field_name: &str,
    ) -> TypeVar {
        let root = output
            .typing
            .def(constructor)
            .expect("constructor def should have a root type");
        let (arg, _, _, _) = function_lower_bound(&output.session, root);
        let Neg::Var(record) = output.session.infer.constraints().types().neg(arg) else {
            panic!("expected constructor record argument var");
        };
        let Some(bounds) = output.session.infer.constraints().bounds().of(*record) else {
            panic!("expected record argument bounds");
        };
        for upper in bounds.uppers() {
            let Neg::Record(fields) = output.session.infer.constraints().types().neg(upper.neg)
            else {
                continue;
            };
            let Some(field) = fields.iter().find(|field| field.name == field_name) else {
                continue;
            };
            let Neg::Var(value) = output.session.infer.constraints().types().neg(field.value)
            else {
                panic!("expected constructor field value var");
            };
            return *value;
        }
        panic!("expected constructor record field {field_name}");
    }

    fn function_upper_bound_ret_effect_row(
        session: &AnalysisSession,
        var: TypeVar,
    ) -> (Vec<NegId>, NegId) {
        let Some(bounds) = session.infer.constraints().bounds().of(var) else {
            panic!("expected function upper bound");
        };
        for upper in bounds.uppers() {
            let Neg::Fun { ret_eff, .. } = session.infer.constraints().types().neg(upper.neg)
            else {
                continue;
            };
            let Neg::Row(items, tail) = session.infer.constraints().types().neg(*ret_eff) else {
                panic!("expected function return effect row");
            };
            return (items.clone(), *tail);
        }
        panic!("expected function upper bound");
    }

    fn type_field_method(
        modules: &ModuleTable,
        owner: TypeDeclId,
        name: &str,
        receiver_kind: TypeMethodReceiver,
    ) -> TypeFieldMethodDecl {
        modules
            .type_field_methods(owner)
            .iter()
            .find(|method| method.name.0 == name && method.receiver_kind == receiver_kind)
            .cloned()
            .expect("type field method should be registered")
    }

    fn assert_pos_stack_pop_var(
        session: &AnalysisSession,
        pos: PosId,
        subtract: SubtractId,
    ) -> TypeVar {
        let Pos::Stack { inner, weight } = session.infer.constraints().types().pos(pos) else {
            panic!("expected stack pop #{:?}", subtract);
        };
        let [entry] = weight.entries() else {
            panic!("expected one stack entry, got {:?}", weight.entries());
        };
        assert_eq!(entry.id, subtract);
        assert_eq!(entry.pops, 1);
        assert!(entry.stack.is_empty());
        match session.infer.constraints().types().pos(*inner) {
            Pos::Var(var) => *var,
            other => panic!("expected stack pop inner var, got {other:?}"),
        }
    }

    fn weight_set_path_id(weight: &StackWeight, expected: &[&str]) -> Option<SubtractId> {
        weight.entries().iter().find_map(|entry| {
            if entry.stack.iter().any(|subtractability| {
                matches!(
                    subtractability,
                    Subtractability::Set(path, args)
                        if path_matches(path, expected) && args.is_empty()
                )
            }) {
                Some(entry.id)
            } else {
                None
            }
        })
    }

    fn weight_has_all_except_path(weight: &StackWeight, expected: &[&str]) -> bool {
        weight.entries().iter().any(|entry| {
            entry.stack.iter().any(|subtractability| {
                matches!(
                    subtractability,
                    Subtractability::AllExcept(path, args)
                        if path_matches(path, expected) && args.is_empty()
                )
            })
        })
    }

    fn weight_has_empty_stack(weight: &StackWeight, subtract: SubtractId) -> bool {
        weight.entries().iter().any(|entry| {
            entry.id == subtract
                && entry.pops == 0
                && entry
                    .stack
                    .iter()
                    .any(|subtractability| matches!(subtractability, Subtractability::Empty))
        })
    }

    fn path_matches(path: &[String], expected: &[&str]) -> bool {
        path.iter().map(String::as_str).eq(expected.iter().copied())
    }

    #[test]
    fn struct_constructor_lowers_to_scheme() {
        let root = parse("struct Box 'a { value: 'a }\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let constructor = lower.modules.value_decls(module, &Name("Box".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let scheme = def_scheme(&output, constructor);
        assert_eq!(scheme.quantifiers.len(), 1);
        let Pos::Fun { ret, .. } = output.session.poly.typ.pos(scheme.predicate) else {
            panic!("expected unary constructor function");
        };
        let Pos::Con(path, args) = output.session.poly.typ.pos(*ret) else {
            panic!("expected constructor return type");
        };
        assert_eq!(path, &vec!["Box".to_string()]);
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn type_with_self_struct_lowers_outer_constructor_scheme() {
        let root = parse("type t 'a with:\n  struct self:\n    field: 'a\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let constructor = lower.modules.value_decls(module, &Name("t".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let scheme = def_scheme(&output, constructor);
        assert_eq!(scheme.quantifiers.len(), 1);
        let Pos::Fun { ret, .. } = output.session.poly.typ.pos(scheme.predicate) else {
            panic!("expected self struct constructor function");
        };
        let Pos::Con(path, args) = output.session.poly.typ.pos(*ret) else {
            panic!("expected outer type constructor return");
        };
        assert_eq!(path, &vec!["t".to_string()]);
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn enum_variant_constructor_lowers_to_scheme() {
        let root = parse("enum opt 'a = none | some 'a\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let opt = lower.modules.type_decls(module, &Name("opt".into()))[0].id;
        let companion = lower.modules.type_companion(opt).expect("opt companion");
        let none = lower.modules.value_decls(companion, &Name("none".into()))[0].def;
        let some = lower.modules.value_decls(companion, &Name("some".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let none_scheme = def_scheme(&output, none);
        let Pos::Con(path, args) = output.session.poly.typ.pos(none_scheme.predicate) else {
            panic!("expected nullary enum constructor value");
        };
        assert_eq!(path, &vec!["opt".to_string()]);
        assert_eq!(args.len(), 1);

        let some_scheme = def_scheme(&output, some);
        let Pos::Fun { ret, .. } = output.session.poly.typ.pos(some_scheme.predicate) else {
            panic!("expected unary enum constructor function");
        };
        let Pos::Con(path, args) = output.session.poly.typ.pos(*ret) else {
            panic!("expected enum constructor return type");
        };
        assert_eq!(path, &vec!["opt".to_string()]);
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn enum_constructor_expression_resolves_reference() {
        let root = parse("enum opt 'a = some 'a\nmy x = opt::some 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let opt = lower.modules.type_decls(module, &Name("opt".into()))[0].id;
        let companion = lower.modules.type_companion(opt).expect("opt companion");
        let constructor = lower.modules.value_decls(companion, &Name("some".into()))[0].def;
        let (x, _) = binding_def_and_order(&lower.modules, module, "x");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, x);
        let Expr::App(callee, _) = output.session.poly.expr(body) else {
            panic!("expected constructor application");
        };
        let reference = expr_ref(&output.session, *callee);
        assert_eq!(output.session.poly.ref_target(reference), Some(constructor));
    }

    #[test]
    fn declared_constructor_expression_spaced_tuple_group_matches_payload_fields() {
        let root = parse(concat!(
            "pub enum bound = unbounded | included int\n",
            "pub enum range = within (bound, bound)\n",
            "my mk(start: bound, end: bound): range = range::within (start, end)\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (mk, _) = binding_def_and_order(&lower.modules, module, "mk");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, mk));
        assert_eq!(rendered, "bound -> bound -> range");
    }

    #[test]
    fn lowers_int_literal_with_primitive_lower_bound() {
        let root = parse("my a = 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "a");
        let expr = binding_expr(&root, "a");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        assert!(matches!(
            session.poly.expr(computation.expr),
            Expr::Lit(Lit::Int(1))
        ));
        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(computation.value)
            .expect("literal value should receive a lower bound");
        assert!(bounds.lowers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().pos(bound.pos),
                Pos::Con(path, args) if path == &vec!["int".to_string()] && args.is_empty()
            )
        }));
    }

    #[test]
    fn binding_annotation_constrains_def_above_body() {
        let root = parse("my a: float = 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (def, _) = binding_def_and_order(&lower.modules, module, "a");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let root = output.typing.def(def).expect("def should have a root type");
        assert!(matches!(
            output.session.poly.expr(binding_body_id(&output, def)),
            Expr::Lit(Lit::Int(_))
        ));
        let body = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(root)
            .expect("root should receive bounds")
            .lowers()
            .iter()
            .find_map(
                |bound| match output.session.infer.constraints().types().pos(bound.pos) {
                    Pos::Var(body) => Some(*body),
                    _ => None,
                },
            )
            .expect("body should flow into def root");

        let types = output.session.infer.constraints().types();
        let root_bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(root)
            .expect("root should receive bounds");
        assert!(root_bounds.uppers().iter().any(|bound| {
            matches!(
                types.neg(bound.neg),
                Neg::Con(path, args) if path == &vec!["float".to_string()] && args.is_empty()
            )
        }));

        let body_bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(body)
            .expect("body should receive bounds");
        assert!(
            body_bounds
                .uppers()
                .iter()
                .any(|bound| { matches!(types.neg(bound.neg), Neg::Var(var) if *var == root) })
        );
    }

    #[test]
    fn binding_header_arg_lowers_to_lambda_and_local_ref() {
        let root = parse("my id x = x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (def, _) = binding_def_and_order(&lower.modules, module, "id");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, def);
        let (pat, lambda_body) = match output.session.poly.expr(body) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected header arg lambda"),
        };
        let arg = match output.session.poly.pat(pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected arg var pattern"),
        };
        let reference = expr_ref(&output.session, lambda_body);
        assert_eq!(output.session.poly.ref_target(reference), Some(arg));
    }

    #[test]
    fn binding_header_arg_annotation_constrains_arg_not_def() {
        let root = parse("my f(x: int) = x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (def, _) = binding_def_and_order(&lower.modules, module, "f");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, def);
        let lambda_body = match output.session.poly.expr(body) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected header arg lambda"),
        };
        let reference = expr_ref(&output.session, lambda_body);
        let arg_value = output
            .session
            .refs
            .value(reference)
            .expect("arg ref should have a value slot");
        let types = output.session.infer.constraints().types();
        let arg_bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(arg_value)
            .expect("arg annotation should constrain arg value");
        assert!(arg_bounds.lowers().iter().any(|bound| {
            matches!(
                types.pos(bound.pos),
                Pos::Con(path, args) if path == &vec!["int".to_string()] && args.is_empty()
            )
        }));

        let root = output.typing.def(def).expect("def should have a root type");
        let root_bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(root)
            .expect("def root should receive bounds");
        assert!(!root_bounds.uppers().iter().any(|bound| {
            matches!(
                types.neg(bound.neg),
                Neg::Con(path, args) if path == &vec!["int".to_string()] && args.is_empty()
            )
        }));
    }

    #[test]
    fn binding_header_result_annotation_constrains_body_not_def() {
        let root = parse("my f(x: int): float = 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (def, _) = binding_def_and_order(&lower.modules, module, "f");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let root = output.typing.def(def).expect("def should have a root type");
        let (_, _, _, ret) = function_lower_bound(&output.session, root);
        let ret_value = match output.session.infer.constraints().types().pos(ret) {
            Pos::Var(var) => *var,
            _ => panic!("expected function return value var"),
        };
        let types = output.session.infer.constraints().types();
        let ret_bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(ret_value)
            .expect("result annotation should constrain body value");
        assert!(ret_bounds.uppers().iter().any(|bound| {
            matches!(
                types.neg(bound.neg),
                Neg::Con(path, args) if path == &vec!["float".to_string()] && args.is_empty()
            )
        }));

        let root_bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(root)
            .expect("def root should receive bounds");
        assert!(!root_bounds.uppers().iter().any(|bound| {
            matches!(
                types.neg(bound.neg),
                Neg::Con(path, args) if path == &vec!["float".to_string()] && args.is_empty()
            )
        }));
    }

    #[test]
    fn role_impl_head_and_colon_description_register_same_candidate_shape() {
        let root = parse("role Eq 'a;\nimpl Eq int;\nimpl int: Eq;\n");
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let candidates = output.session.role_impls.candidates(&["Eq".to_string()]);
        assert_eq!(candidates.len(), 2);
        for candidate in candidates {
            assert_eq!(candidate.inputs.len(), 1);
            assert_role_arg_is_exact_con(&output.session, &candidate.inputs[0], "int");
        }
    }

    #[test]
    fn role_impl_prefix_and_colon_description_register_same_multi_input_shape() {
        for impl_head in ["impl Index lines int:", "impl lines: Index int:"] {
            let root = parse(&format!(
                concat!(
                    "struct lines;\n",
                    "role Index 'container 'key:\n",
                    "  type value\n",
                    "  our x.index: 'key -> value\n",
                    "{impl_head}\n",
                    "  type value = lines\n",
                    "  our x.index i = x\n",
                ),
                impl_head = impl_head,
            ));
            let lower = lower_module_map(&root);

            let output = lower_binding_bodies(&root, lower);

            assert!(output.errors.is_empty(), "{:?}", output.errors);
            let candidates = output.session.role_impls.candidates(&["Index".to_string()]);
            assert_eq!(candidates.len(), 1, "{impl_head}");
            let candidate = &candidates[0];
            assert_eq!(candidate.inputs.len(), 2);
            assert_role_arg_is_exact_con(&output.session, &candidate.inputs[0], "lines");
            assert_role_arg_is_exact_con(&output.session, &candidate.inputs[1], "int");
        }
    }

    #[test]
    fn role_impl_method_receiver_is_constrained_to_impl_target() {
        let root = parse(
            "struct User;\nrole Box 'a:\n  our x.get: 'a\nimpl User: Box {\n  our x.get = x\n}\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let method = lower.modules.role_impls(module)[0].methods[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, method);
        let lambda_body = match output.session.poly.expr(body) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected impl method receiver lambda"),
        };
        let reference = expr_ref(&output.session, lambda_body);
        let receiver_value = output
            .session
            .refs
            .value(reference)
            .expect("receiver ref should have a value slot");
        assert_var_has_exact_con_bound(&output.session, receiver_value, "User");
    }

    #[test]
    fn role_impl_method_requirement_rejects_concrete_return_mismatch() {
        let root = parse(
            "struct User;\nrole Box 'a:\n  our x.get: int\nimpl User: Box {\n  our x.get = x\n}\n",
        );
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.iter().any(|error| {
            matches!(
                error,
                BodyLoweringError::Expr {
                    error: LoweringError::SignatureTypeMismatch {
                        expected: SignatureShape::Function,
                    },
                    ..
                }
            )
        }));
    }

    #[test]
    fn role_impl_method_requirement_clamps_associated_type_from_return() {
        let root = parse(
            "struct User;\nrole Box 'a:\n  type item\n  our x.get: item\nimpl User: Box {\n  our x.get = x\n}\n",
        );
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let candidates = output.session.role_impls.candidates(&["Box".to_string()]);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].associated.len(), 1);
        assert_eq!(candidates[0].associated[0].name, "item");
        let associated = candidates[0].associated[0].value;
        let associated_var = match output
            .session
            .infer
            .constraints()
            .types()
            .pos(associated.lower)
        {
            Pos::Var(var) => *var,
            other => panic!("expected associated lower var, got {other:?}"),
        };
        assert_var_has_lower_con_bound(&output.session, associated_var, "User");
    }

    #[test]
    fn role_impl_method_requirement_ret_effect_records_stack_weighted_upper() {
        let root = parse(
            "act nondet:\nstruct User;\nrole Box 'a:\n  our x.run: [nondet; 'e] unit\nimpl User: Box {\n  our x.run = ()\n}\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let method = lower.modules.role_impls(module)[0].methods[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let root = output.typing.def(method).expect("impl method root");
        let (_, _, ret_eff, _) = function_lower_bound(&output.session, root);
        let body_effect = match output.session.infer.constraints().types().pos(ret_eff) {
            Pos::Var(var) => *var,
            other => panic!("expected body effect var, got {other:?}"),
        };
        let bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(body_effect)
            .expect("body effect should be constrained by requirement");
        let types = output.session.infer.constraints().types();
        assert!(
            bounds.uppers().iter().any(|bound| {
                matches!(types.neg(bound.neg), Neg::Var(_))
                    && weight_set_path_id(&bound.weights.right, &["nondet"]).is_some()
            }),
            "body effect bounds: {:?}",
            bounds
        );
    }

    #[test]
    fn role_method_signature_arg_effect_lowers_to_neg_stack() {
        let root = parse("act nondet:\nrole Box 'a:\n  our x.run: unit [nondet; 'e] -> unit\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let role = lower.modules.type_decls(module, &Name("Box".into()))[0].clone();
        let method = lower.modules.role_methods(role.id)[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let root = output.typing.def(method).expect("role method root");
        let (_, _, _, ret) = function_lower_bound(&output.session, root);
        let arg_eff = match output.session.infer.constraints().types().pos(ret) {
            Pos::Fun { arg_eff, .. } => *arg_eff,
            other => panic!("expected inner function lower bound, got {other:?}"),
        };
        let Neg::Stack { inner, weight } = output.session.infer.constraints().types().neg(arg_eff)
        else {
            panic!(
                "expected stacked arg effect var, got {:?}",
                output.session.infer.constraints().types().neg(arg_eff)
            );
        };
        assert!(matches!(
            output.session.infer.constraints().types().neg(*inner),
            Neg::Var(_)
        ));
        assert!(weight_set_path_id(weight, &["nondet"]).is_some());
    }

    #[test]
    fn role_impl_method_requirement_checks_receiver_function_shape() {
        let root = parse(
            "struct User;\nrole Box 'a:\n  our x.get: unit\nimpl User: Box {\n  our get: unit = ()\n}\n",
        );
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.iter().any(|error| {
            matches!(
                error,
                BodyLoweringError::Expr {
                    error: LoweringError::SignatureShapeMismatch {
                        expected: SignatureShape::Function,
                    },
                    ..
                }
            )
        }));
    }

    #[test]
    fn role_impl_method_requirement_is_available_before_role_body_lowering() {
        let root = parse(
            "struct User;\nimpl User: Box {\n  our x.get = x\n}\nrole Box 'a:\n  type item\n  our x.get: item\n",
        );
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let candidates = output.session.role_impls.candidates(&["Box".to_string()]);
        assert_eq!(candidates.len(), 1);
        let associated = candidates[0].associated[0].value;
        let associated_var = match output
            .session
            .infer
            .constraints()
            .types()
            .pos(associated.lower)
        {
            Pos::Var(var) => *var,
            other => panic!("expected associated lower var, got {other:?}"),
        };
        assert_var_has_lower_con_bound(&output.session, associated_var, "User");
    }

    #[test]
    fn unresolved_role_impl_head_reports_lowering_error() {
        let root =
            parse("role Box 'a:\n  our x.get: 'a\nimpl Missing: Box {\n  our x.get = x\n}\n");
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.iter().any(|error| {
            matches!(
                error,
                BodyLoweringError::Expr {
                    error:
                        LoweringError::AnnotationBuild {
                            error: AnnBuildError::UnresolvedTypeName { path },
                        },
                    ..
                } if path == &vec![Name("Missing".into())]
            )
        }));
    }

    #[test]
    fn role_impl_member_residual_role_is_collected_as_impl_prerequisite() {
        let root = parse(
            "role Eq 'a:\n  our x.eq: unit\nrole Box 'a:\n  our x.get: unit\nimpl 'a: Box {\n  our x.get = x.eq\n}\n",
        );
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let candidates = output.session.role_impls.candidates(&["Box".to_string()]);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].prerequisites.len(), 1);
        assert_eq!(candidates[0].prerequisites[0].role, vec!["Eq".to_string()]);
        assert_eq!(candidates[0].prerequisites[0].inputs.len(), 1);
    }

    #[test]
    fn reference_lowering_queues_resolution_and_scc_edge() {
        let root = parse("my a = 1\nmy b = a\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (target, _) = binding_def_and_order(&lower.modules, module, "a");
        let (owner, site) = binding_def_and_order(&lower.modules, module, "b");
        let expr = binding_expr(&root, "b");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        let reference = match session.poly.expr(computation.expr) {
            Expr::Var(reference) => *reference,
            _ => panic!("expected var expr"),
        };

        assert_eq!(session.poly.ref_target(reference), None);
        session.drain_work();

        assert_eq!(session.poly.ref_target(reference), Some(target));
        assert_eq!(
            session.take_scc_events(),
            vec![SccEvent::ComponentEdgeAdded {
                from: vec![owner],
                to: vec![target]
            }]
        );
    }

    #[test]
    fn qualified_path_lowers_to_resolved_value_reference() {
        let root = parse("mod m:\n  pub x = 1\nmy y = m::x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let m = lower
            .modules
            .module_at(module, &Name("m".into()), ModuleOrder(0))
            .unwrap();
        let target = lower.modules.value_decls(m, &Name("x".into()))[0].def;
        let (owner, site) = binding_def_and_order(&lower.modules, module, "y");
        let expr = binding_expr(&root, "y");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        let reference = match session.poly.expr(computation.expr) {
            Expr::Var(reference) => *reference,
            _ => panic!("expected path expr to lower to var reference"),
        };

        assert_eq!(session.poly.ref_target(reference), None);
        session.drain_work();
        assert_eq!(session.poly.ref_target(reference), Some(target));
    }

    #[test]
    fn builtin_op_path_lowers_to_primitive_body() {
        let root = parse("pub add: int -> int -> int = builtin_op::int_add\nmy site = add\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let add = lower.modules.value_decls(module, &Name("add".into()))[0].def;
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert!(matches!(
            output.session.poly.expr(binding_body_id(&output, add)),
            Expr::PrimitiveOp(PrimitiveOp::IntAdd)
        ));
        let site_body = binding_body_id(&output, site);
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, site_body)),
            Some(add)
        );
    }

    #[test]
    fn yada_yada_syntax_lowers_to_primitive_never() {
        let root = parse("pub main = ...\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "main");
        let expr = binding_expr(&root, "main");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        assert!(matches!(
            session.poly.expr(computation.expr),
            Expr::PrimitiveOp(PrimitiveOp::YadaYada)
        ));
        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(computation.value)
            .expect("yada yada should constrain value");
        let types = session.infer.constraints().types();
        assert!(
            bounds
                .uppers()
                .iter()
                .any(|bound| matches!(types.neg(bound.neg), Neg::Bot))
        );
    }

    #[test]
    fn pipeline_lowers_lhs_as_first_rhs_argument() {
        let root = parse("my f = builtin_op::int_add\nmy x = 1\nmy y = 2\npub z = x | f y\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let f = lower.modules.value_decls(module, &Name("f".into()))[0].def;
        let x = lower.modules.value_decls(module, &Name("x".into()))[0].def;
        let y = lower.modules.value_decls(module, &Name("y".into()))[0].def;
        let z = lower.modules.value_decls(module, &Name("z".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let (outer_callee, outer_arg) = match output.session.poly.expr(binding_body_id(&output, z))
        {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected outer app"),
        };
        let (inner_callee, inner_arg) = match output.session.poly.expr(outer_callee) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected inner app"),
        };
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, inner_callee)),
            Some(f)
        );
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, inner_arg)),
            Some(x)
        );
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, outer_arg)),
            Some(y)
        );
    }

    #[test]
    fn rule_lit_lowers_plain_text_to_text_parse_token() {
        let root = parse_with_text_parse_std("pub main = ~\"hello\"\n");
        let lower = lower_module_map(&root);
        let token = text_parse_def(&lower.modules, "token");
        let module = lower.modules.root_id();
        let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let (callee, arg) = match output.session.poly.expr(binding_body_id(&output, main)) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected token application"),
        };
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, callee)),
            Some(token)
        );
        assert!(
            matches!(output.session.poly.expr(arg), Expr::Lit(Lit::Str(text)) if text == "hello")
        );
    }

    #[test]
    fn rule_expr_wraps_sequence_in_unit_lambda() {
        let root = parse_with_text_parse_std("pub main = rule { \"a\" }\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let (pat, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected rule expr lambda"),
        };
        assert!(matches!(output.session.poly.pat(pat), Pat::Lit(Lit::Unit)));
        let (stmts, tail) = match output.session.poly.expr(body) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected rule sequence block"),
        };
        assert_eq!(stmts.len(), 1);
        assert!(matches!(stmts[0], Stmt::Expr(_)));
        assert!(matches!(
            output.session.poly.expr(tail),
            Expr::Lit(Lit::Unit)
        ));
    }

    #[test]
    fn rule_lit_lazy_capture_builds_record_parser() {
        let root = parse_with_text_parse_std("pub main = ~\"users/:id\"\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
            Expr::Lambda(pat, body) => {
                assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
                (*pat, *body)
            }
            _ => panic!("expected rule literal lambda"),
        };
        let (stmts, tail) = match output.session.poly.expr(body) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected rule literal block"),
        };
        assert_eq!(stmts.len(), 2);
        assert!(matches!(stmts[0], Stmt::Expr(_)));
        assert!(matches!(stmts[1], Stmt::Let(..)));
        match output.session.poly.expr(tail) {
            Expr::Record {
                fields,
                spread: RecordSpread::None,
            } => {
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0, "id");
            }
            _ => panic!("expected capture record"),
        }
    }

    #[test]
    fn rule_lit_interp_runs_parser_without_capture() {
        let root = parse_with_text_parse_std(
            "my id = std::text::parse::word\npub main = ~\"users/{id}\"\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let id = lower.modules.value_decls(module, &Name("id".into()))[0].def;
        let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
            Expr::Lambda(pat, body) => {
                assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
                (*pat, *body)
            }
            _ => panic!("expected rule literal lambda"),
        };
        let (stmts, tail) = match output.session.poly.expr(body) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected rule literal block"),
        };
        assert_eq!(stmts.len(), 2);
        let parser_run = match &stmts[1] {
            Stmt::Expr(expr) => *expr,
            _ => panic!("expected parser interpolation statement"),
        };
        let (callee, _unit) = match output.session.poly.expr(parser_run) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected parser interpolation application"),
        };
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, callee)),
            Some(id)
        );
        assert!(matches!(
            output.session.poly.expr(tail),
            Expr::Lit(Lit::Unit)
        ));
    }

    #[test]
    fn rule_lit_interp_capture_builds_record_parser() {
        let root = parse_with_text_parse_std(
            "my ident = std::text::parse::word\npub main = ~\"users/{id = ident}/posts\"\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let ident = lower.modules.value_decls(module, &Name("ident".into()))[0].def;
        let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
            Expr::Lambda(pat, body) => {
                assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
                (*pat, *body)
            }
            _ => panic!("expected rule literal lambda"),
        };
        let (stmts, tail) = match output.session.poly.expr(body) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected rule literal block"),
        };
        assert_eq!(stmts.len(), 3);
        let captured_expr = match &stmts[1] {
            Stmt::Let(_, _, expr) => *expr,
            _ => panic!("expected interpolation capture statement"),
        };
        let (callee, _unit) = match output.session.poly.expr(captured_expr) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected capture parser application"),
        };
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, callee)),
            Some(ident)
        );
        match output.session.poly.expr(tail) {
            Expr::Record {
                fields,
                spread: RecordSpread::None,
            } => {
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0, "id");
            }
            _ => panic!("expected interpolation capture record"),
        }
    }

    #[test]
    fn rule_expr_alternation_uses_text_parse_choice() {
        let root = parse_with_text_parse_std("pub main = rule { \"a\" | \"b\" }\n");
        let lower = lower_module_map(&root);
        let choice = text_parse_def(&lower.modules, "choice");
        let module = lower.modules.root_id();
        let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
            Expr::Lambda(pat, body) => {
                assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
                (*pat, *body)
            }
            _ => panic!("expected rule expr lambda"),
        };
        let (partial, _right) = match output.session.poly.expr(body) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected choice second application"),
        };
        let (choice_ref, _left) = match output.session.poly.expr(partial) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected choice first application"),
        };
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, choice_ref)),
            Some(choice)
        );
    }

    #[test]
    fn rule_quantifier_lowers_tail_base_exprs() {
        let root = parse_with_text_parse_std(concat!(
            "my parsers = {word: std::text::parse::word}\n",
            "my id x = x\n",
            "pub field_base = rule { parsers.word* }\n",
            "pub call_base = rule { id(std::text::parse::word)+ }\n",
        ));
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
    }

    #[test]
    fn rule_lazy_quantifier_reports_quantifier_unsupported() {
        let root = parse_with_text_parse_std("pub main = rule { a*? }\n");
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.iter().any(|error| {
            matches!(
                error,
                BodyLoweringError::Expr {
                    error: LoweringError::UnsupportedSyntax {
                        kind: SyntaxKind::RuleQuantStarLazy
                    },
                    ..
                }
            )
        }));
    }

    #[test]
    fn cast_decl_registers_cast_scheme_before_annotation_generalization() {
        let root = parse(concat!(
            "struct user_id { raw: int }\n",
            "cast(x: int): user_id = user_id { raw: x }\n",
            "pub main: user_id = 0\n",
        ));
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let candidates = output
            .session
            .casts
            .candidates(&["int".to_string()], &["user_id".to_string()]);
        assert_eq!(candidates.len(), 1);
    }

    #[test]
    fn for_stmt_lowers_to_std_loop_for_in() {
        let root = parse_with_flow_loop_std("my xs = 1\npub main = { for x in xs: x }\n");
        let lower = lower_module_map(&root);
        let for_in = control_flow_loop_for_in_def(&lower.modules);
        let module = lower.modules.root_id();
        let xs = lower.modules.value_decls(module, &Name("xs".into()))[0].def;
        let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let (applied_iter, body_lambda) =
            match output.session.poly.expr(binding_body_id(&output, main)) {
                Expr::App(callee, arg) => (*callee, *arg),
                _ => panic!("expected for_in body application"),
            };
        let (for_in_ref, iter_arg) = match output.session.poly.expr(applied_iter) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected for_in iterator application"),
        };
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, for_in_ref)),
            Some(for_in)
        );
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, iter_arg)),
            Some(xs)
        );
        assert!(matches!(
            output.session.poly.expr(body_lambda),
            Expr::Lambda(..)
        ));
    }

    #[test]
    fn labeled_for_stmt_lowers_to_std_label_loop_for_in() {
        let root = parse_with_flow_loop_and_label_std(
            "my xs = 1\npub main = { for 'outer x in xs: 'outer }\n",
        );
        let lower = lower_module_map(&root);
        let for_in = control_flow_label_loop_for_in_def(&lower.modules);
        let module = lower.modules.root_id();
        let xs = lower.modules.value_decls(module, &Name("xs".into()))[0].def;
        let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let (applied_iter, label_lambda) =
            match output.session.poly.expr(binding_body_id(&output, main)) {
                Expr::App(callee, arg) => (*callee, *arg),
                _ => panic!("expected label_loop for_in body application"),
            };
        let (for_in_ref, iter_arg) = match output.session.poly.expr(applied_iter) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected label_loop for_in iterator application"),
        };
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, for_in_ref)),
            Some(for_in)
        );
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, iter_arg)),
            Some(xs)
        );
        let (label_pat, item_lambda) = match output.session.poly.expr(label_lambda) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected label lambda"),
        };
        let label = match output.session.poly.pat(label_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected label param"),
        };
        let item_body = match output.session.poly.expr(item_lambda) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected item lambda"),
        };
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, item_body)),
            Some(label)
        );
    }

    #[test]
    fn application_lowers_to_app_and_constrains_callee_as_function() {
        let root = parse("my f = 1\nmy x = 2\nmy y = f x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "y");
        let expr = binding_expr(&root, "y");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        let (callee, arg) = match session.poly.expr(computation.expr) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected app expr"),
        };
        let callee_ref = expr_ref(&session, callee);
        let arg_ref = expr_ref(&session, arg);
        let callee_value = session
            .refs
            .value(callee_ref)
            .expect("callee ref value slot");
        assert!(session.refs.value(arg_ref).is_some());

        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(callee_value)
            .expect("callee should have function upper bound");
        assert!(bounds.uppers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().neg(bound.neg),
                Neg::Fun { .. }
            )
        }));
    }

    #[test]
    fn index_tail_lowers_to_index_selection_application() {
        let root = parse("my xs = 1\nmy i = 0\nmy got = xs[i]\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "got");
        let expr = binding_expr(&root, "got");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let (callee, arg) = match session.poly.expr(computation.expr) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected index desugar to application"),
        };
        let select = match session.poly.expr(callee) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected index callee to be a selection"),
        };
        assert_eq!(session.poly.select(select).name, "index");
        assert!(matches!(session.poly.expr(arg), Expr::Var(_)));
    }

    #[test]
    fn bool_names_lower_to_bool_literals() {
        let root = parse("my flag = true\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "flag");
        let expr = binding_expr(&root, "flag");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        assert!(matches!(
            session.poly.expr(computation.expr),
            Expr::Lit(Lit::Bool(true))
        ));
    }

    #[test]
    fn plain_string_literal_lowers_to_str_literal() {
        let root = parse("my text = \"a\\n\"\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
        let expr = binding_expr(&root, "text");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        assert!(matches!(
            session.poly.expr(computation.expr),
            Expr::Lit(Lit::Str(text)) if text == "a\n"
        ));
        assert_var_has_lower_con_path(&session, computation.value, &["std", "text", "str", "str"]);
    }

    #[test]
    fn string_interpolation_lowers_to_show_and_concat() {
        let root = parse_with_text_str_std("my x = 1\nmy text = \"hello %{x}\"\n");
        let lower = lower_module_map(&root);
        let concat = text_str_concat_def(&lower.modules);
        let module = lower.modules.root_id();
        let x = lower.modules.value_decls(module, &Name("x".into()))[0].def;
        let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
        let expr = binding_expr(&root, "text");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        session.drain_work();

        let (concat_partial, interpolation) = match session.poly.expr(computation.expr) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected concat application"),
        };
        let (concat_ref, text) = match session.poly.expr(concat_partial) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected concat partial application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, concat_ref)),
            Some(concat)
        );
        assert!(matches!(
            session.poly.expr(text),
            Expr::Lit(Lit::Str(text)) if text == "hello "
        ));
        let (receiver, show) = match session.poly.expr(interpolation) {
            Expr::Select(receiver, select) => (*receiver, *select),
            _ => panic!("expected interpolation show selection"),
        };
        assert_eq!(session.poly.select(show).name, "show");
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, receiver)),
            Some(x)
        );
    }

    #[test]
    fn string_interpolation_lowers_statement_block_body() {
        let root = parse("my text = \"%{my x = 41; x}\"\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
        let expr = binding_expr(&root, "text");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let (receiver, show) = match session.poly.expr(computation.expr) {
            Expr::Select(receiver, select) => (*receiver, *select),
            _ => panic!("expected interpolation show selection"),
        };
        assert_eq!(session.poly.select(show).name, "show");
        assert!(matches!(session.poly.expr(receiver), Expr::Block(..)));
    }

    #[test]
    fn string_interpolation_kind_only_format_lowers_to_method_selection() {
        let root =
            parse("my n = 1\nmy debug = \"%?{n}\"\nmy lower = \"%x{n}\"\nmy upper = \"%X{n}\"\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let n = lower.modules.value_decls(module, &Name("n".into()))[0].def;
        let mut session = AnalysisSession::new(lower.arena);

        for (binding, method) in [
            ("debug", "debug"),
            ("lower", "lower_hex"),
            ("upper", "upper_hex"),
        ] {
            let (owner, site) = binding_def_and_order(&lower.modules, module, binding);
            let expr = binding_expr(&root, binding);

            let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
                .lower_expr(&expr)
                .unwrap();
            session.drain_work();

            let (receiver, select) = match session.poly.expr(computation.expr) {
                Expr::Select(receiver, select) => (*receiver, *select),
                _ => panic!("expected interpolation format kind selection"),
            };
            assert_eq!(session.poly.select(select).name, method);
            assert_eq!(
                session.poly.ref_target(expr_ref(&session, receiver)),
                Some(n)
            );
        }
    }

    #[test]
    fn string_interpolation_layout_format_lowers_to_std_format_protocol() {
        let root = parse_with_text_str_and_format_std("my n = 1\nmy text = \"%+#08x{n}\"\n");
        let lower = lower_module_map(&root);
        let format_lower_hex = core_fmt_def(&lower.modules, "format_lower_hex");
        let format_spec_ctor = core_fmt_def(&lower.modules, "format_spec");
        let sign_plus = core_fmt_format_sign_def(&lower.modules, "plus");
        let module = lower.modules.root_id();
        let n = lower.modules.value_decls(module, &Name("n".into()))[0].def;
        let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
        let expr = binding_expr(&root, "text");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        session.drain_work();

        let (format_partial, receiver) = match session.poly.expr(computation.expr) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected format protocol application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, receiver)),
            Some(n)
        );

        let (format_ref, format_spec) = match session.poly.expr(format_partial) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected format protocol partial application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, format_ref)),
            Some(format_lower_hex)
        );

        let (constructor, record) = match session.poly.expr(format_spec) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected format_spec constructor application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, constructor)),
            Some(format_spec_ctor)
        );
        let fields = match session.poly.expr(record) {
            Expr::Record {
                fields,
                spread: RecordSpread::None,
            } => fields,
            _ => panic!("expected format_spec record payload"),
        };
        assert_eq!(
            fields
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            vec![
                "kind",
                "align",
                "sign",
                "fill",
                "width",
                "precision",
                "alternate",
                "zero_pad"
            ]
        );
        assert!(matches!(
            session
                .poly
                .expr(format_spec_record_field(fields, "alternate")),
            Expr::Lit(Lit::Bool(true))
        ));
        assert!(matches!(
            session
                .poly
                .expr(format_spec_record_field(fields, "zero_pad")),
            Expr::Lit(Lit::Bool(true))
        ));
        assert!(matches!(
            format_spec_some_lit_int(&session, format_spec_record_field(fields, "width")),
            8
        ));
        assert_eq!(
            session.poly.ref_target(expr_ref(
                &session,
                format_spec_some_payload(&session, format_spec_record_field(fields, "sign"))
            )),
            Some(sign_plus)
        );
    }

    fn format_spec_record_field(fields: &[(String, ExprId)], name: &str) -> ExprId {
        fields
            .iter()
            .find_map(|(field, expr)| (field == name).then_some(*expr))
            .unwrap_or_else(|| panic!("expected format_spec field {name}"))
    }

    fn format_spec_some_lit_int(session: &AnalysisSession, expr: ExprId) -> i64 {
        let value = format_spec_some_payload(session, expr);
        match session.poly.expr(value) {
            Expr::Lit(Lit::Int(number)) => *number,
            _ => panic!("expected opt::just int payload"),
        }
    }

    fn format_spec_some_payload(session: &AnalysisSession, expr: ExprId) -> ExprId {
        match session.poly.expr(expr) {
            Expr::App(_, value) => *value,
            _ => panic!("expected opt::just application"),
        }
    }

    #[test]
    fn string_interpolation_invalid_format_text_reports_unsupported() {
        let root = parse("my n = 1\nmy text = \"%q{n}\"\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
        let expr = binding_expr(&root, "text");
        let mut session = AnalysisSession::new(lower.arena);

        let error = match ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
        {
            Ok(_) => panic!("expected invalid string format interpolation to be unsupported"),
            Err(error) => error,
        };

        assert!(matches!(
            error,
            LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::StringInterpFormatText
            }
        ));
    }

    #[test]
    fn case_guard_lowers_as_guard_expr_with_pattern_scope() {
        let root = parse_with_junction_std("my f = case true:\n  n if n -> 1\n  _ -> 0\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let junction = std_junction_def(&lower.modules);
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        session.drain_work();

        let arms = match session.poly.expr(computation.expr) {
            Expr::Case(_, arms) => arms,
            _ => panic!("expected case expr"),
        };
        let first = &arms[0];
        let local = match session.poly.pat(first.pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected guarded pattern local"),
        };
        let guard = first.guard.expect("expected case guard");
        let guard_arg = assert_junction_app(&session, guard, junction);
        let guard_ref = expr_ref(&session, guard_arg);

        assert_eq!(session.poly.ref_target(guard_ref), Some(local));
    }

    #[test]
    fn catch_guard_lowers_as_guard_expr() {
        let root = parse_with_junction_std(
            "my run = 1\nmy f = catch run:\n  eff x, k if true -> k x\n  value -> value\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let junction = std_junction_def(&lower.modules);
        let (f, _) = binding_def_and_order(&lower.modules, module, "f");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let catch = binding_body_id(&output, f);
        let arms = match output.session.poly.expr(catch) {
            Expr::Catch(_, arms) => arms,
            _ => panic!("expected catch expr"),
        };
        let first = &arms[0];
        let guard = first.guard.expect("expected catch guard");
        let guard_arg = assert_junction_app(&output.session, guard, junction);

        assert!(first.continuation.is_some());
        assert!(matches!(
            output.session.poly.expr(guard_arg),
            Expr::Lit(Lit::Bool(true))
        ));
    }

    #[test]
    fn string_or_pattern_lowers_to_or_literal_pattern() {
        let root = parse("my f = case \"a\":\n  \"a\" | \"b\" -> 1\n  _ -> 0\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let arms = match session.poly.expr(computation.expr) {
            Expr::Case(_, arms) => arms,
            _ => panic!("expected case expr"),
        };
        let (lhs, rhs) = match session.poly.pat(arms[0].pat) {
            Pat::Or(lhs, rhs) => (*lhs, *rhs),
            _ => panic!("expected or pattern"),
        };

        assert!(matches!(
            session.poly.pat(lhs),
            Pat::Lit(Lit::Str(text)) if text == "a"
        ));
        assert!(matches!(
            session.poly.pat(rhs),
            Pat::Lit(Lit::Str(text)) if text == "b"
        ));
    }

    #[test]
    fn record_pattern_with_default_binds_field_local() {
        let root = parse("my f({width = 1}) = width\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (f, _) = binding_def_and_order(&lower.modules, module, "f");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let lambda = binding_body_id(&output, f);
        let (pat, body) = match output.session.poly.expr(lambda) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected function binding to lower to lambda"),
        };
        let field_pat = match output.session.poly.pat(pat) {
            Pat::Record { fields, .. } => fields[0].1,
            _ => panic!("expected record pattern"),
        };
        let field = match output.session.poly.pat(field_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected field local"),
        };
        let body_ref = expr_ref(&output.session, body);

        assert_eq!(output.session.poly.ref_target(body_ref), Some(field));
    }

    #[test]
    fn poly_variant_expr_and_pattern_lower_to_poly_variant_ir() {
        let root =
            parse("my f option = case option:\n  :ok msg -> :rendered msg\n  :pending -> :empty\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (f, _) = binding_def_and_order(&lower.modules, module, "f");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let lambda = binding_body_id(&output, f);
        let case = match output.session.poly.expr(lambda) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected function binding to lower to lambda"),
        };
        let arms = match output.session.poly.expr(case) {
            Expr::Case(_, arms) => arms,
            _ => panic!("expected case expr"),
        };
        assert!(matches!(
            output.session.poly.pat(arms[0].pat),
            Pat::PolyVariant(name, payloads) if name == "ok" && payloads.len() == 1
        ));
        assert!(matches!(
            output.session.poly.expr(arms[0].body),
            Expr::PolyVariant(name, payloads) if name == "rendered" && payloads.len() == 1
        ));
    }

    #[test]
    fn record_literal_lowers_to_record_expr() {
        let root = parse("my r = {x: 1, y: true}\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "r");
        let expr = binding_expr(&root, "r");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        match session.poly.expr(computation.expr) {
            Expr::Record { fields, spread } => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "x");
                assert_eq!(fields[1].0, "y");
                assert!(matches!(spread, RecordSpread::None));
            }
            _ => panic!("expected record literal"),
        }
    }

    #[test]
    fn struct_constructor_accepts_record_literal_argument() {
        let root = parse("struct Point {x: int, y: int}\nmy p = Point {x: 1, y: 2}\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "p");
        let expr = binding_expr(&root, "p");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let (_, arg) = match session.poly.expr(computation.expr) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected constructor application"),
        };
        assert!(matches!(
            session.poly.expr(arg),
            Expr::Record {
                spread: RecordSpread::None,
                ..
            }
        ));
    }

    #[test]
    fn if_condition_is_wrapped_with_junction_before_bool_case() {
        let root = parse_with_junction_std("my f = if true: 1 else: 2\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let junction = std_junction_def(&lower.modules);
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        session.drain_work();

        let arms = match session.poly.expr(computation.expr) {
            Expr::Case(scrutinee, arms) => {
                let condition = assert_junction_app(&session, *scrutinee, junction);
                assert!(matches!(
                    session.poly.expr(condition),
                    Expr::Lit(Lit::Bool(true))
                ));
                arms
            }
            _ => panic!("expected if expr to lower to case"),
        };
        assert_eq!(arms.len(), 2);
        assert!(matches!(
            session.poly.pat(arms[0].pat),
            Pat::Lit(Lit::Bool(true))
        ));
        assert!(matches!(
            session.poly.pat(arms[1].pat),
            Pat::Lit(Lit::Bool(false))
        ));
    }

    #[test]
    fn elsif_lowers_to_nested_false_case() {
        let root = parse_with_junction_std("my f = if true: 1 elsif false: 2 else: 3\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let junction = std_junction_def(&lower.modules);
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        session.drain_work();

        let outer_arms = match session.poly.expr(computation.expr) {
            Expr::Case(scrutinee, arms) => {
                let condition = assert_junction_app(&session, *scrutinee, junction);
                assert!(matches!(
                    session.poly.expr(condition),
                    Expr::Lit(Lit::Bool(true))
                ));
                arms
            }
            _ => panic!("expected outer case"),
        };
        let nested = outer_arms[1].body;
        match session.poly.expr(nested) {
            Expr::Case(scrutinee, arms) => {
                let condition = assert_junction_app(&session, *scrutinee, junction);
                assert!(matches!(
                    session.poly.expr(condition),
                    Expr::Lit(Lit::Bool(false))
                ));
                assert_eq!(arms.len(), 2);
            }
            _ => panic!("expected elsif to lower into false branch case"),
        }
    }

    #[test]
    fn if_without_else_discards_then_value_and_returns_unit() {
        let root = parse_with_junction_std("my f = if true: 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let junction = std_junction_def(&lower.modules);
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        session.drain_work();

        let arms = match session.poly.expr(computation.expr) {
            Expr::Case(scrutinee, arms) => {
                let condition = assert_junction_app(&session, *scrutinee, junction);
                assert!(matches!(
                    session.poly.expr(condition),
                    Expr::Lit(Lit::Bool(true))
                ));
                arms
            }
            _ => panic!("expected if expr to lower to case"),
        };
        assert!(matches!(session.poly.expr(arms[0].body), Expr::Block(_, _)));
        assert!(matches!(
            session.poly.expr(arms[1].body),
            Expr::Lit(Lit::Unit)
        ));
    }

    #[test]
    fn method_lambda_lowers_to_receiver_lambda_with_selection_body() {
        let root = parse("my display = \\.display\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "display");
        let expr = binding_expr(&root, "display");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let (pat, body) = match session.poly.expr(computation.expr) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected method lambda to lower to lambda"),
        };
        let receiver = match session.poly.pat(pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected implicit receiver pattern"),
        };
        let (receiver_expr, select) = match session.poly.expr(body) {
            Expr::Select(receiver_expr, select) => (*receiver_expr, *select),
            _ => panic!("expected method lambda body to be a selection"),
        };
        let receiver_ref = expr_ref(&session, receiver_expr);

        assert_eq!(session.poly.ref_target(receiver_ref), Some(receiver));
        assert_eq!(session.poly.select(select).name, "display");
    }

    #[test]
    fn dollar_sigil_read_lowers_to_ref_get_call() {
        let root = parse("my &x = 1\nmy got = $x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (target, _) = binding_def_and_order(&lower.modules, module, "&x");
        let (owner, site) = binding_def_and_order(&lower.modules, module, "got");
        let expr = binding_expr(&root, "got");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        session.drain_work();

        let (callee, unit) = match session.poly.expr(computation.expr) {
            Expr::App(callee, unit) => (*callee, *unit),
            _ => panic!("expected var read to apply get to unit"),
        };
        let (receiver_expr, select) = match session.poly.expr(callee) {
            Expr::Select(receiver_expr, select) => (*receiver_expr, *select),
            _ => panic!("expected var read callee to be get selection"),
        };
        let receiver_ref = expr_ref(&session, receiver_expr);

        assert_eq!(session.poly.ref_target(receiver_ref), Some(target));
        assert_eq!(session.poly.select(select).name, "get");
        assert!(matches!(session.poly.expr(unit), Expr::Lit(Lit::Unit)));
    }

    #[test]
    fn assign_tail_lowers_to_ref_set() {
        let root = parse("my &x = 1\nmy set = &x = 2\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (target, _) = binding_def_and_order(&lower.modules, module, "&x");
        let (set, _) = binding_def_and_order(&lower.modules, module, "set");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, set);
        let (reference_expr, value_expr) = match output.session.poly.expr(body) {
            Expr::RefSet(reference_expr, value_expr) => (*reference_expr, *value_expr),
            _ => panic!("expected assignment to lower to ref set"),
        };
        let reference = expr_ref(&output.session, reference_expr);

        assert_eq!(output.session.poly.ref_target(reference), Some(target));
        assert!(matches!(
            output.session.poly.expr(value_expr),
            Expr::Lit(Lit::Int(2))
        ));
    }

    #[test]
    fn block_lowers_local_binding_and_tail_reference() {
        let root = parse("my f =\n  my x = 1\n  x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (f, _) = binding_def_and_order(&lower.modules, module, "f");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, f);
        let (stmts, tail) = match output.session.poly.expr(body) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected block body"),
        };
        let [Stmt::Let(_, pat, value)] = stmts.as_slice() else {
            panic!("expected one local let");
        };
        let local = match output.session.poly.pat(*pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected local binding pattern"),
        };
        assert!(matches!(
            output.session.poly.expr(*value),
            Expr::Lit(Lit::Int(1))
        ));
        let tail_ref = expr_ref(&output.session, tail);

        assert_eq!(output.session.poly.ref_target(tail_ref), Some(local));
    }

    #[test]
    fn dollar_binding_lowers_to_var_ref_and_run_wrapper() {
        let root = parse(concat!(
            "mod std:\n",
            "  mod control:\n",
            "    mod var:\n",
            "      type ref 'e 'a with:\n",
            "        our r.get = r\n",
            "      act var 't:\n",
            "        my var_ref() = 0\n",
            "        my run v x = x\n",
            "my f =\n",
            "  my $x = 1\n",
            "  $x\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let std = lower.modules.module_decls(module, &Name("std".into()))[0].module;
        let control = lower.modules.module_decls(std, &Name("control".into()))[0].module;
        let var_module = lower.modules.module_decls(control, &Name("var".into()))[0].module;
        let std_var_companion =
            lower.modules.module_decls(var_module, &Name("var".into()))[0].module;
        let std_var_ref = lower
            .modules
            .value_decls(std_var_companion, &Name("var_ref".into()))[0]
            .def;
        let std_run = lower
            .modules
            .value_decls(std_var_companion, &Name("run".into()))[0]
            .def;
        let (f, _) = binding_def_and_order(&lower.modules, module, "f");
        let local_var_act = lower.modules.synthetic_var_act_uses(f)[0].clone();
        assert_eq!(local_var_act.source, Name("&x".into()));
        let local_var_companion = lower.modules.type_companion(local_var_act.act).unwrap();
        let var_ref = lower
            .modules
            .value_decls(local_var_companion, &Name("var_ref".into()))[0]
            .def;
        let run = lower
            .modules
            .value_decls(local_var_companion, &Name("run".into()))[0]
            .def;
        assert_ne!(var_ref, std_var_ref);
        assert_ne!(run, std_run);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, f);
        let (first_stmts, after_init) = match output.session.poly.expr(body) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected outer block"),
        };
        let [Stmt::Let(_, init_pat, init_expr)] = first_stmts.as_slice() else {
            panic!("expected init let");
        };
        let init_def = match output.session.poly.pat(*init_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected init binding pattern"),
        };
        assert!(matches!(
            output.session.poly.expr(*init_expr),
            Expr::Lit(Lit::Int(1))
        ));
        let _ = def_scheme(&output, init_def);

        let (second_stmts, wrapped) = match output.session.poly.expr(after_init) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected reference block"),
        };
        let [Stmt::Let(_, reference_pat, reference_expr)] = second_stmts.as_slice() else {
            panic!("expected reference let");
        };
        assert!(matches!(
            output.session.poly.pat(*reference_pat),
            Pat::Var(_)
        ));
        let reference_def = match output.session.poly.pat(*reference_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected reference binding pattern"),
        };
        let _ = def_scheme(&output, reference_def);
        let (var_ref_callee, _) = match output.session.poly.expr(*reference_expr) {
            Expr::App(callee, _unit) => (*callee, *_unit),
            _ => panic!("expected var_ref call"),
        };
        let var_ref_ref = expr_ref(&output.session, var_ref_callee);
        assert_eq!(output.session.poly.ref_target(var_ref_ref), Some(var_ref));

        let (run_with_init, _) = match output.session.poly.expr(wrapped) {
            Expr::App(callee, _body) => (*callee, *_body),
            _ => panic!("expected run application"),
        };
        let (run_expr, init_arg) = match output.session.poly.expr(run_with_init) {
            Expr::App(callee, init) => (*callee, *init),
            _ => panic!("expected run init application"),
        };
        let run_ref = expr_ref(&output.session, run_expr);
        assert_eq!(output.session.poly.ref_target(run_ref), Some(run));
        let init_ref = expr_ref(&output.session, init_arg);
        assert_eq!(output.session.poly.ref_target(init_ref), Some(init_def));
    }

    #[test]
    fn dollar_binding_synthetic_act_is_scoped_by_owner_def() {
        let root = parse(concat!(
            "mod std:\n",
            "  mod control:\n",
            "    mod var:\n",
            "      type ref 'e 'a with:\n",
            "        our r.get = r\n",
            "      act var 't:\n",
            "        my var_ref() = 0\n",
            "        my run v x = x\n",
            "my f =\n",
            "  my $x = 1\n",
            "  $x\n",
            "my g =\n",
            "  my $x = 2\n",
            "  $x\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (f, _) = binding_def_and_order(&lower.modules, module, "f");
        let (g, _) = binding_def_and_order(&lower.modules, module, "g");
        let f_act = lower.modules.synthetic_var_act_uses(f)[0].clone();
        let g_act = lower.modules.synthetic_var_act_uses(g)[0].clone();
        assert_eq!(f_act.source, Name("&x".into()));
        assert_eq!(g_act.source, Name("&x".into()));
        assert_ne!(f_act.act, g_act.act);
        let f_var_ref = act_member_def(&lower.modules, f_act.act, "var_ref");
        let f_run = act_member_def(&lower.modules, f_act.act, "run");
        let g_var_ref = act_member_def(&lower.modules, g_act.act, "var_ref");
        let g_run = act_member_def(&lower.modules, g_act.act, "run");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_eq!(
            dollar_binding_method_targets(&output, f),
            (f_var_ref, f_run)
        );
        assert_eq!(
            dollar_binding_method_targets(&output, g),
            (g_var_ref, g_run)
        );
    }

    fn act_member_def(modules: &ModuleTable, act: TypeDeclId, member: &str) -> DefId {
        let companion = modules.type_companion(act).expect("synthetic companion");
        modules.value_decls(companion, &Name(member.into()))[0].def
    }

    fn dollar_binding_method_targets(output: &BodyLowering, owner: DefId) -> (DefId, DefId) {
        let body = binding_body_id(output, owner);
        let (_, after_init) = match output.session.poly.expr(body) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected outer block"),
        };
        let (second_stmts, wrapped) = match output.session.poly.expr(after_init) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected reference block"),
        };
        let [Stmt::Let(_, _, reference_expr)] = second_stmts.as_slice() else {
            panic!("expected reference let");
        };
        let var_ref_callee = match output.session.poly.expr(*reference_expr) {
            Expr::App(callee, _) => *callee,
            _ => panic!("expected var_ref call"),
        };
        let var_ref = output
            .session
            .poly
            .ref_target(expr_ref(&output.session, var_ref_callee))
            .expect("var_ref target");
        let run_with_init = match output.session.poly.expr(wrapped) {
            Expr::App(callee, _) => *callee,
            _ => panic!("expected run application"),
        };
        let run_expr = match output.session.poly.expr(run_with_init) {
            Expr::App(callee, _) => *callee,
            _ => panic!("expected run init application"),
        };
        let run = output
            .session
            .poly
            .ref_target(expr_ref(&output.session, run_expr))
            .expect("run target");
        (var_ref, run)
    }

    #[test]
    fn field_tail_lowers_to_deferred_selection_and_final_record_fallback() {
        let root = parse("my get = \\x -> x.foo\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, _) = binding_def_and_order(&lower.modules, module, "get");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, owner);
        let lambda_body = match output.session.poly.expr(body) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected lambda body"),
        };
        let select = match output.session.poly.expr(lambda_body) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected select expr"),
        };
        assert_eq!(
            output.session.poly.select(select).resolution,
            Some(SelectResolution::RecordField)
        );
    }

    #[test]
    fn struct_field_lowers_to_value_method_selection() {
        let root = parse("struct User { age: int }\nmy u: User = 1\nmy got = u.age\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
        let method = type_field_method(&lower.modules, user.id, "age", TypeMethodReceiver::Value);
        let (got, _) = binding_def_and_order(&lower.modules, module, "got");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let method_scheme = def_scheme(&output, method.def);
        let Pos::Fun { ret, .. } = output.session.poly.typ.pos(method_scheme.predicate) else {
            panic!("expected field method function scheme");
        };
        assert!(matches!(
            output.session.poly.typ.pos(*ret),
            Pos::Con(path, args) if path == &vec!["int".to_string()] && args.is_empty()
        ));
        let got_body = binding_body_id(&output, got);
        let select = match output.session.poly.expr(got_body) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected struct field select"),
        };
        assert_eq!(
            output.session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method.def })
        );
    }

    #[test]
    fn struct_field_ref_assignment_lowers_to_ref_method_selection() {
        let root = parse(concat!(
            "mod std:\n",
            "  mod control:\n",
            "    mod var:\n",
            "      type ref 'e 'a\n",
            "struct User { age: int }\n",
            "my &u: std::control::var::ref 'e User = 1\n",
            "my set = &u.age = 2\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
        let method = type_field_method(&lower.modules, user.id, "age", TypeMethodReceiver::Ref);
        let (set, _) = binding_def_and_order(&lower.modules, module, "set");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let method_scheme = def_scheme(&output, method.def);
        let Pos::Fun { ret, .. } = output.session.poly.typ.pos(method_scheme.predicate) else {
            panic!("expected ref field method function scheme");
        };
        assert!(matches!(
            output.session.poly.typ.pos(*ret),
            Pos::Con(path, args)
                if path == &crate::std_paths::control_var_ref_type() && args.len() == 2
        ));
        let set_body = binding_body_id(&output, set);
        let (reference_expr, value_expr) = match output.session.poly.expr(set_body) {
            Expr::RefSet(reference_expr, value_expr) => (*reference_expr, *value_expr),
            _ => panic!("expected field assignment to lower to ref set"),
        };
        let select = match output.session.poly.expr(reference_expr) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected assignment target to be a field select"),
        };

        assert_eq!(
            output.session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method.def })
        );
        assert!(matches!(
            output.session.poly.expr(value_expr),
            Expr::Lit(Lit::Int(2))
        ));
    }

    #[test]
    fn type_with_value_method_lowers_in_companion_and_resolves_selection() {
        let root = parse("type User with:\n  our x.id = x\nmy u: User = 1\nmy got = u.id\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
        let method = lower.modules.type_methods(user.id)[0].def;
        let (got, _) = binding_def_and_order(&lower.modules, module, "got");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_method_body_is_receiver_identity(&output, method);
        let got_body = binding_body_id(&output, got);
        let select = match output.session.poly.expr(got_body) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected select expr"),
        };
        assert_eq!(
            output.session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
    }

    #[test]
    fn type_method_header_arg_lowers_after_receiver() {
        let root = parse("type User with:\n  our x.pick y = y\nmy site = 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
        let method = lower.modules.type_methods(user.id)[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, method);
        let arg_lambda = match output.session.poly.expr(body) {
            Expr::Lambda(_, arg_lambda) => *arg_lambda,
            _ => panic!("expected method receiver lambda"),
        };
        let (arg_pat, arg_body) = match output.session.poly.expr(arg_lambda) {
            Expr::Lambda(arg_pat, arg_body) => (*arg_pat, *arg_body),
            _ => panic!("expected method header arg lambda"),
        };
        let arg = match output.session.poly.pat(arg_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected arg var pattern"),
        };
        let reference = expr_ref(&output.session, arg_body);
        assert_eq!(output.session.poly.ref_target(reference), Some(arg));
    }

    #[test]
    fn std_ref_update_method_body_lowers() {
        let root = parse(concat!(
            "mod std:\n",
            "  mod control:\n",
            "    mod var:\n",
            "      act ref_update 'a:\n",
            "        pub update: 'a -> 'a\n",
            "      type ref 'e 'a with:\n",
            "        struct self:\n",
            "          get: () -> ['e] 'a\n",
            "          update_effect: () -> [ref_update 'a; 'e] ()\n",
            "        pub r.update f =\n",
            "          my loop(x: [_] _) = catch x:\n",
            "            ref_update::update v, k -> loop:k:f v\n",
            "          loop:r.update_effect()\n",
            "my site = 1\n",
        ));
        let lower = lower_module_map(&root);
        let root_module = lower.modules.root_id();
        let std = lower.modules.module_decls(root_module, &Name("std".into()))[0].module;
        let control = lower.modules.module_decls(std, &Name("control".into()))[0].module;
        let var = lower.modules.module_decls(control, &Name("var".into()))[0].module;
        let ref_type = lower.modules.type_decls(var, &Name("ref".into()))[0].clone();
        let field_method = type_field_method(
            &lower.modules,
            ref_type.id,
            "update_effect",
            TypeMethodReceiver::Value,
        )
        .def;
        let method = lower.modules.type_methods(ref_type.id)[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let body = binding_body_id(&output, method);
        let scheme = def_scheme(&output, method);
        let rendered = poly::dump::format_scheme(&output.session.poly.typ, scheme);
        assert_eq!(
            rendered,
            "std::control::var::ref('a & 'c, 'b) -> ('b -> ['c] 'b) -> ['c, 'a] ()"
        );
        let update_effect =
            find_select_by_name(&output.session, body, "update_effect").expect("update_effect");
        assert_eq!(
            output.session.poly.select(update_effect).resolution,
            Some(SelectResolution::Method { def: field_method })
        );
    }

    #[test]
    fn annotated_recursive_handler_does_not_subtract_outer_effect() {
        let root = parse(concat!(
            "act tick:\n",
            "  pub out: () -> ()\n",
            "act flip:\n",
            "  pub coin: () -> bool\n",
            "pub pick(action: [flip] _) = catch action:\n",
            "  flip::coin(), k -> pick(k true)\n",
            "  v -> v\n",
            "pub loop(x: [tick] _) = catch x:\n",
            "  tick::out(), k -> pick(loop(k ()))\n",
            "  v -> v\n",
            "my site = 1\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let loop_def = lower.modules.value_decls(module, &Name("loop".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, loop_def));
        assert!(
            !rendered.contains("flip"),
            "loop annotation allowed flip to be subtracted: {rendered}"
        );
    }

    #[test]
    fn annotated_recursive_handler_pick_only_terminates() {
        let root = parse(concat!(
            "act flip:\n",
            "  pub coin: () -> bool\n",
            "pub pick(action: [flip] _) = catch action:\n",
            "  flip::coin(), k -> pick(k true)\n",
            "  v -> v\n",
            "my site = 1\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let pick_def = lower.modules.value_decls(module, &Name("pick".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, pick_def));
        assert!(
            rendered.contains("flip"),
            "pick annotation should mention flip: {rendered}"
        );
    }

    #[test]
    fn catch_bare_operation_uses_declared_act_family() {
        let root = parse(concat!(
            "act sub 'a:\n",
            "  pub return: 'a -> never\n",
            "  pub sub(x: [_] 'a): 'a = catch x:\n",
            "    return a, _ -> a\n",
            "    a -> a\n",
            "my site = 1\n",
        ));
        let lower = lower_module_map(&root);
        let root_module = lower.modules.root_id();
        let sub_act = lower.modules.type_decls(root_module, &Name("sub".into()))[0].clone();
        let companion = lower
            .modules
            .type_companion(sub_act.id)
            .expect("act companion");
        let method = lower.modules.value_decls(companion, &Name("sub".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, method));
        assert!(
            rendered.contains("[sub(") || rendered.contains("[sub;") || rendered.contains("[sub "),
            "{rendered}"
        );
        assert!(
            !rendered.contains("[return(") && !rendered.contains("[return "),
            "{rendered}"
        );
    }

    #[test]
    fn act_operation_signature_keeps_declared_act_type_vars() {
        let root = parse(concat!(
            "act parse 'item 'err 'pos 'snap:\n",
            "  pub item: () -> 'item\n",
            "  pub fail: 'err -> never\n",
            "  pub pos: () -> 'pos\n",
            "  pub snapshot: () -> 'snap\n",
            "my site = 1\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let parse_act = lower.modules.type_decls(module, &Name("parse".into()))[0].clone();
        let companion = lower
            .modules
            .type_companion(parse_act.id)
            .expect("act companion");
        let item = lower.modules.value_decls(companion, &Name("item".into()))[0].def;
        let pos = lower.modules.value_decls(companion, &Name("pos".into()))[0].def;
        let snapshot = lower
            .modules
            .value_decls(companion, &Name("snapshot".into()))[0]
            .def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let item_rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, item));
        let pos_rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, pos));
        let snapshot_rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, snapshot));
        assert_eq!(item_rendered, "() -> [parse 'a 'b 'c 'd] 'a");
        assert_eq!(pos_rendered, "() -> [parse 'a 'b 'c 'd] 'c");
        assert_eq!(snapshot_rendered, "() -> [parse 'a 'b 'c 'd] 'd");
    }

    #[test]
    fn top_level_tuple_binding_registers_each_name() {
        let root = parse("my (x, y) = (1, 2)\nmy site = y\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let x = lower.modules.value_decls(module, &Name("x".into()))[0].def;
        let y = lower.modules.value_decls(module, &Name("y".into()))[0].def;
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let site_body = binding_body_id(&output, site);
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, site_body)),
            Some(y)
        );
        assert!(output.session.poly.defs.get(x).is_some());
    }

    #[test]
    fn parenthesized_keyword_binding_registers_as_value_name() {
        let root = parse("my (mod) = 1\nmy site = mod\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let keyword = lower.modules.value_decls(module, &Name("mod".into()))[0].def;
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let site_body = binding_body_id(&output, site);
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, site_body)),
            Some(keyword)
        );
    }

    #[test]
    fn type_with_ref_method_keeps_ampersand_receiver_name_and_resolves_ref_selection() {
        let root = parse(concat!(
            "mod std:\n",
            "  mod control:\n",
            "    mod var:\n",
            "      type ref 'e 'a\n",
            "type User with:\n",
            "  our &x.id = &x\n",
            "my r: std::control::var::ref 'e User = 1\n",
            "my got = r.id\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
        let method = lower.modules.type_methods(user.id)[0].def;
        let (got, _) = binding_def_and_order(&lower.modules, module, "got");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_method_body_is_receiver_identity(&output, method);
        let got_body = binding_body_id(&output, got);
        let select = match output.session.poly.expr(got_body) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected select expr"),
        };
        assert_eq!(
            output.session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
    }

    #[test]
    fn local_type_named_ref_does_not_resolve_ref_selection() {
        let root = parse(
            "type ref 'e 'a\n\
             type User with:\n  our &x.id = &x\n\
             my r: ref 'e User = 1\nmy got = r.id\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (got, _) = binding_def_and_order(&lower.modules, module, "got");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let got_body = binding_body_id(&output, got);
        let select = match output.session.poly.expr(got_body) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected select expr"),
        };
        assert_eq!(
            output.session.poly.select(select).resolution,
            Some(SelectResolution::RecordField)
        );
    }

    #[test]
    fn private_type_method_is_available_only_inside_companion_scope() {
        let root = parse(
            "type User with:\n  my x.secret = x\n  my u: User = 1\n  my inside = u.secret\nmy outside_u: User = 1\nmy outside = outside_u.secret\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
        let companion = lower.modules.type_companion(user.id).unwrap();
        let method = lower.modules.type_methods(user.id)[0].def;
        let inside = lower.modules.value_decls(companion, &Name("inside".into()))[0].def;
        let (outside, _) = binding_def_and_order(&lower.modules, module, "outside");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert!(
            output
                .session
                .methods
                .value_candidates(&["User".into()], "secret")
                .is_empty()
        );
        let inside_select = match output.session.poly.expr(binding_body_id(&output, inside)) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected inside select"),
        };
        assert_eq!(
            output.session.poly.select(inside_select).resolution,
            Some(SelectResolution::Method { def: method })
        );
        let outside_select = match output.session.poly.expr(binding_body_id(&output, outside)) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected outside select"),
        };
        assert_eq!(
            output.session.poly.select(outside_select).resolution,
            Some(SelectResolution::RecordField)
        );
    }

    #[test]
    fn act_method_lowers_in_companion_and_registers_effect_method() {
        let root = parse("act nondet:\n  our x.flip = x\nmy got = 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let nondet = lower.modules.type_decls(module, &Name("nondet".into()))[0].clone();
        let method = lower.modules.act_methods(nondet.id)[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_method_body_is_receiver_identity(&output, method);
        assert_act_method_receiver_has_self_subtract(&output, method, "nondet");
        assert_eq!(
            output.session.effect_methods.candidates("flip")[0].def,
            method
        );
    }

    #[test]
    fn act_copy_lowers_source_method_body_as_destination_method() {
        let root = parse(
            "act outer:\n  my act last:\n    our x.flip = x\n  my act next = last\nmy got = 1\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let outer = lower.modules.type_decls(module, &Name("outer".into()))[0].clone();
        let companion = lower
            .modules
            .type_companion(outer.id)
            .expect("outer companion");
        let next = lower.modules.type_decls(companion, &Name("next".into()))[0].clone();
        let method = lower.modules.act_methods(next.id)[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_method_body_is_receiver_identity(&output, method);
    }

    #[test]
    fn act_copy_lowers_qualified_source_method_body() {
        let root = parse(
            "mod source:\n  act box 'a:\n    our x.flip: 'a = x\nact local 't = source::box 't\nmy got = 1\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let local = lower.modules.type_decls(module, &Name("local".into()))[0].clone();
        let method = lower.modules.act_methods(local.id)[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_method_body_is_receiver_identity(&output, method);
    }

    #[test]
    fn role_method_signature_lowers_to_typeclass_method_selection() {
        let root = parse("role Display 'a:\n  our x.display: unit\nmy show = \\x -> x.display\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let display = lower.modules.type_decls(module, &Name("Display".into()))[0].clone();
        let method = lower.modules.role_methods(display.id)[0].def;
        let (show, _) = binding_def_and_order(&lower.modules, module, "show");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_eq!(
            output.session.role_methods.candidates("display")[0].def,
            method
        );
        let method_scheme = match output.session.poly.defs.get(method) {
            Some(Def::Let {
                scheme: Some(scheme),
                ..
            }) => scheme,
            _ => panic!("role method should have a generalized scheme"),
        };
        assert_eq!(method_scheme.role_predicates.len(), 1);
        assert_eq!(
            method_scheme.role_predicates[0].role,
            vec!["Display".to_string()]
        );

        let show_body = binding_body_id(&output, show);
        let lambda_body = match output.session.poly.expr(show_body) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected show lambda"),
        };
        let select = match output.session.poly.expr(lambda_body) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected select expr"),
        };
        assert_eq!(
            output.session.poly.select(select).resolution,
            Some(SelectResolution::TypeclassMethod { member: method })
        );
    }

    #[test]
    fn tuple_impl_member_coalesces_requirement_scaffolding_vars() {
        let root = parse(concat!(
            "role Size 'a:\n",
            "  our x.size: int\n",
            "impl Size int:\n",
            "  our x.size = x\n",
            "impl Size ('a, 'b):\n",
            "  where 'a: Size\n",
            "  where 'b: Size\n",
            "  our value.size = case value:\n",
            "    (a, b) -> case a.size:\n",
            "      _ -> b.size\n",
        ));
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let rendered = output
            .session
            .poly
            .defs
            .iter()
            .filter_map(|(_, def_data)| match def_data {
                Def::Let {
                    scheme: Some(scheme),
                    ..
                } => Some(poly::dump::format_scheme(&output.session.poly.typ, scheme)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            rendered.iter().any(
                |scheme| scheme == "('a, 'b) -> int where 'b: Size, 'a: Size"
                    || scheme == "('a, 'b) -> int where 'a: Size, 'b: Size"
            ),
            "{rendered:?}"
        );
    }

    #[test]
    fn typeclass_method_receiver_participates_in_selected_method_scheme() {
        let root = parse("role Ord 'a:\n  our x.le: 'a -> bool\nmy le = \\x -> \\y -> x.le y\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (le, _) = binding_def_and_order(&lower.modules, module, "le");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, le));
        assert_eq!(rendered, "'a -> 'a -> bool where 'a: Ord");
    }

    #[test]
    fn role_input_variance_records_method_signature_polarities() {
        let root = parse("role Cast 'from 'to:\n  our x.cast: 'to\n");
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let role = vec!["Cast".to_string()];
        assert_eq!(
            output.session.role_input_variances.for_role(&role),
            Some(
                [
                    RoleInputVariance::Contravariant,
                    RoleInputVariance::Covariant,
                ]
                .as_slice()
            )
        );
    }

    #[test]
    fn role_input_variance_keeps_data_constructor_arguments_invariant() {
        let root = parse(concat!(
            "pub enum wrap 'a = item 'a\n",
            "role UsesWrap 'a:\n",
            "  our x.use: wrap 'a -> bool\n",
        ));
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let role = vec!["UsesWrap".to_string()];
        assert_eq!(
            output.session.role_input_variances.for_role(&role),
            Some([RoleInputVariance::Invariant].as_slice())
        );
    }

    #[test]
    fn unannotated_role_default_method_does_not_force_input_invariant() {
        let root = parse("role Display 'a:\n  our x.display: unit\n  our x.id = x\n");
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let role = vec!["Display".to_string()];
        assert_eq!(
            output.session.role_input_variances.for_role(&role),
            Some([RoleInputVariance::Contravariant].as_slice())
        );
    }

    #[test]
    fn covariant_where_role_input_drops_supertype_scaffold_from_residual() {
        let root = parse(concat!(
            "pub enum mylist 'a = nil | cons('a, mylist 'a)\n",
            "role Ord 'a:\n",
            "  our x.le: 'a -> bool\n",
            "my split_le xs x = case xs:\n",
            "  mylist::nil -> mylist::nil\n",
            "  mylist::cons(y, rest) -> case y.le x:\n",
            "    true -> mylist::cons(y, split_le rest x)\n",
            "    false -> split_le rest x\n",
            "my sort_head xs = case xs:\n",
            "  mylist::nil -> mylist::nil\n",
            "  mylist::cons(x, rest) -> mylist::cons(x, split_le rest x)\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (sort_head, _) = binding_def_and_order(&lower.modules, module, "sort_head");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let scheme = def_scheme(&output, sort_head);
        assert!(matches!(
            scheme.role_predicates[0].inputs[0],
            poly::types::RolePredicateArg::Covariant(_)
        ));
        let rendered = poly::dump::format_scheme(&output.session.poly.typ, scheme);
        assert_eq!(rendered, "mylist('a & 'b) -> mylist('b | 'a) where 'a: Ord");
    }

    #[test]
    fn unannotated_role_default_method_keeps_covariant_where_residual_clean() {
        let root = parse(concat!(
            "pub enum mylist 'a = nil | cons('a, mylist 'a)\n",
            "role Display 'a:\n",
            "  our x.display: unit\n",
            "  our x.id = x\n",
            "my display_items(xs: mylist 'a): unit =\n",
            "  where 'a: Display\n",
            "  case xs:\n",
            "    mylist::nil -> ()\n",
            "    mylist::cons(y, rest) ->\n",
            "      y.display\n",
            "      display_items rest\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (display_items, _) = binding_def_and_order(&lower.modules, module, "display_items");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let scheme = def_scheme(&output, display_items);
        assert!(matches!(
            scheme.role_predicates[0].inputs[0],
            poly::types::RolePredicateArg::Covariant(_)
        ));
        let rendered = poly::dump::format_scheme(&output.session.poly.typ, scheme);
        assert_eq!(rendered, "mylist 'a -> () where 'a: Display");
    }

    #[test]
    fn multi_input_role_method_selection_resolves_concrete_demand() {
        let root = parse(concat!(
            "role Index 'container 'key:\n",
            "  type value\n",
            "  pub container.index: 'key -> value\n",
            "impl Index int int:\n",
            "  type value = int\n",
            "  our c.index i = c\n",
            "my pick(c: int, i: int) = c.index i\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (pick, _) = binding_def_and_order(&lower.modules, module, "pick");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, pick));
        // selection 解決は receiver demand を別に fabricate せず、method instantiation
        // 由来の demand だけを使う。複数引数 role でも concrete なら discharge される。
        assert_eq!(rendered, "int -> int -> int");
    }

    #[test]
    fn explicit_associated_type_keeps_impl_input_type_parameter() {
        let root = parse(concat!(
            "type box 'a with:\n",
            "  struct self:\n",
            "    item: 'a\n",
            "role Index 'container 'key:\n",
            "  type value\n",
            "  pub container.index: 'key -> value\n",
            "impl Index (box 'a) int:\n",
            "  type value = 'a\n",
            "  our c.index i = c.item\n",
            "my pick(c: box int, i: int) = c.index i\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (pick, _) = binding_def_and_order(&lower.modules, module, "pick");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, pick));
        assert_eq!(rendered, "box int -> int -> int");
    }

    #[test]
    fn role_method_signature_is_lowered_as_positive_shape() {
        let root = parse("role Display 'a:\n  our x.display: unit\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let display = lower.modules.type_decls(module, &Name("Display".into()))[0].clone();
        let method = lower.modules.role_methods(display.id)[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let root = output.typing.def(method).expect("role method root");
        let bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(root)
            .expect("role method signature should constrain root");
        let types = output.session.infer.constraints().types();
        assert!(bounds.lowers().iter().any(|bound| {
            matches!(
                types.pos(bound.pos),
                Pos::Fun { ret, .. }
                    if matches!(
                        types.pos(*ret),
                        Pos::Con(path, args)
                            if path == &vec!["unit".to_string()] && args.is_empty()
                    )
            )
        }));
        assert!(
            !bounds
                .uppers()
                .iter()
                .any(|bound| matches!(types.neg(bound.neg), Neg::Fun { .. }))
        );
    }

    #[test]
    fn private_role_method_is_not_registered_for_selection_fallback() {
        let root = parse("role Hidden 'a:\n  my x.secret: unit\nmy show = \\x -> x.secret\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let hidden = lower.modules.type_decls(module, &Name("Hidden".into()))[0].clone();
        assert_eq!(lower.modules.role_methods(hidden.id)[0].vis, Vis::My);
        let (show, _) = binding_def_and_order(&lower.modules, module, "show");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert!(output.session.role_methods.candidates("secret").is_empty());
        let show_body = binding_body_id(&output, show);
        let lambda_body = match output.session.poly.expr(show_body) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected show lambda"),
        };
        let select = match output.session.poly.expr(lambda_body) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected select expr"),
        };
        assert_eq!(
            output.session.poly.select(select).resolution,
            Some(SelectResolution::RecordField)
        );
    }

    #[test]
    fn private_role_method_is_available_inside_role_companion_scope() {
        let root = parse(
            "role Hidden 'a:\n  my x.secret = x\n  my inside = \\x -> x.secret\nmy outside = \\x -> x.secret\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let hidden = lower.modules.type_decls(module, &Name("Hidden".into()))[0].clone();
        let companion = lower.modules.type_companion(hidden.id).unwrap();
        let method = lower.modules.role_methods(hidden.id)[0].def;
        let inside = lower.modules.value_decls(companion, &Name("inside".into()))[0].def;
        let (outside, _) = binding_def_and_order(&lower.modules, module, "outside");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert!(output.session.role_methods.candidates("secret").is_empty());
        let inside_body = binding_body_id(&output, inside);
        let inside_select = match output.session.poly.expr(inside_body) {
            Expr::Lambda(_, body) => match output.session.poly.expr(*body) {
                Expr::Select(_, select) => *select,
                _ => panic!("expected inside select"),
            },
            _ => panic!("expected inside lambda"),
        };
        assert_eq!(
            output.session.poly.select(inside_select).resolution,
            Some(SelectResolution::TypeclassMethod { member: method })
        );
        let outside_body = binding_body_id(&output, outside);
        let outside_select = match output.session.poly.expr(outside_body) {
            Expr::Lambda(_, body) => match output.session.poly.expr(*body) {
                Expr::Select(_, select) => *select,
                _ => panic!("expected outside select"),
            },
            _ => panic!("expected outside lambda"),
        };
        assert_eq!(
            output.session.poly.select(outside_select).resolution,
            Some(SelectResolution::RecordField)
        );
    }

    #[test]
    fn local_arg_application_flows_empty_stack_to_callee_and_result() {
        let root = parse("my h = \\f -> f 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "h");
        let binding = binding_node(&root, "h").expect("h binding");
        let arg_patterns = binding_arg_patterns(&binding);
        let body = binding_body_expr(&binding).expect("h binding body");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_with_args(&arg_patterns, &body, None)
            .unwrap();

        let types = session.infer.constraints().types();
        let (ret_eff, ret) = lambda_output(&session, computation.value);

        let (arg, _, _, _) = function_lower_bound(&session, computation.value);
        let subtract = {
            let callee = match types.neg(arg) {
                Neg::Var(var) => *var,
                other => panic!("expected callee argument var, got {other:?}"),
            };
            session
                .infer
                .constraints()
                .bounds()
                .of(callee)
                .expect("callee argument should receive function upper bound")
                .uppers()
                .iter()
                .find_map(|bound| {
                    let Neg::Fun { ret_eff, .. } = types.neg(bound.neg) else {
                        return None;
                    };
                    let Neg::Stack { weight, .. } = types.neg(*ret_eff) else {
                        return None;
                    };
                    let [entry] = weight.entries() else {
                        return None;
                    };
                    (entry.pops == 0 && entry.stack == vec![Subtractability::Empty])
                        .then_some(entry.id)
                })
                .expect("callee return effect upper should carry empty push")
        };
        let callee = match types.neg(arg) {
            Neg::Var(var) => *var,
            other => panic!("expected callee argument var, got {other:?}"),
        };
        let callee_bounds = session
            .infer
            .constraints()
            .bounds()
            .of(callee)
            .expect("callee argument should receive function upper bound");
        let call_effect = callee_bounds
            .uppers()
            .iter()
            .find_map(|bound| {
                let Neg::Fun { ret_eff, .. } = types.neg(bound.neg) else {
                    return None;
                };
                let Neg::Stack { inner, weight } = types.neg(*ret_eff) else {
                    return None;
                };
                if !weight_has_empty_stack(weight, subtract) {
                    return None;
                }
                match types.neg(*inner) {
                    Neg::Var(effect) => Some(*effect),
                    _ => None,
                }
            })
            .expect("callee return effect upper should carry empty stack");
        let result_effect = function_result_effect(&session, computation.value);
        assert_eq!(
            assert_pos_stack_pop_var(&session, ret_eff, subtract),
            result_effect
        );
        assert_pos_stack_pop_var(&session, ret, subtract);
        let result_effect_bounds = session
            .infer
            .constraints()
            .bounds()
            .of(result_effect)
            .expect("result effect should receive stacked call effect lower bound");
        assert!(
            result_effect_bounds.lowers().iter().any(|bound| {
                matches!(types.pos(bound.pos), Pos::Var(var) if *var == call_effect)
                    && weight_has_empty_stack(&bound.weights.left, subtract)
            }),
            "application result effect should carry stacked call effect"
        );
    }

    #[test]
    fn unannotated_callback_return_effect_surfaces_without_empty_stack() {
        let root = parse("my h(x, f) = f x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (h, _) = binding_def_and_order(&lower.modules, module, "h");

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, h));
        assert_eq!(rendered, "'a -> ('a -> ['b] 'c) -> ['b] 'c");
    }

    #[test]
    fn annotated_local_arg_keeps_return_effect_unannotated_for_call_subtract() {
        let root = parse("my h(x: [_] _) = x\n");
        let binding = binding_node(&root, "h").expect("h binding");

        assert_eq!(
            local_binding_call_return_effect(&binding),
            LocalCallReturnEffect::Unannotated
        );
    }

    #[test]
    fn module_callee_application_does_not_record_empty_subtract_for_defined_lambda() {
        let root = parse("my f = 1\nmy h = \\x -> f x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "h");
        let expr = binding_expr(&root, "h");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_expr(&expr)
            .unwrap();

        let types = session.infer.constraints().types();
        let (ret_eff, ret) = lambda_output(&session, computation.value);

        assert!(matches!(types.pos(ret_eff), Pos::Var(_)));
        assert!(matches!(types.pos(ret), Pos::Var(_)));
    }

    #[test]
    fn anonymous_lambda_application_does_not_climb_to_outer_defined_predicate() {
        let root = parse("my outer = \\x -> \\f -> f 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "outer");
        let expr = binding_expr(&root, "outer");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_expr(&expr)
            .unwrap();

        let types = session.infer.constraints().types();
        let (ret_eff, ret) = lambda_output(&session, computation.value);

        assert!(matches!(types.pos(ret_eff), Pos::Var(_)));
        assert!(matches!(types.pos(ret), Pos::Var(_)));
    }

    #[test]
    fn lambda_lowering_binds_local_param_and_constrains_function_value() {
        let root = parse("my id = \\x -> x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "id");
        let expr = binding_expr(&root, "id");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_expr(&expr)
            .unwrap();
        let (pat, body) = match session.poly.expr(computation.expr) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected lambda expr"),
        };
        let param = match session.poly.pat(pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected lambda param binding"),
        };
        let body_ref = expr_ref(&session, body);
        let param_value = session.refs.value(body_ref).expect("local ref value slot");

        assert_eq!(session.poly.ref_target(body_ref), Some(param));

        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(computation.value)
            .expect("lambda value should receive a function lower bound");
        let types = session.infer.constraints().types();
        let (arg, arg_eff, ret) = bounds
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun {
                    arg, arg_eff, ret, ..
                } => Some((*arg, *arg_eff, *ret)),
                _ => None,
            })
            .expect("lambda lower bound should be a function");

        assert!(matches!(types.neg(arg), Neg::Var(var) if *var == param_value));
        assert_neg_bottom(types, arg_eff);
        assert!(matches!(types.pos(ret), Pos::Var(var) if *var == param_value));
    }

    #[test]
    fn lambda_multiple_params_lower_to_nested_lambdas() {
        let root = parse("my f = \\() x -> x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        let (first_pat, inner) = match session.poly.expr(computation.expr) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected outer lambda"),
        };
        assert!(matches!(session.poly.pat(first_pat), Pat::Lit(Lit::Unit)));

        let (second_pat, body) = match session.poly.expr(inner) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected inner lambda"),
        };
        let param = match session.poly.pat(second_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected second parameter binding"),
        };
        let body_ref = expr_ref(&session, body);

        assert_eq!(session.poly.ref_target(body_ref), Some(param));
    }

    #[test]
    fn binding_empty_call_header_lowers_to_unit_lambda_param() {
        let root = parse("my f() = 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let f = lower.modules.value_decls(module, &Name("f".into()))[0].def;

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let body = binding_body_id(&output, f);
        let (param, _) = match output.session.poly.expr(body) {
            Expr::Lambda(param, body) => (*param, *body),
            _ => panic!("expected unit lambda body"),
        };
        assert!(matches!(
            output.session.poly.pat(param),
            Pat::Lit(Lit::Unit)
        ));
    }

    #[test]
    fn lambda_param_effect_annotation_adds_stacked_inner_lower() {
        let root = parse("type handled\nmy f = \\x: [handled] 'a -> x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_expr(&expr)
            .unwrap();

        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(computation.value)
            .expect("lambda value should receive a function lower bound");
        let types = session.infer.constraints().types();
        let (arg_eff, ret_eff, ret) = bounds
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun {
                    arg_eff,
                    ret_eff,
                    ret,
                    ..
                } => Some((*arg_eff, *ret_eff, *ret)),
                _ => None,
            })
            .expect("lambda lower bound should be a function");
        let param_effect = match types.neg(arg_eff) {
            Neg::Var(var) => *var,
            other => panic!("expected arg effect var, got {other:?}"),
        };

        // 注釈残差は fresh な内側変数として param effect の下界に入る。self edge にはしない。
        let param_bounds = session
            .infer
            .constraints()
            .bounds()
            .of(param_effect)
            .expect("param effect should receive stacked inner lower bound");
        let subtract = param_bounds
            .lowers()
            .iter()
            .find_map(|bound| {
                if !matches!(types.pos(bound.pos), Pos::Var(var) if *var != param_effect) {
                    return None;
                }
                weight_set_path_id(&bound.weights.left, &["handled"])
            })
            .expect("param effect should carry handled stack on a fresh inner var");
        assert_pos_stack_pop_var(&session, ret_eff, subtract);
        assert_pos_stack_pop_var(&session, ret, subtract);
    }

    #[test]
    fn lambda_param_value_annotation_keeps_outer_arg_effect_bottom() {
        let root = parse("my f = \\x: int -> x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_expr(&expr)
            .unwrap();

        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(computation.value)
            .expect("lambda value should receive a function lower bound");
        let types = session.infer.constraints().types();
        let (arg_eff, ret_eff, ret) = bounds
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun {
                    arg_eff,
                    ret_eff,
                    ret,
                    ..
                } => Some((*arg_eff, *ret_eff, *ret)),
                _ => None,
            })
            .expect("lambda lower bound should be a function");

        assert_neg_bottom(types, arg_eff);
        assert!(matches!(types.pos(ret_eff), Pos::Var(_)));
        assert!(matches!(types.pos(ret), Pos::Var(_)));
    }

    #[test]
    fn recursive_lambda_lowers_to_local_self_binding() {
        let root = parse("my f = \\'self x -> 'self\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let (stmts, tail) = match session.poly.expr(computation.expr) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected recursive lambda block"),
        };
        let [Stmt::Let(_, self_pat, body)] = stmts.as_slice() else {
            panic!("expected recursive self let");
        };
        let self_def = match session.poly.pat(*self_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected recursive self local"),
        };
        let lambda_body = match session.poly.expr(*body) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected recursive lambda body"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, lambda_body)),
            Some(self_def)
        );
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, tail)),
            Some(self_def)
        );
    }

    #[test]
    fn labeled_case_expr_lowers_to_recursive_self_application() {
        let root = parse("my f = case 'go 4: 0 -> 0, n -> 'go 0\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_expr(&expr)
            .unwrap();

        let (self_def, lambda, tail) = recursive_self_block_parts(&session, computation.expr);
        let (tail_callee, tail_arg) = match session.poly.expr(tail) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected case label tail application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, tail_callee)),
            Some(self_def)
        );
        assert!(matches!(
            session.poly.expr(tail_arg),
            Expr::Lit(Lit::Int(4))
        ));

        let case_expr = lambda_body(&session, lambda);
        let arms = match session.poly.expr(case_expr) {
            Expr::Case(_, arms) => arms,
            _ => panic!("expected recursive case body"),
        };
        let recur_callee = match session.poly.expr(arms[1].body) {
            Expr::App(callee, _) => *callee,
            _ => panic!("expected recursive case arm application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, recur_callee)),
            Some(self_def)
        );
    }

    #[test]
    fn labeled_case_lambda_lowers_to_recursive_self_function() {
        let root = parse("my f = \\case 'go: 0 -> 0, n -> 'go 0\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_expr(&expr)
            .unwrap();

        let (self_def, lambda, tail) = recursive_self_block_parts(&session, computation.expr);
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, tail)),
            Some(self_def)
        );
        let case_expr = lambda_body(&session, lambda);
        let arms = match session.poly.expr(case_expr) {
            Expr::Case(_, arms) => arms,
            _ => panic!("expected recursive case lambda body"),
        };
        let recur_callee = match session.poly.expr(arms[1].body) {
            Expr::App(callee, _) => *callee,
            _ => panic!("expected recursive case lambda arm application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, recur_callee)),
            Some(self_def)
        );
    }

    #[test]
    fn labeled_catch_expr_lowers_to_recursive_self_application() {
        let root = parse("my f = catch 'go 1: value -> 'go value\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_expr(&expr)
            .unwrap();

        let (self_def, lambda, tail) = recursive_self_block_parts(&session, computation.expr);
        let (tail_callee, tail_arg) = match session.poly.expr(tail) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected catch label tail application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, tail_callee)),
            Some(self_def)
        );
        assert!(matches!(
            session.poly.expr(tail_arg),
            Expr::Lit(Lit::Int(1))
        ));

        let catch_expr = lambda_body(&session, lambda);
        let arms = match session.poly.expr(catch_expr) {
            Expr::Catch(_, arms) => arms,
            _ => panic!("expected recursive catch body"),
        };
        let recur_callee = match session.poly.expr(arms[0].body) {
            Expr::App(callee, _) => *callee,
            _ => panic!("expected recursive catch arm application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, recur_callee)),
            Some(self_def)
        );
    }

    #[test]
    fn labeled_catch_lambda_lowers_to_recursive_self_function() {
        let root = parse("my f = \\catch 'go: value -> 'go value\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_binding_body_expr(&expr)
            .unwrap();

        let (self_def, lambda, tail) = recursive_self_block_parts(&session, computation.expr);
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, tail)),
            Some(self_def)
        );
        let catch_expr = lambda_body(&session, lambda);
        let arms = match session.poly.expr(catch_expr) {
            Expr::Catch(_, arms) => arms,
            _ => panic!("expected recursive catch lambda body"),
        };
        let recur_callee = match session.poly.expr(arms[0].body) {
            Expr::App(callee, _) => *callee,
            _ => panic!("expected recursive catch lambda arm application"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, recur_callee)),
            Some(self_def)
        );
    }

    #[test]
    fn case_lowering_binds_arm_pattern_local() {
        let root = parse("my f = case 1: n -> n\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let (_scrutinee, arms) = match session.poly.expr(computation.expr) {
            Expr::Case(scrutinee, arms) => (*scrutinee, arms),
            _ => panic!("expected case expr"),
        };
        let [arm] = arms.as_slice() else {
            panic!("expected one case arm");
        };
        let param = match session.poly.pat(arm.pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected arm pattern local"),
        };
        let body_ref = expr_ref(&session, arm.body);

        assert_eq!(session.poly.ref_target(body_ref), Some(param));
        assert!(computation.is_expansive());
    }

    #[test]
    fn case_lambda_lowers_to_lambda_with_case_body() {
        let root = parse("my f = \\case: n -> n\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let (scrutinee_pat, body) = match session.poly.expr(computation.expr) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected case lambda"),
        };
        let scrutinee_def = match session.poly.pat(scrutinee_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected case lambda scrutinee local"),
        };
        let (scrutinee, arms) = match session.poly.expr(body) {
            Expr::Case(scrutinee, arms) => (*scrutinee, arms),
            _ => panic!("expected case lambda body"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, scrutinee)),
            Some(scrutinee_def)
        );
        let [arm] = arms.as_slice() else {
            panic!("expected one case arm");
        };
        let param = match session.poly.pat(arm.pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected arm pattern local"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, arm.body)),
            Some(param)
        );
    }

    #[test]
    fn case_constructor_pattern_resolves_path_reference() {
        let root = parse("mod m:\n  my some = 0\nmy x = 1\nmy f = case x: m::some y -> y\n");
        let lower = lower_module_map(&root);
        let root_module = lower.modules.root_id();
        let m = lower.modules.module_decls(root_module, &Name("m".into()))[0].module;
        let constructor = lower.modules.value_decls(m, &Name("some".into()))[0].def;
        let (f, _) = binding_def_and_order(&lower.modules, root_module, "f");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let case = binding_body_id(&output, f);
        let (_scrutinee, arms) = match output.session.poly.expr(case) {
            Expr::Case(scrutinee, arms) => (*scrutinee, arms),
            _ => panic!("expected case expr"),
        };
        let [arm] = arms.as_slice() else {
            panic!("expected one case arm");
        };
        let (reference, payloads) = match output.session.poly.pat(arm.pat) {
            Pat::Con(reference, payloads) => (*reference, payloads),
            _ => panic!("expected constructor pattern"),
        };
        let [payload] = payloads.as_slice() else {
            panic!("expected one constructor payload");
        };
        let payload = match output.session.poly.pat(*payload) {
            Pat::Var(def) => *def,
            _ => panic!("expected constructor payload local"),
        };
        let body_ref = expr_ref(&output.session, arm.body);

        assert_eq!(output.session.poly.ref_target(reference), Some(constructor));
        assert_eq!(output.session.poly.ref_target(body_ref), Some(payload));
    }

    #[test]
    fn constructor_pattern_payload_flows_from_scrutinee_without_annotation() {
        let root = parse(concat!(
            "pub enum opt 'a = none | some 'a\n",
            "my id_from_some o = case o:\n",
            "  opt::some x -> x\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (id_from_some, _) = binding_def_and_order(&lower.modules, module, "id_from_some");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, id_from_some));
        assert_eq!(rendered, "opt 'a -> 'a");
    }

    #[test]
    fn constructor_pattern_spaced_tuple_group_matches_tuple_payload_fields() {
        let root = parse(concat!(
            "pub enum bound = unbounded | included int\n",
            "pub enum range = within (bound, bound)\n",
            "my start r = case r:\n",
            "  range::within (start, _) -> start\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (start, _) = binding_def_and_order(&lower.modules, module, "start");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let rendered =
            poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, start));
        assert_eq!(rendered, "range -> bound");
    }

    #[test]
    fn constructor_pattern_payload_participates_in_guard_role_method() {
        let root = parse_with_junction_std(concat!(
            "role Ord 'a:\n",
            "  our x.le: 'a -> bool\n",
            "pub enum view 'a = empty | leaf 'a\n",
            "my keep v x = case v:\n",
            "  view::leaf y if y.le x -> y\n",
        ));
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (keep, _) = binding_def_and_order(&lower.modules, module, "keep");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let scheme = def_scheme(&output, keep);
        assert!(matches!(
            scheme.role_predicates[0].inputs[0],
            poly::types::RolePredicateArg::Covariant(_)
        ));
        let rendered = poly::dump::format_scheme(&output.session.poly.typ, scheme);
        assert_eq!(rendered, "view('b & 'a) -> 'a -> 'b where Ord('a | 'b)");
    }

    #[test]
    fn catch_lowering_binds_value_arm_pattern_local() {
        let root = parse("my f = catch 1: value -> value\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let (_body, arms) = match session.poly.expr(computation.expr) {
            Expr::Catch(body, arms) => (*body, arms),
            _ => panic!("expected catch expr"),
        };
        let [arm] = arms.as_slice() else {
            panic!("expected one catch arm");
        };
        assert!(arm.continuation.is_none());
        let value = match session.poly.pat(arm.pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected value arm pattern local"),
        };
        let body_ref = expr_ref(&session, arm.body);

        assert_eq!(session.poly.ref_target(body_ref), Some(value));
        assert!(computation.is_expansive());
    }

    #[test]
    fn catch_lambda_lowers_to_lambda_with_catch_body() {
        let root = parse("my f = \\catch: value -> value\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        let (scrutinee_pat, body) = match session.poly.expr(computation.expr) {
            Expr::Lambda(pat, body) => (*pat, *body),
            _ => panic!("expected catch lambda"),
        };
        let scrutinee_def = match session.poly.pat(scrutinee_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected catch lambda scrutinee local"),
        };
        let (scrutinee, arms) = match session.poly.expr(body) {
            Expr::Catch(scrutinee, arms) => (*scrutinee, arms),
            _ => panic!("expected catch lambda body"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, scrutinee)),
            Some(scrutinee_def)
        );
        let [arm] = arms.as_slice() else {
            panic!("expected one catch arm");
        };
        assert!(arm.continuation.is_none());
        let param = match session.poly.pat(arm.pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected value arm pattern local"),
        };
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, arm.body)),
            Some(param)
        );
    }

    #[test]
    fn catch_effect_arm_binds_payload_and_continuation_locals() {
        let root = parse("my run = 1\nmy f = catch run:\n  eff x, k -> k x\n  value -> value\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (f, _) = binding_def_and_order(&lower.modules, module, "f");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let catch = binding_body_id(&output, f);
        let (_body, arms) = match output.session.poly.expr(catch) {
            Expr::Catch(body, arms) => (*body, arms),
            _ => panic!("expected catch expr"),
        };
        let [effect_arm, value_arm] = arms.as_slice() else {
            panic!("expected effect arm followed by value arm");
        };
        let continuation = effect_arm
            .continuation
            .expect("expected effect arm continuation");
        assert!(value_arm.continuation.is_none());

        let payload = match output.session.poly.pat(effect_arm.pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected effect payload local"),
        };
        let continuation = match output.session.poly.pat(continuation) {
            Pat::Var(def) => *def,
            _ => panic!("expected continuation local"),
        };
        let (callee, arg) = match output.session.poly.expr(effect_arm.body) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected continuation application"),
        };
        let k_ref = expr_ref(&output.session, callee);
        let x_ref = expr_ref(&output.session, arg);
        let k_value = output
            .session
            .refs
            .value(k_ref)
            .expect("continuation ref value");

        assert_eq!(output.session.poly.ref_target(k_ref), Some(continuation));
        assert_eq!(output.session.poly.ref_target(x_ref), Some(payload));
        let bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(k_value)
            .expect("continuation should receive function bounds");
        let types = output.session.infer.constraints().types();
        assert!(
            bounds
                .lowers()
                .iter()
                .any(|bound| matches!(types.pos(bound.pos), Pos::Fun { .. }))
        );
        assert!(
            bounds
                .uppers()
                .iter()
                .any(|bound| matches!(types.neg(bound.neg), Neg::Fun { .. }))
        );
    }

    #[test]
    fn catch_complete_effect_handler_flows_rest_effect_to_result() {
        let root = parse(
            "act out:\n  our say: int -> unit\nmy run = 1\nmy f = catch run:\n  out::say msg, k -> 0\n  value -> value\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        assert!(!effect_has_lower_source_with_row_upper(
            &session,
            computation.effect,
            &["out"],
        ));
    }

    #[test]
    fn catch_incomplete_effect_handler_flows_scrutinee_effect_to_result() {
        let root = parse(
            "act choose:\n  our branch: unit -> int\n  our reject: unit -> never\nmy run = 1\nmy f = catch run:\n  choose::branch(), k -> 0\n  value -> value\n",
        );
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
        let expr = binding_expr(&root, "f");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        assert!(effect_has_lower_source_with_row_upper(
            &session,
            computation.effect,
            &["choose"],
        ));
    }

    #[test]
    fn body_lowering_keeps_lambda_local_refs_out_of_scc_edges() {
        let root = parse("my id = \\x -> x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (def, _) = binding_def_and_order(&lower.modules, module, "id");

        let mut output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let events = output.session.take_scc_events();
        assert!(events
            .iter()
            .any(|event| matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![def])));
        assert!(!events.iter().any(|event| {
            matches!(
                event,
                SccEvent::ComponentEdgeAdded { .. } | SccEvent::MergeComponents { .. }
            )
        }));
    }

    fn expr_ref(session: &AnalysisSession, expr: poly::expr::ExprId) -> RefId {
        match session.poly.expr(expr) {
            Expr::Var(reference) => *reference,
            _ => panic!("expected var expr"),
        }
    }

    fn recursive_self_block_parts(
        session: &AnalysisSession,
        expr: poly::expr::ExprId,
    ) -> (DefId, poly::expr::ExprId, poly::expr::ExprId) {
        let (stmts, tail) = match session.poly.expr(expr) {
            Expr::Block(stmts, Some(tail)) => (stmts, *tail),
            _ => panic!("expected recursive self block"),
        };
        let [Stmt::Let(_, self_pat, body)] = stmts.as_slice() else {
            panic!("expected recursive self let");
        };
        let self_def = match session.poly.pat(*self_pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected recursive self local"),
        };
        (self_def, *body, tail)
    }

    fn lambda_body(session: &AnalysisSession, expr: poly::expr::ExprId) -> poly::expr::ExprId {
        match session.poly.expr(expr) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected lambda expr"),
        }
    }

    fn find_select_by_name(
        session: &AnalysisSession,
        expr: poly::expr::ExprId,
        name: &str,
    ) -> Option<SelectId> {
        let mut children = Vec::new();
        match session.poly.expr(expr) {
            Expr::Select(receiver, select) => {
                if session.poly.select(*select).name == name {
                    return Some(*select);
                }
                children.push(*receiver);
            }
            Expr::App(callee, arg) | Expr::RefSet(callee, arg) => {
                children.push(*callee);
                children.push(*arg);
            }
            Expr::Lambda(_, body) => children.push(*body),
            Expr::Tuple(items) | Expr::PolyVariant(_, items) => {
                children.extend(items.iter().copied());
            }
            Expr::Record { fields, spread } => {
                children.extend(fields.iter().map(|(_, expr)| *expr));
                match spread {
                    RecordSpread::Head(expr) | RecordSpread::Tail(expr) => children.push(*expr),
                    RecordSpread::None => {}
                }
            }
            Expr::Case(scrutinee, arms) => {
                children.push(*scrutinee);
                children.extend(arms.iter().filter_map(|arm| arm.guard));
                children.extend(arms.iter().map(|arm| arm.body));
            }
            Expr::Catch(scrutinee, arms) => {
                children.push(*scrutinee);
                children.extend(arms.iter().filter_map(|arm| arm.guard));
                children.extend(arms.iter().map(|arm| arm.body));
            }
            Expr::Block(statements, tail) => {
                for statement in statements {
                    match statement {
                        Stmt::Let(_, _, body) | Stmt::Expr(body) => children.push(*body),
                        Stmt::Module(_, body) => {
                            for statement in body {
                                match statement {
                                    Stmt::Let(_, _, body) | Stmt::Expr(body) => {
                                        children.push(*body);
                                    }
                                    Stmt::Module(_, _) => {}
                                }
                            }
                        }
                    }
                }
                if let Some(tail) = tail {
                    children.push(*tail);
                }
            }
            Expr::Lit(_) | Expr::PrimitiveOp(_) | Expr::Var(_) => {}
        }
        children
            .into_iter()
            .find_map(|child| find_select_by_name(session, child, name))
    }

    fn lambda_output(session: &AnalysisSession, value: TypeVar) -> (PosId, PosId) {
        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(value)
            .expect("lambda value should receive a function lower bound");
        let types = session.infer.constraints().types();
        bounds
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun { ret_eff, ret, .. } => Some((*ret_eff, *ret)),
                _ => None,
            })
            .expect("lambda lower bound should be a function")
    }

    fn function_result_effect(session: &AnalysisSession, value: TypeVar) -> TypeVar {
        let (ret_eff, _) = lambda_output(session, value);
        match session.infer.constraints().types().pos(ret_eff) {
            Pos::Stack { inner, .. } => match session.infer.constraints().types().pos(*inner) {
                Pos::Var(effect) => *effect,
                other => panic!("expected stacked result effect var, got {other:?}"),
            },
            Pos::Var(effect) => *effect,
            other => panic!("expected result effect var, got {other:?}"),
        }
    }

    fn assert_neg_bottom(types: &poly::types::TypeArena, row: NegId) {
        match types.neg(row) {
            Neg::Bot => {}
            other => panic!("expected negative bottom, got {other:?}"),
        }
    }

    fn assert_role_arg_is_exact_con(
        session: &AnalysisSession,
        arg: &crate::roles::RoleConstraintArg,
        name: &str,
    ) {
        let types = session.infer.constraints().types();
        assert!(matches!(
            types.pos(arg.lower),
            Pos::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
        ));
        assert!(matches!(
            types.neg(arg.upper),
            Neg::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
        ));
    }

    fn assert_var_has_exact_con_bound(session: &AnalysisSession, var: TypeVar, name: &str) {
        let types = session.infer.constraints().types();
        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(var)
            .expect("variable should receive bounds");
        assert!(bounds.lowers().iter().any(|bound| {
            matches!(
                types.pos(bound.pos),
                Pos::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
            )
        }));
        assert!(bounds.uppers().iter().any(|bound| {
            matches!(
                types.neg(bound.neg),
                Neg::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
            )
        }));
    }

    fn assert_var_has_lower_con_bound(session: &AnalysisSession, var: TypeVar, name: &str) {
        let types = session.infer.constraints().types();
        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(var)
            .expect("variable should receive bounds");
        assert!(bounds.lowers().iter().any(|bound| {
            matches!(
                types.pos(bound.pos),
                Pos::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
            )
        }));
    }

    fn assert_var_has_lower_con_path(session: &AnalysisSession, var: TypeVar, path: &[&str]) {
        let expected = path
            .iter()
            .map(|segment| (*segment).to_string())
            .collect::<Vec<_>>();
        let types = session.infer.constraints().types();
        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(var)
            .expect("variable should receive bounds");
        assert!(bounds.lowers().iter().any(|bound| {
            matches!(
                types.pos(bound.pos),
                Pos::Con(path, args) if path == &expected && args.is_empty()
            )
        }));
    }

    fn effect_has_lower_source_with_row_upper(
        session: &AnalysisSession,
        effect: TypeVar,
        path: &[&str],
    ) -> bool {
        let Some(bounds) = session.infer.constraints().bounds().of(effect) else {
            return false;
        };
        let types = session.infer.constraints().types();
        bounds.lowers().iter().any(|bound| {
            let Pos::Var(source) = types.pos(bound.pos) else {
                return false;
            };
            var_has_row_upper(session, *source, path)
        })
    }

    fn var_has_row_upper(session: &AnalysisSession, var: TypeVar, path: &[&str]) -> bool {
        let Some(bounds) = session.infer.constraints().bounds().of(var) else {
            return false;
        };
        let types = session.infer.constraints().types();
        bounds
            .uppers()
            .iter()
            .any(|bound| neg_row_contains_path(types, bound.neg, path))
    }

    fn neg_row_contains_path(types: &poly::types::TypeArena, neg: NegId, path: &[&str]) -> bool {
        let Neg::Row(items, _) = types.neg(neg) else {
            return false;
        };
        items.iter().any(|item| match types.neg(*item) {
            Neg::Con(found, args) => {
                args.is_empty()
                    && found
                        .iter()
                        .map(|segment| segment.as_str())
                        .eq(path.iter().copied())
            }
            _ => false,
        })
    }

    #[test]
    fn body_lowering_writes_let_body_and_def_type() {
        let root = parse("my a = 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (def, _) = binding_def_and_order(&lower.modules, module, "a");

        let mut output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let body = binding_body_id(&output, def);
        assert!(matches!(
            output.session.poly.expr(body),
            Expr::Lit(Lit::Int(1))
        ));
        assert!(output.typing.def(def).is_some());
        assert!(output
            .session
            .take_scc_events()
            .iter()
            .any(|event| matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![def])));
    }

    #[test]
    fn body_lowering_resolves_references_after_queue_drain() {
        let root = parse("my a = 1\nmy b = a\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (target, _) = binding_def_and_order(&lower.modules, module, "a");
        let (owner, _) = binding_def_and_order(&lower.modules, module, "b");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let body = binding_body_id(&output, owner);
        let reference = expr_ref(&output.session, body);
        assert_eq!(output.session.poly.ref_target(reference), Some(target));
    }

    #[test]
    fn body_lowering_resolves_import_alias_references_after_queue_drain() {
        let root = parse("mod m:\n  my a = 1\nuse m::a as imported\nmy b = imported\n");
        let lower = lower_module_map(&root);
        let root_module = lower.modules.root_id();
        let m = lower.modules.module_decls(root_module, &Name("m".into()))[0].module;
        let target = lower.modules.value_decls(m, &Name("a".into()))[0].def;
        let (owner, _) = binding_def_and_order(&lower.modules, root_module, "b");

        let output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let body = binding_body_id(&output, owner);
        let reference = expr_ref(&output.session, body);
        assert_eq!(output.session.poly.ref_target(reference), Some(target));
    }

    #[test]
    fn body_lowering_opens_self_recursion_from_registered_root() {
        let root = parse("my f = \\x -> f\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (def, _) = binding_def_and_order(&lower.modules, module, "f");

        let mut output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let def_root = output.typing.def(def).expect("def root");
        let body = binding_body_id(&output, def);
        let lambda_body = match output.session.poly.expr(body) {
            Expr::Lambda(_, body) => *body,
            _ => panic!("expected lambda body"),
        };
        let reference = expr_ref(&output.session, lambda_body);
        let use_value = output
            .session
            .refs
            .value(reference)
            .expect("self ref use value");
        let events = output.session.take_scc_events();
        assert!(events.iter().any(|event| {
            matches!(
                event,
                SccEvent::OpenUse {
                    target,
                    target_root,
                    use_value: event_use,
                } if *target == def && *target_root == def_root && *event_use == use_value
            )
        }));

        let root_pos = output.session.infer.alloc_pos(Pos::Var(def_root));
        let use_bounds = output
            .session
            .infer
            .constraints()
            .bounds()
            .of(use_value)
            .expect("self ref use bounds");
        assert!(
            use_bounds
                .lowers()
                .iter()
                .any(|bound| bound.pos == root_pos)
        );
    }

    #[test]
    fn body_lowering_keeps_forward_cycle_in_one_scc() {
        let root = parse("my a = b\nmy b = a\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (a, _) = binding_def_and_order(&lower.modules, module, "a");
        let (b, _) = binding_def_and_order(&lower.modules, module, "b");

        let mut output = lower_binding_bodies(&root, lower);

        assert_eq!(output.errors, Vec::new());
        let events = output.session.take_scc_events();
        assert!(events.iter().any(|event| {
            matches!(event, SccEvent::MergeComponents { merged, .. } if merged == &vec![a, b] || merged == &vec![b, a])
        }));
        assert!(events.iter().any(|event| {
            matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![a, b] || component == &vec![b, a])
        }));
    }
}
