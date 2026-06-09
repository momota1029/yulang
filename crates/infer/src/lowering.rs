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
use poly::expr::{Def, DefId, Expr, Lit, Pat, PatId, RefId};
use poly::types::{Neg, NegId, Neu, Pos, PosId, SubtractId, Subtractability, TypeVar};
use rustc_hash::FxHashMap;

use crate::analysis::{AnalysisSession, AnalysisWork};
use crate::annotation::{
    AnnBuildError, AnnComputationTarget, AnnConstraintError, AnnConstraintLowerer, AnnSelfAlias,
    AnnType, AnnTypeBuilder, AnnTypeVarId,
};
use crate::scc::SccInput;
use crate::typing::Typing;
use crate::uses::{RefUse, SelectionUse};
use crate::{
    ActMethodDecl, LoadedFileCsts, LoadedFilesError, Lower, ModuleChildDecl, ModuleId, ModuleOrder,
    ModuleTable, ModuleTypeDecl, TypeDeclId, TypeMethodDecl, TypeMethodReceiver,
    lower_loaded_file_csts_module_map,
};

type Cst = SyntaxNode<YulangLanguage>;

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
}

impl BodyLowerer {
    fn new(lower: Lower) -> Self {
        let labels = lower.modules.dump_labels();
        let mut session = AnalysisSession::new(lower.arena);
        register_declared_type_methods(&mut session, &lower.modules);
        register_declared_act_methods(&mut session, &lower.modules);
        Self {
            session,
            modules: lower.modules,
            typing: Typing::new(),
            labels,
            errors: Vec::new(),
            value_cursors: FxHashMap::default(),
            module_cursors: FxHashMap::default(),
            type_cursors: FxHashMap::default(),
        }
    }

    fn finish(self) -> BodyLowering {
        BodyLowering {
            session: self.session,
            modules: self.modules,
            typing: self.typing,
            labels: self.labels,
            errors: self.errors,
        }
    }

    fn lower_block(&mut self, block: &Cst, module: ModuleId) {
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => self.lower_binding(&child, module),
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, module),
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl => self.lower_type_decl_with_body(&child, module),
                SyntaxKind::ActDecl => self.lower_act_decl_body(&child, module),
                _ => {}
            }
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
        let Some(name) = crate::binding_name(node) else {
            return;
        };
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

        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            decl.order,
            decl.def,
            &mut self.labels,
        )
        .with_self_alias(self_alias.clone())
        .lower_binding_body_expr(&expr);
        match lowered {
            Ok(computation) => {
                match self.connect_binding_annotation(
                    node,
                    module,
                    decl.order,
                    self_alias,
                    root,
                    computation,
                ) {
                    Ok(()) => self.finish_binding(decl.def, name, root, computation),
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

    fn lower_type_decl_with_body(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::type_decl_name(node) else {
            return;
        };
        let Some(decl) = self.next_type_decl(module, &name) else {
            return;
        };
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
                _ => {}
            }
        }
    }

    fn lower_act_decl_body(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::type_decl_name(node) else {
            return;
        };
        let Some(decl) = self.next_type_decl(module, &name) else {
            return;
        };
        let Some(body) = crate::act_decl_body(node) else {
            return;
        };
        let Some(companion) = self.modules.type_companion(decl.id) else {
            return;
        };
        let mut method_cursor = 0usize;
        for child in body.children() {
            match child.kind() {
                SyntaxKind::Binding if crate::act_operation_binding(&child) => {}
                SyntaxKind::Binding if crate::type_method_binding(&child).is_some() => {
                    let method = self
                        .modules
                        .act_methods(decl.id)
                        .get(method_cursor)
                        .cloned();
                    method_cursor += usize::from(method.is_some());
                    if let Some(method) = method {
                        self.lower_act_method_binding(&child, companion, &method);
                    }
                }
                SyntaxKind::Binding => self.lower_binding(&child, companion),
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, companion),
                _ => {}
            }
        }
    }

    fn lower_act_method_binding(&mut self, node: &Cst, module: ModuleId, method: &ActMethodDecl) {
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
        .lower_act_method_body_expr(
            &expr,
            method.receiver.clone(),
            method.owner,
            binding_type_expr(node),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation);
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
        .with_self_alias(Some(self_alias.clone()))
        .lower_type_method_body_expr(
            &expr,
            method.receiver.clone(),
            method.receiver_kind,
            owner.id,
            &self_alias.type_vars,
            binding_type_expr(node),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation);
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
        root: TypeVar,
        computation: Computation,
    ) -> Result<(), LoweringError> {
        let Some(type_expr) = binding_type_expr(node) else {
            return Ok(());
        };
        let mut builder = ann_type_builder(&self.modules, module, site, self_alias);
        let ann = builder
            .build_type_expr(&type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
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

    fn finish_binding(
        &mut self,
        def: poly::expr::DefId,
        name: Name,
        root: TypeVar,
        computation: Computation,
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
        self.constrain_def_body(root, computation.value);
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
        let decl = self.modules.value_decls(module, name).get(*cursor).cloned();
        *cursor += usize::from(decl.is_some());
        decl
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
}

fn register_declared_type_methods(session: &mut AnalysisSession, modules: &ModuleTable) {
    for method in modules.all_type_methods() {
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

fn register_declared_act_methods(session: &mut AnalysisSession, modules: &ModuleTable) {
    for method in modules.all_act_methods() {
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
    locals: Vec<LocalBinding>,
    function_frames: Vec<FunctionPredicateFrame>,
}

impl<'a> ExprLowerer<'a> {
    pub fn new(
        session: &'a mut AnalysisSession,
        modules: &'a ModuleTable,
        module: ModuleId,
        site: ModuleOrder,
        parent: poly::expr::DefId,
    ) -> Self {
        Self {
            session,
            modules,
            module,
            site,
            parent,
            labels: None,
            self_alias: None,
            locals: Vec::new(),
            function_frames: Vec::new(),
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
        Self {
            session,
            modules,
            module,
            site,
            parent,
            labels: Some(labels),
            self_alias: None,
            locals: Vec::new(),
            function_frames: Vec::new(),
        }
    }

    pub fn with_self_alias(mut self, self_alias: Option<AnnSelfAlias>) -> Self {
        self.self_alias = self_alias;
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

    fn lower_type_method_body_expr(
        &mut self,
        node: &Cst,
        receiver: Name,
        receiver_kind: TypeMethodReceiver,
        owner: TypeDeclId,
        type_vars: &[String],
        result_type_expr: Option<Cst>,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
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
        let pat =
            self.bind_pattern_local(receiver, receiver_value, LocalCallReturnEffect::Annotated);
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_expr_with_lambda_scope(node, LambdaScope::Defined);
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        if let Some(type_expr) = result_type_expr {
            self.connect_type_method_result_annotation(
                body,
                &type_expr,
                &mut ann_builder,
                &mut ann_solver_vars,
            )?;
        }

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.never_neg();
        let body_effect = self.alloc_pos(Pos::Var(body.effect));
        let body_value = self.alloc_pos(Pos::Var(body.value));
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Defined, Vec::new(), frame);
        let ret_eff = self.wrap_pos_with_subtracts(body_effect, &predicate_subtracts);
        let ret = self.wrap_pos_with_subtracts(body_value, &predicate_subtracts);
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
        receiver: Name,
        owner: TypeDeclId,
        result_type_expr: Option<Cst>,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
        );
        let mut ann_solver_vars = FxHashMap::default();

        let receiver_value = self.fresh_type_var();
        let receiver_effect = self.fresh_type_var();
        let receiver_subtract = self.connect_act_method_receiver_effect(receiver_effect, owner)?;
        let before_locals = self.locals.len();
        let pat =
            self.bind_pattern_local(receiver, receiver_value, LocalCallReturnEffect::Annotated);
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_expr_with_lambda_scope(node, LambdaScope::Defined);
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        if let Some(type_expr) = result_type_expr {
            self.connect_type_method_result_annotation(
                body,
                &type_expr,
                &mut ann_builder,
                &mut ann_solver_vars,
            )?;
        }

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.alloc_neg(Neg::Var(receiver_effect));
        let body_effect = self.alloc_pos(Pos::Var(body.effect));
        let body_value = self.alloc_pos(Pos::Var(body.value));
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Defined, vec![receiver_subtract], frame);
        let ret_eff = self.wrap_pos_with_subtracts(body_effect, &predicate_subtracts);
        let ret = self.wrap_pos_with_subtracts(body_value, &predicate_subtracts);
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
        self.session
            .infer
            .subtract_fact(effect, subtract, Subtractability::Set(path, Vec::new()));
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
                    Pos::Con(vec!["ref".into()], vec![effect_arg, payload_arg]),
                );
                self.constrain_upper(
                    receiver_value,
                    Neg::Con(vec!["ref".into()], vec![effect_arg, payload_arg]),
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
        self.session.infer.alloc_neu(Neu::Bounds(lower, var, upper))
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
        let mut items = node
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item));
        let Some(head) = items.next() else {
            return Ok(self.unit_expr());
        };

        let mut acc = self.lower_head(head, head_lambda_scope)?;
        for item in items {
            match item {
                NodeOrToken::Node(child)
                    if matches!(child.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC) =>
                {
                    acc = self.apply_arguments(acc, &child)?;
                }
                NodeOrToken::Node(child) if child.kind() == SyntaxKind::Field => {
                    acc = self.lower_field_selection(acc, &child)?;
                }
                NodeOrToken::Node(child) => {
                    return Err(LoweringError::UnsupportedSyntax { kind: child.kind() });
                }
                NodeOrToken::Token(token) => {
                    return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
                }
            }
        }
        Ok(acc)
    }

    fn lower_head(
        &mut self,
        head: NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        match head {
            NodeOrToken::Token(token) => match token.kind() {
                SyntaxKind::Ident | SyntaxKind::SigilIdent => {
                    self.lower_name(Name(token.text().to_string()))
                }
                SyntaxKind::Number => self.lower_number(token.text()),
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
            SyntaxKind::CaseExpr => self.lower_case(node),
            SyntaxKind::CatchExpr => self.lower_catch(node),
            SyntaxKind::Number => self.lower_number(&node.text().to_string()),
            SyntaxKind::Paren => self.lower_paren(node, lambda_scope),
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
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .last()
        else {
            return Err(LoweringError::MissingLambdaBody);
        };
        let mut ann_builder = ann_type_builder(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
        );
        let mut ann_solver_vars = FxHashMap::default();
        self.lower_lambda_params(
            patterns.as_slice(),
            &body,
            lambda_scope,
            &mut ann_builder,
            &mut ann_solver_vars,
        )
    }

    fn lower_lambda_params(
        &mut self,
        patterns: &[Cst],
        body: &Cst,
        lambda_scope: LambdaScope,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<Computation, LoweringError> {
        let Some((pattern, rest)) = patterns.split_first() else {
            return self.lower_expr(body);
        };

        let param_value = self.fresh_type_var();
        let annotation = self.connect_lambda_pattern_annotation(
            pattern,
            param_value,
            ann_builder,
            ann_solver_vars,
        )?;
        let before_locals = self.locals.len();
        let pat = self.lower_lambda_pattern(pattern, param_value, annotation.call_return_effect)?;
        self.function_frames
            .push(FunctionPredicateFrame::new(lambda_scope));
        let previous_level = self.session.infer.enter_child_level();
        let body_result =
            self.lower_lambda_params(rest, body, lambda_scope, ann_builder, ann_solver_vars);
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
        let body_effect = self.alloc_pos(Pos::Var(body.effect));
        let body_value = self.alloc_pos(Pos::Var(body.value));
        let predicate_subtracts =
            self.lambda_predicate_subtracts(lambda_scope, annotation.subtracts, frame);
        let ret_eff = self.wrap_pos_with_subtracts(body_effect, &predicate_subtracts);
        let ret = self.wrap_pos_with_subtracts(body_value, &predicate_subtracts);
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
        let result = lowerer
            .connect_computation(AnnComputationTarget { value, effect }, &ann)
            .map(|subtracts| LambdaPatternAnnotation {
                arg_eff,
                subtracts,
                call_return_effect: LocalCallReturnEffect::Annotated,
            })
            .map_err(|error| LoweringError::AnnotationConstraint { error });
        *ann_solver_vars = lowerer.into_vars();
        result
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

    fn lower_number(&mut self, text: &str) -> Result<Computation, LoweringError> {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let (lit, primitive) = parse_number_lit(text)?;

        self.constrain_lower(value, primitive_type(primitive));
        let expr = self.session.poly.add_expr(Expr::Lit(lit));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_name(&mut self, name: Name) -> Result<Computation, LoweringError> {
        if let Some(local) = self.local_binding(&name) {
            return Ok(self.lower_local_name(name, local));
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
        self.session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: reference,
            target,
        });

        let expr = self.session.poly.add_expr(Expr::Var(reference));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_local_name(&mut self, name: Name, local: LocalBinding) -> Computation {
        let effect = self.fresh_exact_pure_effect();
        let reference = self.session.poly.add_ref();
        self.session.poly.resolve_ref(reference, local.def);
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, name.0);
        }
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value: local.value,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Var(reference));
        Computation::value(expr, local.value, effect)
    }

    fn local_binding(&self, name: &Name) -> Option<LocalBinding> {
        self.locals
            .iter()
            .rev()
            .find(|local| &local.name == name)
            .cloned()
    }

    fn apply_arguments(
        &mut self,
        mut callee: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let args = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .collect::<Vec<_>>();
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

    fn lower_field_selection(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let name = field_name(node).ok_or(LoweringError::MissingFieldName)?;
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
            },
        );
        let expr = self
            .session
            .poly
            .add_expr(Expr::Select(receiver.expr, select));
        Ok(Computation::new(
            expr,
            result_value,
            result_effect,
            receiver.evaluation,
        ))
    }

    fn make_app(&mut self, callee: Computation, arg: Computation) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let call_effect = self.fresh_type_var();

        let arg_value = self.alloc_pos(Pos::Var(arg.value));
        let arg_effect = self.alloc_pos(Pos::Var(arg.effect));
        let return_effect = self.alloc_neg(Neg::Var(call_effect));
        let return_value = self.alloc_neg(Neg::Var(result_value));
        let callee_upper = self.alloc_neg(Neg::Fun {
            arg: arg_value,
            arg_eff: arg_effect,
            ret_eff: return_effect,
            ret: return_value,
        });
        self.subtype(Pos::Var(callee.value), callee_upper);
        self.subtype_var_to_var(callee.effect, result_effect);
        self.subtype_var_to_var(arg.effect, result_effect);
        self.subtype_var_to_var(call_effect, result_effect);
        self.record_unannotated_local_callee_return_effect(&callee, call_effect);

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

    fn record_unannotated_local_callee_return_effect(
        &mut self,
        callee: &Computation,
        call_effect: TypeVar,
    ) {
        if !self
            .function_frames
            .last()
            .is_some_and(|frame| frame.scope == LambdaScope::Defined)
        {
            return;
        }
        let Some(def) = self.local_callee_def(callee) else {
            return;
        };
        let Some(local) = self.local_binding_by_def(def) else {
            return;
        };
        if local.call_return_effect != LocalCallReturnEffect::Unannotated {
            return;
        }

        let subtract = self.session.infer.fresh_subtract_id();
        self.session
            .infer
            .subtract_fact(call_effect, subtract, Subtractability::Empty);
        let frame = self
            .function_frames
            .last_mut()
            .expect("checked that function frame exists");
        frame.subtracts.push(subtract);
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

    fn subtype(&mut self, lower: Pos, upper: NegId) {
        let lower = self.alloc_pos(lower);
        self.session.infer.subtype(lower, upper);
    }

    fn wrap_pos_with_subtracts(&mut self, pos: PosId, subtracts: &[SubtractId]) -> PosId {
        subtracts.iter().fold(pos, |inner, subtract| {
            self.alloc_pos(Pos::NonSubtract(inner, *subtract))
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
    call_return_effect: LocalCallReturnEffect,
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
    subtracts: Vec<SubtractId>,
    call_return_effect: LocalCallReturnEffect,
}

pub use crate::typing::{Computation, Evaluation};

#[derive(Debug, Clone, PartialEq, Eq)]
/// expression lowering が構造化して返す失敗。
pub enum LoweringError {
    UnsupportedSyntax { kind: SyntaxKind },
    UnsupportedPatternSyntax { kind: SyntaxKind },
    UnresolvedName { name: Name },
    InvalidNumber { text: String },
    MissingLambdaBody,
    MissingCaseScrutinee,
    MissingCaseArmPattern,
    MissingCaseArmBody,
    MissingCatchScrutinee,
    MissingCatchArmPattern,
    MissingCatchArmBody,
    MissingFieldName,
    AnnotationBuild { error: AnnBuildError },
    AnnotationConstraint { error: AnnConstraintError },
}

fn item_is_trivia(item: &NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>) -> bool {
    item.as_token()
        .is_some_and(|token| matches!(token.kind(), SyntaxKind::Space | SyntaxKind::LineComment))
}

fn field_name(node: &Cst) -> Option<String> {
    let token = node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::DotField)?;
    Some(token.text().trim_start_matches('.').to_string())
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

fn binding_body_expr(binding: &Cst) -> Option<Cst> {
    crate::child_node(binding, SyntaxKind::BindingBody)?
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

fn binding_type_expr(binding: &Cst) -> Option<Cst> {
    let header = crate::child_node(binding, SyntaxKind::BindingHeader)?;
    let pattern = crate::child_node(&header, SyntaxKind::Pattern)?;
    pattern_type_expr(&pattern)
}

fn pattern_type_expr(pattern: &Cst) -> Option<Cst> {
    if let Some(type_expr) = pattern
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeAnn)
        .and_then(|ann| {
            ann.children()
                .find(|child| child.kind() == SyntaxKind::TypeExpr)
        })
    {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower_module_map;
    use crate::scc::SccEvent;
    use poly::expr::{DefId, ExprId, Pat, RefId, SelectResolution};

    fn parse(src: &str) -> Cst {
        SyntaxNode::new_root(yulang_parser::parse_module_to_green(src))
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

    fn binding_body_id(output: &BodyLowering, def: DefId) -> ExprId {
        match output.session.poly.defs.get(def) {
            Some(Def::Let {
                body: Some(body), ..
            }) => *body,
            _ => panic!("expected lowered let body"),
        }
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
        let fact = output
            .session
            .infer
            .constraints()
            .subtracts()
            .facts(effect)
            .iter()
            .find(|fact| {
                matches!(
                    &fact.subtractability,
                    Subtractability::Set(path, args)
                        if path == &vec![effect_name.to_string()] && args.is_empty()
                )
            })
            .expect("receiver effect should record self-subtract");

        assert_pos_non_subtract(&output.session, ret_eff, fact.id);
        assert_pos_non_subtract(&output.session, ret, fact.id);
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

    fn assert_pos_non_subtract(session: &AnalysisSession, pos: PosId, subtract: SubtractId) {
        match session.infer.constraints().types().pos(pos) {
            Pos::NonSubtract(_, found) if *found == subtract => {}
            other => panic!("expected non-subtract #{:?}, got {other:?}", subtract),
        }
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
    fn type_with_ref_method_keeps_ampersand_receiver_name_and_resolves_ref_selection() {
        let root = parse(
            "type ref 'e 'a\ntype User with:\n  our &x.id = &x\nmy r: ref 'e User = 1\nmy got = r.id\n",
        );
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
    fn local_arg_application_records_empty_subtract_for_defined_lambda_predicate() {
        let root = parse("my h = \\f -> f 1\n");
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
        let (result_effect, subtract) = match types.pos(ret_eff) {
            Pos::NonSubtract(inner, subtract) => match types.pos(*inner) {
                Pos::Var(effect) => (*effect, *subtract),
                other => panic!("expected wrapped body effect var, got {other:?}"),
            },
            other => panic!("expected non-subtract return effect, got {other:?}"),
        };
        assert!(matches!(
            types.pos(ret),
            Pos::NonSubtract(_, ret_subtract) if *ret_subtract == subtract
        ));

        let result_bounds = session
            .infer
            .constraints()
            .bounds()
            .of(result_effect)
            .expect("application result effect should receive flow lower bounds");
        let call_effect = result_bounds
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Var(effect)
                    if session
                        .infer
                        .constraints()
                        .subtracts()
                        .facts(*effect)
                        .iter()
                        .any(|fact| {
                            fact.id == subtract && fact.subtractability == Subtractability::Empty
                        }) =>
                {
                    Some(*effect)
                }
                _ => None,
            })
            .expect("call effect should carry Empty-subtract fact");

        assert_eq!(
            session
                .infer
                .constraints()
                .subtracts()
                .facts(call_effect)
                .len(),
            1
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
    fn lambda_param_effect_annotation_adds_subtract_fact_and_wraps_output() {
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

        assert_eq!(
            session
                .infer
                .constraints()
                .subtracts()
                .facts(param_effect)
                .len(),
            1
        );
        assert!(matches!(types.pos(ret_eff), Pos::NonSubtract(_, _)));
        assert!(matches!(types.pos(ret), Pos::NonSubtract(_, _)));
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
        let [(pat, body)] = arms.as_slice() else {
            panic!("expected one case arm");
        };
        let param = match session.poly.pat(*pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected arm pattern local"),
        };
        let body_ref = expr_ref(&session, *body);

        assert_eq!(session.poly.ref_target(body_ref), Some(param));
        assert!(computation.is_expansive());
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
        let [(pat, body)] = arms.as_slice() else {
            panic!("expected one case arm");
        };
        let (reference, payloads) = match output.session.poly.pat(*pat) {
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
        let body_ref = expr_ref(&output.session, *body);

        assert_eq!(output.session.poly.ref_target(reference), Some(constructor));
        assert_eq!(output.session.poly.ref_target(body_ref), Some(payload));
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
        let [(pat, continuation, body)] = arms.as_slice() else {
            panic!("expected one catch arm");
        };
        assert!(continuation.is_none());
        let value = match session.poly.pat(*pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected value arm pattern local"),
        };
        let body_ref = expr_ref(&session, *body);

        assert_eq!(session.poly.ref_target(body_ref), Some(value));
        assert!(computation.is_expansive());
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
        let [(payload, Some(continuation), effect_body), value_arm] = arms.as_slice() else {
            panic!("expected effect arm followed by value arm");
        };
        assert!(value_arm.1.is_none());

        let payload = match output.session.poly.pat(*payload) {
            Pat::Var(def) => *def,
            _ => panic!("expected effect payload local"),
        };
        let continuation = match output.session.poly.pat(*continuation) {
            Pat::Var(def) => *def,
            _ => panic!("expected continuation local"),
        };
        let (callee, arg) = match output.session.poly.expr(*effect_body) {
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
            "act choose:\n  our branch: unit -> bool\n  our reject: unit -> never\nmy run = 1\nmy f = catch run:\n  choose::branch(), k -> 0\n  value -> value\n",
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

    fn assert_neg_bottom(types: &poly::types::TypeArena, row: NegId) {
        match types.neg(row) {
            Neg::Bot => {}
            other => panic!("expected negative bottom, got {other:?}"),
        }
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
