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
use poly::expr::{Def, DefId, Expr, Lit, Pat, PatId, RefId, Vis};
use poly::types::{
    BuiltinType, Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, SubtractId, Subtractability,
    TypeVar,
};
use rustc_hash::FxHashMap;

use crate::analysis::{AnalysisSession, AnalysisWork};
use crate::annotation::{
    AnnBuildError, AnnComputationTarget, AnnConstraintError, AnnConstraintLowerer, AnnSelfAlias,
    AnnType, AnnTypeBuilder, AnnTypeVarId,
};
use crate::compact::{CompactBounds, CompactFun, CompactType, compact_type_var};
use crate::constraints::TypeLevel;
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate,
};
use crate::scc::SccInput;
use crate::typing::Typing;
use crate::uses::{RefUse, SelectionUse};
use crate::{
    ActMethodDecl, LoadedFileCsts, LoadedFilesError, Lower, ModuleChildDecl, ModuleId, ModuleOrder,
    ModuleTable, ModuleTypeDecl, ModuleTypeKind, RoleImplDecl, RoleImplMethodDecl, RoleMethodDecl,
    TypeDeclId, TypeMethodDecl, TypeMethodReceiver, binding_type_expr,
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
    impl_cursors: FxHashMap<ModuleId, usize>,
    role_requirements: FxHashMap<DefId, RoleMethodRequirement>,
    local_method_scope: Option<ModuleId>,
}

impl BodyLowerer {
    fn new(lower: Lower) -> Self {
        let labels = lower.modules.dump_labels();
        let mut session = AnalysisSession::new(lower.arena);
        register_declared_type_methods(&mut session, &lower.modules);
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
            role_requirements: FxHashMap::default(),
            local_method_scope: None,
        };
        lowerer.collect_declared_role_requirements();
        lowerer
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
                | SyntaxKind::ErrorDecl => self.lower_type_decl(&child, module),
                SyntaxKind::RoleDecl => self.lower_role_decl_body(&child, module),
                SyntaxKind::ActDecl => self.lower_act_decl_body(&child, module),
                SyntaxKind::ImplDecl => self.lower_role_impl_decl(&child, module),
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
        let arg_patterns = binding_arg_patterns(node);
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
        .lower_binding_body_with_args(
            arg_patterns.as_slice(),
            &expr,
            result_type_expr.as_ref(),
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
                        root,
                        computation,
                    )
                };
                match connected {
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
                _ => {}
            }
        }
        self.local_method_scope = previous_scope;
    }

    fn lower_type_constructors(&mut self, node: &Cst, module: ModuleId, decl: &ModuleTypeDecl) {
        match decl.kind {
            ModuleTypeKind::Struct => {
                let payload = ConstructorPayload::from_struct(node);
                self.lower_constructor_def(node, module, decl, decl.name.clone(), payload);
            }
            ModuleTypeKind::Enum | ModuleTypeKind::Error => {
                for variant in crate::enum_variant_nodes(node) {
                    let Some(name) = crate::enum_variant_name(&variant) else {
                        continue;
                    };
                    let payload = ConstructorPayload::from_enum_variant(&variant);
                    self.lower_constructor_def(node, module, decl, name, payload);
                }
            }
            ModuleTypeKind::TypeAlias | ModuleTypeKind::Role | ModuleTypeKind::Act => {}
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
        let mut ann_builder = AnnTypeBuilder::with_self_alias(
            &self.modules,
            module,
            owner.order,
            AnnSelfAlias {
                owner: owner.id,
                type_vars: type_vars.clone(),
            },
        );
        let mut ann_solver_vars = FxHashMap::default();
        for (name, solver_var) in type_vars.iter().zip(owner_arg_vars.iter().copied()) {
            let ann_var = ann_builder.ann_type_var_for_role(name);
            ann_solver_vars.insert(ann_var.id, solver_var);
        }

        let payload = build_constructor_payload_annotations(payload, &mut ann_builder)?;
        drop(ann_builder);

        let owner_args = owner_arg_vars
            .into_iter()
            .map(|var| self.invariant_var_arg(var))
            .collect::<Vec<_>>();
        let args = self.prepare_constructor_args(payload);
        let vars = std::mem::take(&mut ann_solver_vars);
        let mut ann_lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, &self.modules, vars);
        connect_constructor_arg_annotations(&mut ann_lowerer, &args)?;
        let _ = ann_lowerer.into_vars();

        self.constrain_constructor_arg_shapes(&args);
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

    fn prepare_constructor_args(
        &mut self,
        payload: AnnotatedConstructorPayload,
    ) -> Vec<ConstructorArg> {
        match payload {
            AnnotatedConstructorPayload::Unit => Vec::new(),
            AnnotatedConstructorPayload::Tuple(items) => items
                .into_iter()
                .map(|item| self.prepare_constructor_value_arg(item))
                .collect(),
            AnnotatedConstructorPayload::Record(fields) => {
                let record = self.session.infer.fresh_type_var();
                let fields = fields
                    .into_iter()
                    .map(|field| {
                        let value = self.session.infer.fresh_type_var();
                        ConstructorRecordField {
                            name: field.name.0,
                            value,
                            ann: field.ann,
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

    fn prepare_constructor_value_arg(
        &mut self,
        item: AnnotatedConstructorPayloadItem,
    ) -> ConstructorArg {
        let value = self.session.infer.fresh_type_var();
        ConstructorArg::Value {
            value,
            ann: item.ann,
        }
    }

    fn constrain_constructor_arg_shapes(&mut self, args: &[ConstructorArg]) {
        for arg in args {
            let ConstructorArg::Record { value, fields } = arg else {
                continue;
            };
            let lower_fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: self.session.infer.alloc_pos(Pos::Var(field.value)),
                    optional: false,
                })
                .collect();
            let upper_fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: self.session.infer.alloc_neg(Neg::Var(field.value)),
                    optional: false,
                })
                .collect();
            let lower = self.session.infer.alloc_pos(Pos::Record(lower_fields));
            let upper = self.session.infer.alloc_neg(Neg::Record(upper_fields));
            let value_upper = self.session.infer.alloc_neg(Neg::Var(*value));
            let value_lower = self.session.infer.alloc_pos(Pos::Var(*value));
            self.session.infer.subtype(lower, value_upper);
            self.session.infer.subtype(value_lower, upper);
        }
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
        self.session.infer.alloc_neu(Neu::Bounds(lower, var, upper))
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
        let previous_scope = self.local_method_scope.replace(companion);
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
        self.local_method_scope = previous_scope;
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
                Err(_) => return,
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
        let associated_anns = role_associated_names
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    AnnType::Var(ann_builder.ann_type_var_for_role(name)),
                )
            })
            .collect::<Vec<_>>();
        let mut ann_solver_vars = FxHashMap::default();
        let vars = std::mem::take(&mut ann_solver_vars);
        let mut lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, &self.modules, vars);
        let mut inputs = Vec::with_capacity(spec.inputs.len());
        for input in &spec.inputs {
            inputs.push(
                lowerer
                    .lower_role_arg(input)
                    .map_err(|error| LoweringError::AnnotationConstraint { error })?,
            );
        }
        let mut associated = Vec::with_capacity(associated_anns.len());
        for (name, ann) in &associated_anns {
            associated.push(RoleAssociatedConstraint {
                name: name.clone(),
                value: lowerer
                    .lower_role_arg(ann)
                    .map_err(|error| LoweringError::AnnotationConstraint { error })?,
            });
        }
        ann_solver_vars = lowerer.into_vars();
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
            inputs,
            associated,
            prerequisites: Vec::new(),
        });
        Ok(RoleImplLoweringContext {
            role: spec.role,
            target_ann: spec.target,
            input_names: role_input_names,
            input_signatures: spec.inputs.iter().map(signature_from_ann_type).collect(),
            associated_signatures: associated_anns
                .iter()
                .map(|(name, ann)| (name.clone(), signature_from_ann_type(ann)))
                .collect(),
            type_var_bindings: ann_builder.type_var_bindings(),
            ann_solver_vars,
        })
    }

    fn role_impl_method_requirement(
        &self,
        context: &RoleImplLoweringContext,
        name: Name,
    ) -> Option<SignatureType> {
        let method = self
            .modules
            .role_methods(context.role)
            .iter()
            .find(|method| method.name == name)?;
        let requirement = self.role_requirements.get(&method.def)?;
        Some(substitute_role_requirement_signature(requirement, context))
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
        requirement: Option<SignatureType>,
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
            method.receiver.clone(),
            target_ann,
            binding_type_expr(node),
            type_var_bindings,
            ann_solver_vars,
            requirement.as_ref(),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation)
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
            method.receiver.clone(),
            role_path,
            role_inputs,
            role_associated,
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
        .with_local_method_scope(self.local_method_scope)
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
        .with_local_method_scope(self.local_method_scope)
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

    fn next_role_impl_decl(&mut self, module: ModuleId) -> Option<RoleImplDecl> {
        let cursor = self.impl_cursors.entry(module).or_default();
        let decl = self.modules.role_impls(module).get(*cursor).cloned();
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

fn signature_from_ann_type(ann: &AnnType) -> SignatureType {
    match ann {
        AnnType::Builtin(builtin) => SignatureType::Builtin(*builtin),
        AnnType::Named(id) => SignatureType::Named(*id),
        AnnType::Var(var) => SignatureType::Var(SignatureVar {
            name: var.name.clone(),
        }),
        AnnType::EffectRow(row) => SignatureType::EffectRow(signature_effect_row_from_ann(row)),
        AnnType::Effectful { eff, ret } => SignatureType::Effectful {
            eff: signature_effect_row_from_ann(eff),
            ret: Box::new(signature_from_ann_type(ret)),
        },
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
    local_method_scope: Option<ModuleId>,
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
            local_method_scope: None,
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
            local_method_scope: None,
            locals: Vec::new(),
            function_frames: Vec::new(),
        }
    }

    pub fn with_self_alias(mut self, self_alias: Option<AnnSelfAlias>) -> Self {
        self.self_alias = self_alias;
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
        if arg_patterns.is_empty() {
            return self.lower_binding_body_expr(body);
        }
        let mut ann_builder = ann_type_builder(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
        );
        let mut ann_solver_vars = FxHashMap::default();
        self.lower_lambda_params(
            arg_patterns,
            body,
            LambdaScope::Defined,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr,
        )
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

    fn lower_role_method_body_expr(
        &mut self,
        node: &Cst,
        receiver: Option<Name>,
        role_path: Vec<String>,
        role_inputs: &[String],
        role_associated: &[String],
        result_type_expr: Option<Cst>,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
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
            let body = self.lower_expr_with_lambda_scope(node, LambdaScope::Defined)?;
            if let Some(type_expr) = result_type_expr {
                self.connect_type_method_result_annotation(
                    body,
                    &type_expr,
                    &mut ann_builder,
                    &mut ann_solver_vars,
                )?;
            }
            return Ok(body);
        };

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
            .expect("role method predicate frame should be balanced");
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

    fn lower_impl_method_body_expr(
        &mut self,
        node: &Cst,
        receiver: Option<Name>,
        receiver_ann: &AnnType,
        result_type_expr: Option<Cst>,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        requirement: Option<&SignatureType>,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
        );
        ann_builder.seed_type_var_bindings(type_var_bindings);

        let Some(receiver) = receiver else {
            let body = self.lower_expr_with_lambda_scope(node, LambdaScope::Defined)?;
            if let Some(type_expr) = result_type_expr {
                self.connect_type_method_result_annotation(
                    body,
                    &type_expr,
                    &mut ann_builder,
                    ann_solver_vars,
                )?;
            }
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
            .expect("impl method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        if let Some(type_expr) = result_type_expr {
            self.connect_type_method_result_annotation(
                body,
                &type_expr,
                &mut ann_builder,
                ann_solver_vars,
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

    fn connect_impl_method_requirement(
        &mut self,
        value: TypeVar,
        requirement: &SignatureType,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        self.check_impl_method_requirement_shape(value, requirement)?;
        self.check_impl_method_requirement_concrete_type(value, requirement)?;
        let seed = signature_vars_from_ann_vars(type_var_bindings, ann_solver_vars);
        let upper = {
            let mut lowerer = SignatureLowerer::with_vars_at_level(
                &mut self.session.infer,
                self.modules,
                seed,
                TypeLevel::root(),
            );
            lowerer
                .lower_neg(requirement)
                .map_err(|error| LoweringError::SignatureConstraint { error })?
        };
        let lower = self.session.infer.alloc_pos(Pos::Var(value));
        self.session.infer.subtype(lower, upper);
        Ok(())
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
            None,
        )
    }

    fn lower_lambda_params(
        &mut self,
        patterns: &[Cst],
        body: &Cst,
        lambda_scope: LambdaScope,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        body_type_expr: Option<&Cst>,
    ) -> Result<Computation, LoweringError> {
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
        let pat = self.lower_lambda_pattern(pattern, param_value, annotation.call_return_effect)?;
        self.function_frames
            .push(FunctionPredicateFrame::new(lambda_scope));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_lambda_params(
            rest,
            body,
            lambda_scope,
            ann_builder,
            ann_solver_vars,
            body_type_expr,
        );
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
                local_method_scope: self.local_method_scope,
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

enum ConstructorPayload {
    Unit,
    Tuple(Vec<ConstructorPayloadItem>),
    Record(Vec<ConstructorRecordPayloadField>),
}

impl ConstructorPayload {
    fn from_struct(node: &Cst) -> Self {
        let fields = crate::struct_field_nodes(node);
        payload_from_fields(fields)
    }

    fn from_enum_variant(node: &Cst) -> Self {
        let fields = crate::enum_variant_field_nodes(node);
        if !fields.is_empty() {
            return payload_from_fields(fields);
        }
        let items = crate::enum_variant_direct_type_exprs(node)
            .into_iter()
            .map(|ty| ConstructorPayloadItem { ty: Some(ty) })
            .collect::<Vec<_>>();
        if items.is_empty() {
            Self::Unit
        } else {
            Self::Tuple(items)
        }
    }
}

struct ConstructorPayloadItem {
    ty: Option<Cst>,
}

struct ConstructorRecordPayloadField {
    name: Name,
    ty: Option<Cst>,
}

enum AnnotatedConstructorPayload {
    Unit,
    Tuple(Vec<AnnotatedConstructorPayloadItem>),
    Record(Vec<AnnotatedConstructorRecordPayloadField>),
}

struct AnnotatedConstructorPayloadItem {
    ann: Option<AnnType>,
}

struct AnnotatedConstructorRecordPayloadField {
    name: Name,
    ann: Option<AnnType>,
}

enum ConstructorArg {
    Value {
        value: TypeVar,
        ann: Option<AnnType>,
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
    ann: Option<AnnType>,
}

fn build_constructor_payload_annotations(
    payload: ConstructorPayload,
    ann_builder: &mut AnnTypeBuilder,
) -> Result<AnnotatedConstructorPayload, LoweringError> {
    match payload {
        ConstructorPayload::Unit => Ok(AnnotatedConstructorPayload::Unit),
        ConstructorPayload::Tuple(items) => items
            .into_iter()
            .map(|item| {
                let ann = item
                    .ty
                    .map(|ty| ann_builder.build_type_expr(&ty))
                    .transpose()
                    .map_err(|error| LoweringError::AnnotationBuild { error })?;
                Ok(AnnotatedConstructorPayloadItem { ann })
            })
            .collect::<Result<Vec<_>, LoweringError>>()
            .map(AnnotatedConstructorPayload::Tuple),
        ConstructorPayload::Record(fields) => fields
            .into_iter()
            .map(|field| {
                let ann = field
                    .ty
                    .map(|ty| ann_builder.build_type_expr(&ty))
                    .transpose()
                    .map_err(|error| LoweringError::AnnotationBuild { error })?;
                Ok(AnnotatedConstructorRecordPayloadField {
                    name: field.name,
                    ann,
                })
            })
            .collect::<Result<Vec<_>, LoweringError>>()
            .map(AnnotatedConstructorPayload::Record),
    }
}

fn payload_from_fields(fields: Vec<Cst>) -> ConstructorPayload {
    if fields.is_empty() {
        return ConstructorPayload::Unit;
    }

    let mut record = Vec::new();
    let mut tuple = Vec::new();
    for field in fields {
        if let Some(name) = crate::struct_field_name(&field) {
            record.push(ConstructorRecordPayloadField {
                name,
                ty: crate::field_type_expr(&field),
            });
        } else {
            tuple.push(ConstructorPayloadItem {
                ty: crate::field_type_expr(&field),
            });
        }
    }

    if !record.is_empty() {
        ConstructorPayload::Record(record)
    } else {
        ConstructorPayload::Tuple(tuple)
    }
}

fn connect_constructor_arg_annotations(
    lowerer: &mut AnnConstraintLowerer,
    args: &[ConstructorArg],
) -> Result<(), LoweringError> {
    for arg in args {
        match arg {
            ConstructorArg::Value {
                value,
                ann: Some(ann),
            } => {
                lowerer
                    .connect_value(*value, ann)
                    .map_err(|error| LoweringError::AnnotationConstraint { error })?;
            }
            ConstructorArg::Value { ann: None, .. } => {}
            ConstructorArg::Record { fields, .. } => {
                for field in fields {
                    if let Some(ann) = &field.ann {
                        lowerer
                            .connect_value(field.value, ann)
                            .map_err(|error| LoweringError::AnnotationConstraint { error })?;
                    }
                }
            }
        }
    }
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
    SignatureConstraint { error: SignatureConstraintError },
    SignatureShapeMismatch { expected: SignatureShape },
    SignatureTypeMismatch { expected: SignatureShape },
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

fn collect_binding_arg_patterns(node: &Cst, out: &mut Vec<Cst>) {
    for child in node.children() {
        if !matches!(child.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC) {
            continue;
        }
        collect_binding_arg_patterns(&child, out);
        out.extend(
            child
                .children()
                .filter(|item| item.kind() == SyntaxKind::Pattern),
        );
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureEffectRow {
    items: Vec<SignatureEffectAtom>,
    tail: Option<SignatureVar>,
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
}

impl SignatureShape {
    fn of(signature: &SignatureType) -> Self {
        match signature {
            SignatureType::Builtin(_) | SignatureType::Named(_) | SignatureType::Apply { .. } => {
                Self::Constructor
            }
            SignatureType::EffectRow(_) => Self::EffectRow,
            SignatureType::Effectful { ret, .. } => Self::of(ret),
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
        && actual.cons.iter().all(|con| {
            con.path == expected.path
                && con.args.len() == expected.args.len()
                && con
                    .args
                    .iter()
                    .zip(&expected.args)
                    .all(|(actual, expected)| {
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
        SignatureType::EffectRow(_) | SignatureType::Function { .. } => None,
    }
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
            SignatureType::Builtin(builtin) => {
                let path = vec![builtin.surface_name().to_string()];
                Ok(self.alloc_pos(Pos::Con(path, Vec::new())))
            }
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
            SignatureType::Builtin(builtin) => {
                let path = vec![builtin.surface_name().to_string()];
                Ok(self.alloc_neg(Neg::Con(path, Vec::new())))
            }
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

    fn lower_effect_row_pos(
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
            items.push(self.lower_pos(ty)?);
        }
        if let Some(tail) = &row.tail {
            let tail = self.signature_var(tail);
            items.push(self.alloc_pos(Pos::Var(tail)));
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
        self.record_effect_row_subtractability(effect, row)?;
        Ok(self.alloc_neg(Neg::Var(effect)))
    }

    fn connect_effect_tail_lower(&mut self, effect: TypeVar, row: &SignatureEffectRow) {
        if let Some(tail) = &row.tail {
            let tail = self.signature_var(tail);
            let tail = self.alloc_pos(Pos::Var(tail));
            let effect = self.alloc_neg(Neg::Var(effect));
            self.infer.subtype(tail, effect);
        }
    }

    fn record_effect_row_subtractability(
        &mut self,
        effect: TypeVar,
        row: &SignatureEffectRow,
    ) -> Result<(), SignatureConstraintError> {
        if row
            .items
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
        {
            let id = self.infer.fresh_subtract_id();
            self.infer.subtract_fact(effect, id, Subtractability::All);
            return Ok(());
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
                self.infer.subtract_fact(effect, id, Subtractability::Empty);
            }
            return Ok(());
        }

        for (path, args) in atoms {
            let id = self.infer.fresh_subtract_id();
            self.infer
                .subtract_fact(effect, id, Subtractability::Set(path, args));
        }
        Ok(())
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
        let var = match signature {
            SignatureType::Var(var) => self.signature_var(var),
            _ => self.fresh_type_var(),
        };
        Ok(self.alloc_neu(Neu::Bounds(lower, var, upper)))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower_module_map;
    use crate::scc::SccEvent;
    use poly::expr::{DefId, ExprId, Pat, RefId, SelectResolution, Vis};

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

    fn def_scheme(output: &BodyLowering, def: DefId) -> &poly::types::Scheme {
        match output.session.poly.defs.get(def) {
            Some(Def::Let {
                scheme: Some(scheme),
                ..
            }) => scheme,
            _ => panic!("expected def scheme"),
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
    fn enum_variant_constructor_lowers_to_scheme() {
        let root = parse("enum opt 'a = none | some 'a\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let none = lower.modules.value_decls(module, &Name("none".into()))[0].def;
        let some = lower.modules.value_decls(module, &Name("some".into()))[0].def;

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
        let root = parse("enum opt 'a = some 'a\nmy x = some 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let constructor = lower.modules.value_decls(module, &Name("some".into()))[0].def;
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
    fn role_impl_method_requirement_ret_effect_records_subtractable_effect() {
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
        assert!(bounds.uppers().iter().any(|bound| {
            let Neg::Var(requirement_effect) = types.neg(bound.neg) else {
                return false;
            };
            output
                .session
                .infer
                .constraints()
                .subtracts()
                .facts(*requirement_effect)
                .iter()
                .any(|fact| match &fact.subtractability {
                    Subtractability::Set(path, args) => {
                        path == &vec!["nondet".to_string()] && args.is_empty()
                    }
                    _ => false,
                })
        }));
    }

    #[test]
    fn role_method_signature_arg_effect_does_not_lower_to_plain_neg_row() {
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
        let arg_effect = match output.session.infer.constraints().types().neg(arg_eff) {
            Neg::Var(var) => *var,
            other => panic!("expected subtractable arg effect var, got {other:?}"),
        };
        assert!(
            output
                .session
                .infer
                .constraints()
                .subtracts()
                .facts(arg_effect)
                .iter()
                .any(|fact| matches!(
                    &fact.subtractability,
                    Subtractability::Set(path, args)
                        if path == &vec!["nondet".to_string()] && args.is_empty()
                ))
        );
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
