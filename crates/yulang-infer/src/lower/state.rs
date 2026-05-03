use std::collections::{HashMap, HashSet};

use crate::ast::expr::{ExprKind, TypedExpr};
use crate::diagnostic::{
    ConstraintCause, ExpectedEdge, ExpectedEdgeId, ExpectedEdgeKind, TypeOrigin,
};
use crate::ids::{DefId, NegId, PosId, RefId, TypeVar, fresh_def_id, fresh_ref_id, fresh_type_var};
use crate::lower::ctx::LowerCtx;
use crate::solve::Infer;
use crate::symbols::{ModuleId, Name, Path, Visibility};
use crate::types::{Neg, Pos};

use super::{
    ActiveRecursiveSelfInstance, EnumVariantPatternShape, FunctionSigEffectHint,
    LowerDetailProfile, SyntaxNode,
};

/// lowering ワンパスで持ち回す全状態。
pub struct LowerState {
    pub ctx: LowerCtx,
    pub infer: Infer,
    pub lower_detail: LowerDetailProfile,
    /// let 多相のレベル（enter_let / leave_let で管理）
    pub current_level: u32,
    /// DefId → その束縛の TypeVar（宣言時に確保したもの）
    pub def_tvs: HashMap<DefId, TypeVar>,
    /// `my`/`our` binding が導入した DefId。lambda 引数などの monomorphic local と区別する。
    pub let_bound_defs: HashSet<DefId>,
    /// catch arm が導入した continuation DefId。
    pub continuation_defs: HashSet<DefId>,
    /// lexical parameter / pattern DefId → それを導入した binding owner。
    pub def_owners: HashMap<DefId, DefId>,
    /// local DefId の人間向け名前。
    pub def_names: HashMap<DefId, crate::symbols::Name>,
    /// lambda parameter def ごとの pattern local binder 群。
    pub lambda_local_defs: HashMap<DefId, Vec<DefId>>,
    /// lambda parameter def ごとの header pattern。
    pub lambda_param_pats: HashMap<DefId, crate::ast::expr::TypedPat>,
    /// lambda parameter def ごとの effect annotation 種別。
    pub lambda_param_effect_annotations: HashMap<DefId, yulang_core_ir::ParamEffectAnnotation>,
    /// 関数シグネチャ注釈を持つ lambda/header parameter の latent effect 挙動。
    pub lambda_param_function_sig_hints: HashMap<DefId, FunctionSigEffectHint>,
    /// 関数シグネチャ注釈が許可する effect allow-list。
    pub lambda_param_function_allowed_effects:
        HashMap<DefId, yulang_core_ir::FunctionSigAllowedEffects>,
    /// top-level / observable binding の desugar 済み body。
    pub principal_bodies: HashMap<DefId, TypedExpr>,
    /// lowering 中の self recursive binding が self-call で使う provisional scheme。
    pub provisional_self_schemes: HashMap<DefId, crate::FrozenScheme>,
    /// lowering 中の self recursive binding が body 内で共有する monomorphic root tv。
    pub provisional_self_root_tvs: HashMap<DefId, TypeVar>,
    /// lowering 中の binding body で共有する monomorphic self instance。
    pub active_recursive_self_instances: HashMap<DefId, ActiveRecursiveSelfInstance>,
    /// binding body で実際に self-call が起きた owner。
    pub recursive_self_uses: HashSet<DefId>,
    /// lowering 後にも recursive binding だったことを残す集合。
    pub recursive_binding_defs: HashSet<DefId>,
    /// runtime export 用に固定した concrete scheme。
    pub runtime_export_schemes: HashMap<DefId, yulang_core_ir::Scheme>,
    /// ファイル単位 root block。principal root export 用。
    pub top_level_blocks: Vec<(Path, crate::ast::expr::TypedBlock)>,
    /// top-level 式のために作った synthetic owner。
    pub top_level_expr_owners: Vec<DefId>,
    /// 型制約を張ったときの「実際の型が文脈型として使われる」軽い記録。
    /// runtime IR には影響させず、diagnostic / hover / 将来の elaboration evidence に使う。
    pub expected_edges: Vec<ExpectedEdge>,
    next_expected_edge_id: u32,
    /// 現在見えている型変数スコープ。
    pub type_var_scopes: Vec<HashMap<String, TypeVar>>,
    /// DefId → 参照時に露出する latent effect slot。
    /// annotation 付き引数のように、変数参照が effect を運ぶ場合にだけ設定する。
    pub def_eff_tvs: HashMap<DefId, TypeVar>,
    /// `$x` 用の local ref DefId → 対応する synthetic act 名。
    pub var_ref_acts: HashMap<DefId, crate::symbols::Name>,
    /// 現在 lowering 中の束縛 owner。
    pub current_owner: Option<DefId>,
    /// effect path ごとの act type 引数個数。
    pub effect_arities: HashMap<Path, usize>,
    /// effect path ごとの act type 引数。
    pub effect_args: HashMap<Path, Vec<(TypeVar, TypeVar)>>,
    /// operation DefId ごとの effect atom 引数。
    pub effect_op_args: HashMap<DefId, Vec<(TypeVar, TypeVar)>>,
    /// operation DefId が属する effect path。
    pub effect_op_effect_paths: HashMap<DefId, Path>,
    /// operation DefId ごとの明示シグネチャ。
    pub effect_op_pos_sigs: HashMap<DefId, PosId>,
    pub effect_op_neg_sigs: HashMap<DefId, NegId>,
    /// act copy のために、effect path ごとの宣言 CST を保持する。
    pub act_templates: HashMap<Path, SyntaxNode>,
    /// 現在 lowering 中の act body。`.` binding を effect method として登録するために使う。
    pub current_act_effect_path: Option<Path>,
    /// 現在の block suffix を `do` が参照するときの置換式。
    pub do_replacement: Option<TypedExpr>,
    /// type/companion method/role method の探索環境を rebuild すべきか。
    pub selection_lookup_dirty: bool,
    /// 型名と同名の companion module。
    pub companion_modules: HashSet<ModuleId>,
    /// enum variant constructor DefId → variant tag。
    pub enum_variant_tags: HashMap<DefId, Name>,
    /// enum variant constructor DefId → pattern 用の nominal shape。
    pub enum_variant_patterns: HashMap<DefId, EnumVariantPatternShape>,
    /// 後解決された RefId のうち、frozen scheme の参照インスタンス化まで済ませたもの。
    instantiated_resolved_refs: HashSet<RefId>,
    force_local_bindings_depth: u32,
    suppress_top_level_expr_owners_depth: u32,
    synthetic_with_module_counter: u32,
}

impl LowerState {
    pub fn new() -> Self {
        Self {
            ctx: LowerCtx::new(),
            infer: Infer::new(),
            lower_detail: LowerDetailProfile::default(),
            current_level: 0,
            def_tvs: HashMap::new(),
            let_bound_defs: HashSet::new(),
            continuation_defs: HashSet::new(),
            def_owners: HashMap::new(),
            def_names: HashMap::new(),
            lambda_local_defs: HashMap::new(),
            lambda_param_pats: HashMap::new(),
            lambda_param_effect_annotations: HashMap::new(),
            lambda_param_function_sig_hints: HashMap::new(),
            lambda_param_function_allowed_effects: HashMap::new(),
            principal_bodies: HashMap::new(),
            provisional_self_schemes: HashMap::new(),
            provisional_self_root_tvs: HashMap::new(),
            active_recursive_self_instances: HashMap::new(),
            recursive_self_uses: HashSet::new(),
            recursive_binding_defs: HashSet::new(),
            runtime_export_schemes: HashMap::new(),
            top_level_blocks: Vec::new(),
            top_level_expr_owners: Vec::new(),
            expected_edges: Vec::new(),
            next_expected_edge_id: 0,
            type_var_scopes: Vec::new(),
            def_eff_tvs: HashMap::new(),
            var_ref_acts: HashMap::new(),
            current_owner: None,
            effect_arities: HashMap::new(),
            effect_args: HashMap::new(),
            effect_op_args: HashMap::new(),
            effect_op_effect_paths: HashMap::new(),
            effect_op_pos_sigs: HashMap::new(),
            effect_op_neg_sigs: HashMap::new(),
            act_templates: HashMap::new(),
            current_act_effect_path: None,
            do_replacement: None,
            selection_lookup_dirty: true,
            companion_modules: HashSet::new(),
            enum_variant_tags: HashMap::new(),
            enum_variant_patterns: HashMap::new(),
            instantiated_resolved_refs: HashSet::new(),
            force_local_bindings_depth: 0,
            suppress_top_level_expr_owners_depth: 0,
            synthetic_with_module_counter: 0,
        }
    }

    /// let binding の body に入るとき。
    pub fn enter_let(&mut self) {
        self.current_level += 1;
    }

    /// let binding の body から出るとき。
    pub fn leave_let(&mut self) {
        self.current_level = self.current_level.saturating_sub(1);
    }

    /// 現在のレベルで fresh な TypeVar を発行する。
    pub fn fresh_tv(&self) -> TypeVar {
        self.fresh_tv_at(self.current_level)
    }

    pub fn fresh_tv_at(&self, level: u32) -> TypeVar {
        let tv = fresh_type_var();
        self.infer.register_level(tv, level);
        tv
    }

    pub fn fresh_tv_with_origin(&self, origin: TypeOrigin) -> TypeVar {
        self.fresh_tv_at_origin(self.current_level, origin)
    }

    pub fn fresh_tv_at_origin(&self, level: u32, origin: TypeOrigin) -> TypeVar {
        let tv = self.fresh_tv_at(level);
        self.infer.register_origin(tv, origin);
        tv
    }

    pub fn record_expected_edge(
        &mut self,
        actual_tv: TypeVar,
        expected_tv: TypeVar,
        kind: ExpectedEdgeKind,
        cause: ConstraintCause,
    ) -> ExpectedEdgeId {
        let id = self.fresh_expected_edge_id();
        self.expected_edges.push(ExpectedEdge {
            id,
            actual_tv,
            expected_tv,
            actual_eff: None,
            expected_eff: None,
            kind,
            cause,
        });
        id
    }

    pub fn record_expected_edge_with_effects(
        &mut self,
        actual_tv: TypeVar,
        expected_tv: TypeVar,
        actual_eff: Option<TypeVar>,
        expected_eff: Option<TypeVar>,
        kind: ExpectedEdgeKind,
        cause: ConstraintCause,
    ) -> ExpectedEdgeId {
        let id = self.fresh_expected_edge_id();
        self.expected_edges.push(ExpectedEdge {
            id,
            actual_tv,
            expected_tv,
            actual_eff,
            expected_eff,
            kind,
            cause,
        });
        id
    }

    fn fresh_expected_edge_id(&mut self) -> ExpectedEdgeId {
        let id = ExpectedEdgeId(self.next_expected_edge_id);
        self.next_expected_edge_id += 1;
        id
    }

    pub fn expect_value(
        &mut self,
        actual_tv: TypeVar,
        expected_tv: TypeVar,
        kind: ExpectedEdgeKind,
        cause: ConstraintCause,
    ) -> ExpectedEdgeId {
        let edge_id = self.record_expected_edge(actual_tv, expected_tv, kind, cause.clone());
        self.infer
            .constrain_with_cause(Pos::Var(actual_tv), Neg::Var(expected_tv), cause);
        edge_id
    }

    pub fn expect_value_and_effect(
        &mut self,
        actual_tv: TypeVar,
        expected_tv: TypeVar,
        actual_eff: TypeVar,
        expected_eff: TypeVar,
        kind: ExpectedEdgeKind,
        cause: ConstraintCause,
    ) {
        self.record_expected_edge_with_effects(
            actual_tv,
            expected_tv,
            Some(actual_eff),
            Some(expected_eff),
            kind,
            cause.clone(),
        );
        self.infer
            .constrain_with_cause(Pos::Var(actual_tv), Neg::Var(expected_tv), cause);
        self.infer
            .constrain(Pos::Var(actual_eff), Neg::Var(expected_eff));
    }

    pub fn representation_coerce(
        &mut self,
        actual_tv: TypeVar,
        expected_tv: TypeVar,
        eff: TypeVar,
        expr: TypedExpr,
    ) -> TypedExpr {
        let actual_eff = expr.eff;
        let edge_id = self.record_expected_edge_with_effects(
            actual_tv,
            expected_tv,
            Some(actual_eff),
            Some(eff),
            ExpectedEdgeKind::RepresentationCoerce,
            ConstraintCause {
                span: None,
                reason: crate::diagnostic::ConstraintReason::RepresentationCoerce,
            },
        );
        self.infer.constrain(Pos::Var(actual_eff), Neg::Var(eff));
        TypedExpr {
            tv: expected_tv,
            eff,
            kind: ExprKind::Coerce {
                edge_id: Some(edge_id),
                actual_tv,
                expected_tv,
                expr: Box::new(expr),
            },
        }
    }

    /// fresh な DefId を発行し、SCC に登録する。
    pub fn fresh_def(&mut self) -> DefId {
        let def = fresh_def_id();
        self.infer.register_def(def);
        def
    }

    pub fn fresh_synthetic_with_module_name(&mut self) -> Name {
        let id = self.synthetic_with_module_counter;
        self.synthetic_with_module_counter += 1;
        Name(format!("#with{id}"))
    }

    /// fresh な RefId を発行する。
    pub fn fresh_ref(&self) -> RefId {
        fresh_ref_id()
    }

    pub fn register_def_tv(&mut self, def: DefId, tv: TypeVar) {
        self.def_tvs.insert(def, tv);
        self.infer.register_def_tv(def, tv);
    }

    pub fn mark_let_bound_def(&mut self, def: DefId) {
        self.let_bound_defs.insert(def);
    }

    pub fn is_let_bound_def(&self, def: DefId) -> bool {
        self.let_bound_defs.contains(&def)
    }

    pub fn mark_continuation_def(&mut self, def: DefId) {
        self.continuation_defs.insert(def);
    }

    pub fn is_continuation_def(&self, def: DefId) -> bool {
        self.continuation_defs.contains(&def)
    }

    pub fn register_def_owner(&mut self, def: DefId, owner: DefId) {
        self.def_owners.insert(def, owner);
    }

    pub fn def_owner(&self, def: DefId) -> Option<DefId> {
        self.def_owners.get(&def).copied()
    }

    pub fn activate_recursive_self_instance(
        &mut self,
        def: DefId,
        instance: ActiveRecursiveSelfInstance,
    ) {
        self.active_recursive_self_instances.insert(def, instance);
    }

    pub fn deactivate_recursive_self_instance(&mut self, def: DefId) {
        self.active_recursive_self_instances.remove(&def);
    }

    pub fn active_recursive_self_instance(
        &self,
        def: DefId,
    ) -> Option<ActiveRecursiveSelfInstance> {
        self.active_recursive_self_instances.get(&def).copied()
    }

    pub fn mark_recursive_self_use(&mut self, def: DefId) {
        self.recursive_self_uses.insert(def);
    }

    pub fn take_recursive_self_use(&mut self, def: DefId) -> bool {
        self.recursive_self_uses.remove(&def)
    }

    pub fn mark_recursive_binding(&mut self, def: DefId) {
        self.recursive_binding_defs.insert(def);
    }

    pub fn is_recursive_binding(&self, def: DefId) -> bool {
        self.recursive_binding_defs.contains(&def)
    }

    pub fn register_def_name(&mut self, def: DefId, name: crate::symbols::Name) {
        self.def_names.insert(def, name);
    }

    pub fn def_name(&self, def: DefId) -> Option<&crate::symbols::Name> {
        self.def_names.get(&def)
    }

    pub fn register_lambda_local_defs(&mut self, param_def: DefId, local_defs: Vec<DefId>) {
        self.lambda_local_defs.insert(param_def, local_defs);
    }

    pub fn register_lambda_param_pat(&mut self, param_def: DefId, pat: crate::ast::expr::TypedPat) {
        self.lambda_param_pats.insert(param_def, pat);
    }

    pub fn register_lambda_param_effect_annotation(
        &mut self,
        param_def: DefId,
        annotation: yulang_core_ir::ParamEffectAnnotation,
    ) {
        self.lambda_param_effect_annotations
            .insert(param_def, annotation);
    }

    pub fn register_lambda_param_function_sig(
        &mut self,
        param_def: DefId,
        hint: FunctionSigEffectHint,
    ) {
        self.lambda_param_function_sig_hints.insert(param_def, hint);
    }

    pub fn register_lambda_param_function_allowed_effects(
        &mut self,
        param_def: DefId,
        allowed: yulang_core_ir::FunctionSigAllowedEffects,
    ) {
        self.lambda_param_function_allowed_effects
            .insert(param_def, allowed);
    }

    pub fn lambda_param_function_sig_hint(
        &self,
        param_def: DefId,
    ) -> Option<FunctionSigEffectHint> {
        self.lambda_param_function_sig_hints
            .get(&param_def)
            .copied()
    }

    pub fn record_top_level_block(&mut self, path: Path, block: crate::ast::expr::TypedBlock) {
        self.top_level_blocks.push((path, block));
    }

    pub fn record_top_level_expr_owner(&mut self, owner: DefId) {
        self.top_level_expr_owners.push(owner);
    }

    pub fn register_def_eff_tv(&mut self, def: DefId, eff_tv: TypeVar) {
        self.def_eff_tvs.insert(def, eff_tv);
    }

    pub fn fresh_pure_eff_tv(&mut self) -> TypeVar {
        let tv = self.fresh_tv();
        self.infer
            .constrain(self.infer.arena.empty_pos_row, Neg::Var(tv));
        tv
    }

    pub fn fresh_exact_pure_eff_tv(&mut self) -> TypeVar {
        let tv = self.fresh_tv();
        self.infer
            .constrain(self.infer.arena.empty_pos_row, Neg::Var(tv));
        self.infer
            .constrain(Pos::Var(tv), self.infer.arena.empty_neg_row);
        tv
    }

    pub fn mark_selection_lookup_dirty(&mut self) {
        self.selection_lookup_dirty = true;
    }

    pub fn with_act_effect_path<T>(&mut self, path: Path, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = self.current_act_effect_path.replace(path);
        let result = f(self);
        self.current_act_effect_path = old;
        result
    }

    pub fn pos_row(&self, items: Vec<Pos>, tail: Pos) -> Pos {
        Pos::Row(
            items
                .into_iter()
                .map(|item| self.infer.alloc_pos(item))
                .collect(),
            self.infer.alloc_pos(tail),
        )
    }

    pub fn neg_row(&self, items: Vec<Neg>, tail: Neg) -> Neg {
        Neg::Row(
            items
                .into_iter()
                .map(|item| self.infer.alloc_neg(item))
                .collect(),
            self.infer.alloc_neg(tail),
        )
    }

    pub fn pos_fun(&self, arg: Neg, arg_eff: Neg, ret_eff: Pos, ret: Pos) -> Pos {
        Pos::Fun {
            arg: self.infer.alloc_neg(arg),
            arg_eff: self.infer.alloc_neg(arg_eff),
            ret_eff: self.infer.alloc_pos(ret_eff),
            ret: self.infer.alloc_pos(ret),
        }
    }

    pub fn neg_fun(&self, arg: Pos, arg_eff: Pos, ret_eff: Neg, ret: Neg) -> Neg {
        Neg::Fun {
            arg: self.infer.alloc_pos(arg),
            arg_eff: self.infer.alloc_pos(arg_eff),
            ret_eff: self.infer.alloc_neg(ret_eff),
            ret: self.infer.alloc_neg(ret),
        }
    }

    pub fn pos_tuple(&self, items: Vec<Pos>) -> Pos {
        Pos::Tuple(
            items
                .into_iter()
                .map(|item| self.infer.alloc_pos(item))
                .collect(),
        )
    }

    pub fn pos_record(&self, fields: Vec<crate::types::RecordField<Pos>>) -> Pos {
        Pos::Record(
            fields
                .into_iter()
                .map(|field| crate::types::RecordField {
                    name: field.name,
                    value: self.infer.alloc_pos(field.value),
                    optional: field.optional,
                })
                .collect(),
        )
    }

    pub fn pos_record_tail_spread(
        &self,
        fields: Vec<crate::types::RecordField<Pos>>,
        tail: Pos,
    ) -> Pos {
        Pos::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| crate::types::RecordField {
                    name: field.name,
                    value: self.infer.alloc_pos(field.value),
                    optional: field.optional,
                })
                .collect(),
            tail: self.infer.alloc_pos(tail),
        }
    }

    pub fn pos_record_head_spread(
        &self,
        tail: Pos,
        fields: Vec<crate::types::RecordField<Pos>>,
    ) -> Pos {
        Pos::RecordHeadSpread {
            tail: self.infer.alloc_pos(tail),
            fields: fields
                .into_iter()
                .map(|field| crate::types::RecordField {
                    name: field.name,
                    value: self.infer.alloc_pos(field.value),
                    optional: field.optional,
                })
                .collect(),
        }
    }

    pub fn neg_record(&self, fields: Vec<crate::types::RecordField<Neg>>) -> Neg {
        Neg::Record(
            fields
                .into_iter()
                .map(|field| crate::types::RecordField {
                    name: field.name,
                    value: self.infer.alloc_neg(field.value),
                    optional: field.optional,
                })
                .collect(),
        )
    }

    pub fn pos_variant(&self, items: Vec<(crate::symbols::Name, Vec<Pos>)>) -> Pos {
        Pos::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| self.infer.alloc_pos(payload))
                            .collect(),
                    )
                })
                .collect(),
        )
    }

    pub fn pos_con(&self, path: Path, args: Vec<(Pos, Neg)>) -> Pos {
        Pos::Con(
            path,
            args.into_iter()
                .map(|(pos, neg)| (self.infer.alloc_pos(pos), self.infer.alloc_neg(neg)))
                .collect(),
        )
    }

    pub fn neg_con(&self, path: Path, args: Vec<(Pos, Neg)>) -> Neg {
        Neg::Con(
            path,
            args.into_iter()
                .map(|(pos, neg)| (self.infer.alloc_pos(pos), self.infer.alloc_neg(neg)))
                .collect(),
        )
    }

    pub fn mark_companion_module(&mut self, module: ModuleId) {
        self.companion_modules.insert(module);
        self.mark_selection_lookup_dirty();
    }

    pub fn insert_value(&mut self, module: ModuleId, name: crate::symbols::Name, def: DefId) {
        self.insert_value_with_visibility(module, name, def, Visibility::Pub);
    }

    pub fn insert_value_with_visibility(
        &mut self,
        module: ModuleId,
        name: crate::symbols::Name,
        def: DefId,
        visibility: Visibility,
    ) {
        if !self.ctx.is_operator_def(def) {
            let mut canonical_path = self.ctx.module_path(module).segments;
            canonical_path.push(name.clone());
            self.ctx.record_canonical_value_path(
                def,
                Path {
                    segments: canonical_path,
                },
            );
        }
        self.ctx
            .modules
            .insert_value_with_visibility(module, name, def, visibility);
        if self.companion_modules.contains(&module) {
            self.mark_selection_lookup_dirty();
        }
    }

    pub fn insert_value_alias_with_visibility(
        &mut self,
        module: ModuleId,
        name: crate::symbols::Name,
        def: DefId,
        visibility: Visibility,
    ) {
        let mut alias_path = self.ctx.module_path(module).segments;
        alias_path.push(name.clone());
        let alias_path = Path {
            segments: alias_path,
        };
        if self
            .ctx
            .modules
            .node(module)
            .values
            .get(&name)
            .is_some_and(|existing| self.ctx.is_canonical_value_path(*existing, &alias_path))
        {
            return;
        }
        self.ctx
            .modules
            .insert_value_with_visibility(module, name, def, visibility);
        if self.companion_modules.contains(&module) {
            self.mark_selection_lookup_dirty();
        }
    }

    pub fn insert_type(&mut self, module: ModuleId, name: crate::symbols::Name, def: DefId) {
        self.insert_type_with_visibility(module, name, def, Visibility::Pub);
    }

    pub fn insert_type_with_visibility(
        &mut self,
        module: ModuleId,
        name: crate::symbols::Name,
        def: DefId,
        visibility: Visibility,
    ) {
        let mut canonical_path = self.ctx.module_path(module).segments;
        canonical_path.push(name.clone());
        self.ctx
            .modules
            .insert_type_with_visibility(module, name, def, visibility);
        self.ctx.record_canonical_type_path(
            def,
            Path {
                segments: canonical_path,
            },
        );
        self.mark_selection_lookup_dirty();
    }

    pub fn insert_type_alias_with_visibility(
        &mut self,
        module: ModuleId,
        name: crate::symbols::Name,
        def: DefId,
        visibility: Visibility,
    ) {
        let mut alias_path = self.ctx.module_path(module).segments;
        alias_path.push(name.clone());
        let alias_path = Path {
            segments: alias_path,
        };
        if self
            .ctx
            .modules
            .node(module)
            .types
            .get(&name)
            .is_some_and(|existing| self.ctx.is_canonical_type_path(*existing, &alias_path))
        {
            return;
        }
        self.ctx
            .modules
            .insert_type_with_visibility(module, name, def, visibility);
        self.mark_selection_lookup_dirty();
    }

    pub fn insert_module(&mut self, module: ModuleId, name: crate::symbols::Name, child: ModuleId) {
        self.insert_module_with_visibility(module, name, child, Visibility::Pub);
    }

    pub fn insert_module_with_visibility(
        &mut self,
        module: ModuleId,
        name: crate::symbols::Name,
        child: ModuleId,
        visibility: Visibility,
    ) {
        self.ctx
            .modules
            .insert_module_with_visibility(module, name, child, visibility);
        self.mark_selection_lookup_dirty();
    }

    pub fn insert_module_alias_with_visibility(
        &mut self,
        module: ModuleId,
        name: crate::symbols::Name,
        child: ModuleId,
        visibility: Visibility,
    ) {
        if self
            .ctx
            .modules
            .node(module)
            .modules
            .get(&name)
            .is_some_and(|existing| self.ctx.modules.node(*existing).parent == Some(module))
        {
            return;
        }
        self.ctx
            .modules
            .insert_module_alias_with_visibility(module, name, child, visibility);
        self.mark_selection_lookup_dirty();
    }

    pub fn refresh_selection_environment(&mut self) {
        if self.ctx.refs.has_unresolved() {
            self.ctx.resolve_pending_refs();
        }
        self.instantiate_late_resolved_refs();
        if self.selection_lookup_dirty {
            self.infer.rebuild_type_methods(&self.ctx.modules);
            self.selection_lookup_dirty = false;
        }
        if !self.infer.deferred_selections.borrow().is_empty() {
            self.infer.resolve_deferred_selections();
        }
        if !self.infer.deferred_role_method_calls.borrow().is_empty() {
            self.infer.resolve_deferred_role_method_calls();
        }
    }

    pub fn mark_resolved_ref_instantiated(&mut self, ref_id: RefId) {
        self.instantiated_resolved_refs.insert(ref_id);
    }

    fn instantiate_late_resolved_refs(&mut self) {
        let refs = self
            .ctx
            .refs
            .resolved()
            .iter()
            .filter_map(|(ref_id, resolved)| {
                (!self.instantiated_resolved_refs.contains(ref_id)).then_some((*ref_id, *resolved))
            })
            .collect::<Vec<_>>();

        for (ref_id, resolved) in refs {
            if !self.infer.is_frozen_ref_committed(resolved.def_id) {
                continue;
            }
            let Some(scheme) = self
                .infer
                .frozen_schemes
                .borrow()
                .get(&resolved.def_id)
                .cloned()
            else {
                continue;
            };
            let subst = crate::scheme::instantiate_frozen_scheme_with_subst(
                &self.infer,
                &scheme,
                resolved.ref_tv,
                &[],
            );
            if let Some(owner) = resolved.owner {
                self.infer
                    .instantiate_role_constraints_for_owner_with_scheme(
                        resolved.def_id,
                        owner,
                        &subst,
                        Some(&scheme),
                    );
            }
            self.instantiated_resolved_refs.insert(ref_id);
        }
    }

    pub fn with_owner<T>(&mut self, owner: DefId, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved = self.current_owner.replace(owner);
        let out = f(self);
        self.current_owner = saved;
        out
    }

    pub fn with_force_local_bindings<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.force_local_bindings_depth += 1;
        let out = f(self);
        self.force_local_bindings_depth -= 1;
        out
    }

    pub fn force_local_bindings(&self) -> bool {
        self.force_local_bindings_depth > 0
    }

    pub fn without_top_level_expr_owners<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.suppress_top_level_expr_owners_depth += 1;
        let out = f(self);
        self.suppress_top_level_expr_owners_depth -= 1;
        out
    }

    pub fn suppress_top_level_expr_owners(&self) -> bool {
        self.suppress_top_level_expr_owners_depth > 0
    }

    pub fn current_type_scope(&self) -> Option<&HashMap<String, TypeVar>> {
        self.type_var_scopes.last()
    }

    pub fn push_type_scope(&mut self, scope: HashMap<String, TypeVar>) {
        self.type_var_scopes.push(scope);
    }

    pub fn pop_type_scope(&mut self) {
        self.type_var_scopes.pop();
    }

    pub fn with_type_scope<T>(
        &mut self,
        scope: HashMap<String, TypeVar>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.push_type_scope(scope);
        let out = f(self);
        self.pop_type_scope();
        out
    }
}
