//! Extracted lowering implementation.

pub(super) mod block_local;
pub(super) mod chain;
pub(super) mod constraints;
pub(super) mod lambda;
pub(super) mod method_body;
pub(super) mod tail;

use super::*;

pub struct ExprLowerer<'a> {
    pub(super) session: &'a mut AnalysisSession,
    pub(super) modules: &'a ModuleTable,
    pub(super) module: ModuleId,
    pub(super) source_file: Path,
    pub(super) site: ModuleOrder,
    pub(super) parent: poly::expr::DefId,
    pub(super) parent_has_type_annotation: bool,
    pub(super) labels: Option<&'a mut DumpLabels>,
    pub(super) self_alias: Option<AnnSelfAlias>,
    pub(super) type_var_aliases: Vec<(String, String)>,
    pub(super) type_name_aliases: Vec<(String, TypeDeclId)>,
    pub(super) local_method_scope: Option<ModuleId>,
    pub(super) synthetic_var_acts: Vec<SyntheticVarActUse>,
    pub(super) synthetic_var_act_cursor: usize,
    pub(super) synthetic_sub_label_acts: Vec<SyntheticSubLabelActUse>,
    pub(super) synthetic_sub_label_act_cursor: usize,
    pub(super) known_ref_targets: FxHashMap<RefId, DefId>,
    pub(super) locals: Vec<LocalBinding>,
    pub(super) sub_syntax_scopes: Vec<SubSyntaxScope>,
    pub(super) effect_views: Vec<LocalEffect>,
    pub(super) function_frames: Vec<FunctionPredicateFrame>,
    pub(super) active_defined_skeletons: Vec<ActiveDefinedLambdaSkeleton>,
    pub(super) connected_defined_skeleton_predicates: FxHashSet<DefinedSkeletonPredicateKey>,
    pub(super) local_generalize_boundary: TypeLevel,
    pub(super) do_replacement: Option<Computation>,
    pub(super) pattern_binding_rewrites: FxHashMap<Name, Name>,
}

#[derive(Clone)]
pub(in crate::lowering) enum LambdaBodyMode {
    Expr,
    Sub { label: Option<Name> },
}

impl<'a> ExprLowerer<'a> {
    #[allow(dead_code)]
    pub fn new(
        session: &'a mut AnalysisSession,
        modules: &'a ModuleTable,
        module: ModuleId,
        site: ModuleOrder,
        parent: poly::expr::DefId,
    ) -> Self {
        let local_generalize_boundary = session.infer.current_level();
        let synthetic_var_acts = modules.synthetic_var_act_uses(parent).to_vec();
        let synthetic_sub_label_acts = modules.synthetic_sub_label_act_uses(parent).to_vec();
        Self {
            session,
            modules,
            module,
            source_file: Path::default(),
            site,
            parent,
            parent_has_type_annotation: false,
            labels: None,
            self_alias: None,
            type_var_aliases: Vec::new(),
            type_name_aliases: Vec::new(),
            local_method_scope: None,
            synthetic_var_acts,
            synthetic_var_act_cursor: 0,
            synthetic_sub_label_acts,
            synthetic_sub_label_act_cursor: 0,
            known_ref_targets: FxHashMap::default(),
            locals: Vec::new(),
            sub_syntax_scopes: Vec::new(),
            effect_views: Vec::new(),
            function_frames: Vec::new(),
            active_defined_skeletons: Vec::new(),
            connected_defined_skeleton_predicates: FxHashSet::default(),
            local_generalize_boundary,
            do_replacement: None,
            pattern_binding_rewrites: FxHashMap::default(),
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
        let synthetic_sub_label_acts = modules.synthetic_sub_label_act_uses(parent).to_vec();
        Self {
            session,
            modules,
            module,
            source_file: Path::default(),
            site,
            parent,
            parent_has_type_annotation: false,
            labels: Some(labels),
            self_alias: None,
            type_var_aliases: Vec::new(),
            type_name_aliases: Vec::new(),
            local_method_scope: None,
            synthetic_var_acts,
            synthetic_var_act_cursor: 0,
            synthetic_sub_label_acts,
            synthetic_sub_label_act_cursor: 0,
            known_ref_targets: FxHashMap::default(),
            locals: Vec::new(),
            sub_syntax_scopes: Vec::new(),
            effect_views: Vec::new(),
            function_frames: Vec::new(),
            active_defined_skeletons: Vec::new(),
            connected_defined_skeleton_predicates: FxHashSet::default(),
            local_generalize_boundary,
            do_replacement: None,
            pattern_binding_rewrites: FxHashMap::default(),
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

    pub fn with_type_name_aliases(mut self, aliases: &[(String, TypeDeclId)]) -> Self {
        self.type_name_aliases = aliases.to_vec();
        self
    }

    pub fn with_local_method_scope(mut self, scope: Option<ModuleId>) -> Self {
        self.local_method_scope = scope;
        self
    }

    pub fn with_source_file(mut self, source_file: Path) -> Self {
        self.source_file = source_file;
        self
    }

    pub fn with_parent_type_annotation(mut self, parent_has_type_annotation: bool) -> Self {
        self.parent_has_type_annotation = parent_has_type_annotation;
        self
    }

    pub(super) fn source_span(&self, range: Option<SourceRange>) -> Option<SourceSpan> {
        range.map(|range| SourceSpan {
            file: self.source_file.clone(),
            range,
        })
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

    #[allow(dead_code)]
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
}
