use std::collections::BTreeMap;

use yulang_core_ir as core_ir;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ShapeTable {
    pub exprs: Vec<ExprShape>,
    pub applies: Vec<ApplyShape>,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct CoreShapeProfile {
    pub exprs: usize,
    pub applies: usize,
    pub apply_complete: usize,
    pub apply_partial: usize,
    pub apply_missing_evidence: usize,
    pub apply_missing_context: usize,
    pub apply_missing_principal: usize,
    pub apply_with_principal: usize,
    pub apply_with_substitutions: usize,
    pub apply_with_substitution_candidates: usize,
    pub apply_with_principal_elaboration: usize,
    pub apply_principal_elaboration_complete: usize,
    pub apply_principal_elaboration_incomplete: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprShape {
    pub path: ExprPath,
    pub kind: ExprShapeKind,
    pub value: ValueShape,
    pub effect: EffectShape,
    pub status: ShapeStatus,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApplyShape {
    pub path: ExprPath,
    pub owner: Option<core_ir::Path>,
    pub target: Option<core_ir::Path>,
    pub callee_kind: ApplyHeadKind,
    pub callee_intrinsic: Option<core_ir::TypeBounds>,
    pub callee_contextual: Option<core_ir::TypeBounds>,
    pub arg_intrinsic: Option<core_ir::TypeBounds>,
    pub arg_contextual: Option<core_ir::TypeBounds>,
    pub result_intrinsic: Option<core_ir::TypeBounds>,
    pub callee_source_edge: Option<u32>,
    pub arg_source_edge: Option<u32>,
    pub principal_callee: Option<core_ir::Type>,
    pub substitutions: Vec<core_ir::TypeSubstitution>,
    pub substitution_candidates: Vec<core_ir::PrincipalSubstitutionCandidate>,
    pub principal_elaboration: Option<core_ir::PrincipalElaborationPlan>,
    pub status: ApplyShapeStatus,
    pub missing_reasons: Vec<ApplyShapeMissingReason>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprPath(pub Vec<ExprPathSegment>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprPathSegment {
    RootExpr(usize),
    Binding(core_ir::Path),
    LambdaBody,
    ApplyCallee,
    ApplyArg,
    IfCond,
    IfThen,
    IfElse,
    TupleItem(usize),
    RecordField(core_ir::Name),
    RecordSpread,
    VariantPayload,
    SelectBase,
    MatchScrutinee,
    MatchGuard(usize),
    MatchArmBody(usize),
    BlockStmt(usize),
    BlockTail,
    PatternDefault(core_ir::Name),
    ModuleBody,
    HandleBody,
    HandleGuard(usize),
    HandleArmBody(usize),
    CoerceInner,
    PackInner,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ApplyHeadKind {
    Path(core_ir::Path),
    Primitive(core_ir::PrimitiveOp),
    Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprShapeKind {
    Var,
    PrimitiveOp,
    Lit,
    Lambda,
    Apply,
    If,
    Tuple,
    Record,
    Variant,
    Select,
    Match,
    Block,
    Handle,
    Coerce,
    Pack,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ValueShape {
    pub intrinsic: Option<core_ir::TypeBounds>,
    pub contextual: Option<core_ir::TypeBounds>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct EffectShape {
    pub intrinsic: Option<core_ir::TypeBounds>,
    pub contextual: Option<core_ir::TypeBounds>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShapeStatus {
    Complete,
    Partial,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ApplyShapeStatus {
    Complete,
    MissingEvidence,
    MissingContext,
    MissingPrincipal,
    Partial,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ApplyShapeMissingReason {
    NoApplyEvidence,
    NoExpectedCallee,
    NoExpectedArg,
    RoleMethodWithoutPrincipal,
    EmptyCalleeBounds,
    EmptyArgBounds,
    EmptyResultBounds,
    NoPrincipalCallee,
    NoSubstitutions,
    NoSubstitutionCandidates,
}

pub(super) fn profile_core_program(program: &core_ir::CoreProgram) -> CoreShapeProfile {
    let table = collect_core_shape_table(program);
    if std::env::var_os("YULANG_DEBUG_CORE_SHAPES").is_some() {
        print_debug_core_shapes(&table);
    }
    table.profile()
}

pub(super) fn collect_core_shape_table(program: &core_ir::CoreProgram) -> ShapeTable {
    let mut collector = ShapeCollector::default();
    for binding in &program.program.bindings {
        collector.walk_expr(
            &binding.body,
            ExprPath(vec![ExprPathSegment::Binding(binding.name.clone())]),
        );
    }
    for (index, expr) in program.program.root_exprs.iter().enumerate() {
        collector.walk_expr(expr, ExprPath(vec![ExprPathSegment::RootExpr(index)]));
    }
    collector.table
}

impl ShapeTable {
    pub fn profile(&self) -> CoreShapeProfile {
        let mut profile = CoreShapeProfile {
            exprs: self.exprs.len(),
            applies: self.applies.len(),
            ..CoreShapeProfile::default()
        };
        for apply in &self.applies {
            match apply.status {
                ApplyShapeStatus::Complete => profile.apply_complete += 1,
                ApplyShapeStatus::MissingEvidence => profile.apply_missing_evidence += 1,
                ApplyShapeStatus::MissingContext => profile.apply_missing_context += 1,
                ApplyShapeStatus::MissingPrincipal => profile.apply_missing_principal += 1,
                ApplyShapeStatus::Partial => profile.apply_partial += 1,
            }
            if apply.principal_callee.is_some() {
                profile.apply_with_principal += 1;
            }
            if !apply.substitutions.is_empty() {
                profile.apply_with_substitutions += 1;
            }
            if !apply.substitution_candidates.is_empty() {
                profile.apply_with_substitution_candidates += 1;
            }
            if let Some(plan) = &apply.principal_elaboration {
                profile.apply_with_principal_elaboration += 1;
                if plan.complete {
                    profile.apply_principal_elaboration_complete += 1;
                } else {
                    profile.apply_principal_elaboration_incomplete += 1;
                }
            }
        }
        profile
    }
}

#[derive(Default)]
struct ShapeCollector {
    table: ShapeTable,
}

impl ShapeCollector {
    fn walk_expr(&mut self, expr: &core_ir::Expr, path: ExprPath) {
        self.table.exprs.push(expr_shape(expr, path.clone()));
        match expr {
            core_ir::Expr::Var(_) | core_ir::Expr::PrimitiveOp(_) | core_ir::Expr::Lit(_) => {}
            core_ir::Expr::Lambda { body, .. } => {
                self.walk_expr(body, path.child(ExprPathSegment::LambdaBody));
            }
            core_ir::Expr::Apply {
                callee,
                arg,
                evidence,
            } => {
                self.table
                    .applies
                    .push(apply_shape(&path, callee, evidence.as_ref()));
                self.walk_expr(callee, path.child(ExprPathSegment::ApplyCallee));
                self.walk_expr(arg, path.child(ExprPathSegment::ApplyArg));
            }
            core_ir::Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.walk_expr(cond, path.child(ExprPathSegment::IfCond));
                self.walk_expr(then_branch, path.child(ExprPathSegment::IfThen));
                self.walk_expr(else_branch, path.child(ExprPathSegment::IfElse));
            }
            core_ir::Expr::Tuple(items) => {
                for (index, item) in items.iter().enumerate() {
                    self.walk_expr(item, path.child(ExprPathSegment::TupleItem(index)));
                }
            }
            core_ir::Expr::Record { fields, spread } => {
                for field in fields {
                    self.walk_expr(
                        &field.value,
                        path.child(ExprPathSegment::RecordField(field.name.clone())),
                    );
                }
                if let Some(spread) = spread {
                    self.walk_record_spread(spread, path.child(ExprPathSegment::RecordSpread));
                }
            }
            core_ir::Expr::Variant { value, .. } => {
                if let Some(value) = value {
                    self.walk_expr(value, path.child(ExprPathSegment::VariantPayload));
                }
            }
            core_ir::Expr::Select { base, .. } => {
                self.walk_expr(base, path.child(ExprPathSegment::SelectBase));
            }
            core_ir::Expr::Match {
                scrutinee, arms, ..
            } => {
                self.walk_expr(scrutinee, path.child(ExprPathSegment::MatchScrutinee));
                for (index, arm) in arms.iter().enumerate() {
                    self.walk_pattern_defaults(&arm.pattern, &path);
                    if let Some(guard) = &arm.guard {
                        self.walk_expr(guard, path.child(ExprPathSegment::MatchGuard(index)));
                    }
                    self.walk_expr(&arm.body, path.child(ExprPathSegment::MatchArmBody(index)));
                }
            }
            core_ir::Expr::Block { stmts, tail } => {
                for (index, stmt) in stmts.iter().enumerate() {
                    self.walk_stmt(stmt, path.child(ExprPathSegment::BlockStmt(index)));
                }
                if let Some(tail) = tail {
                    self.walk_expr(tail, path.child(ExprPathSegment::BlockTail));
                }
            }
            core_ir::Expr::Handle { body, arms, .. } => {
                self.walk_expr(body, path.child(ExprPathSegment::HandleBody));
                for (index, arm) in arms.iter().enumerate() {
                    self.walk_pattern_defaults(&arm.payload, &path);
                    if let Some(guard) = &arm.guard {
                        self.walk_expr(guard, path.child(ExprPathSegment::HandleGuard(index)));
                    }
                    self.walk_expr(&arm.body, path.child(ExprPathSegment::HandleArmBody(index)));
                }
            }
            core_ir::Expr::Coerce { expr, .. } => {
                self.walk_expr(expr, path.child(ExprPathSegment::CoerceInner));
            }
            core_ir::Expr::Pack { expr, .. } => {
                self.walk_expr(expr, path.child(ExprPathSegment::PackInner));
            }
        }
    }

    fn walk_stmt(&mut self, stmt: &core_ir::Stmt, path: ExprPath) {
        match stmt {
            core_ir::Stmt::Let { pattern, value } => {
                self.walk_pattern_defaults(pattern, &path);
                self.walk_expr(value, path);
            }
            core_ir::Stmt::Expr(expr) => self.walk_expr(expr, path),
            core_ir::Stmt::Module { body, .. } => {
                self.walk_expr(body, path.child(ExprPathSegment::ModuleBody));
            }
        }
    }

    fn walk_record_spread(&mut self, spread: &core_ir::RecordSpreadExpr, path: ExprPath) {
        match spread {
            core_ir::RecordSpreadExpr::Head(expr) | core_ir::RecordSpreadExpr::Tail(expr) => {
                self.walk_expr(expr, path);
            }
        }
    }

    fn walk_pattern_defaults(&mut self, pattern: &core_ir::Pattern, path: &ExprPath) {
        match pattern {
            core_ir::Pattern::Wildcard | core_ir::Pattern::Bind(_) | core_ir::Pattern::Lit(_) => {}
            core_ir::Pattern::Tuple(items) => {
                for item in items {
                    self.walk_pattern_defaults(item, path);
                }
            }
            core_ir::Pattern::List {
                prefix,
                spread,
                suffix,
            } => {
                for item in prefix {
                    self.walk_pattern_defaults(item, path);
                }
                if let Some(spread) = spread {
                    self.walk_pattern_defaults(spread, path);
                }
                for item in suffix {
                    self.walk_pattern_defaults(item, path);
                }
            }
            core_ir::Pattern::Record { fields, .. } => {
                for field in fields {
                    self.walk_pattern_defaults(&field.pattern, path);
                    if let Some(default) = &field.default {
                        self.walk_expr(
                            default,
                            path.child(ExprPathSegment::PatternDefault(field.name.clone())),
                        );
                    }
                }
            }
            core_ir::Pattern::Variant { value, .. } => {
                if let Some(value) = value {
                    self.walk_pattern_defaults(value, path);
                }
            }
            core_ir::Pattern::Or { left, right } => {
                self.walk_pattern_defaults(left, path);
                self.walk_pattern_defaults(right, path);
            }
            core_ir::Pattern::As { pattern, .. } => {
                self.walk_pattern_defaults(pattern, path);
            }
        }
    }
}

impl ExprPath {
    fn child(&self, segment: ExprPathSegment) -> Self {
        let mut path = self.0.clone();
        path.push(segment);
        Self(path)
    }
}

fn expr_shape(expr: &core_ir::Expr, path: ExprPath) -> ExprShape {
    let kind = expr_shape_kind(expr);
    let value = value_shape(expr);
    let status = if value.intrinsic.is_some() && value.contextual.is_some() {
        ShapeStatus::Complete
    } else if value.intrinsic.is_some() || value.contextual.is_some() {
        ShapeStatus::Partial
    } else {
        ShapeStatus::Unknown
    };
    ExprShape {
        path,
        kind,
        value,
        effect: EffectShape::default(),
        status,
    }
}

fn value_shape(expr: &core_ir::Expr) -> ValueShape {
    match expr {
        core_ir::Expr::Apply { evidence, .. } => ValueShape {
            intrinsic: evidence.as_ref().map(|evidence| evidence.result.clone()),
            contextual: None,
        },
        core_ir::Expr::If { evidence, .. }
        | core_ir::Expr::Match { evidence, .. }
        | core_ir::Expr::Handle { evidence, .. } => ValueShape {
            intrinsic: evidence.as_ref().map(|evidence| evidence.result.clone()),
            contextual: None,
        },
        core_ir::Expr::Coerce { evidence, .. } => ValueShape {
            intrinsic: evidence.as_ref().map(|evidence| evidence.actual.clone()),
            contextual: evidence.as_ref().map(|evidence| evidence.expected.clone()),
        },
        _ => ValueShape::default(),
    }
}

fn apply_shape(
    path: &ExprPath,
    callee: &core_ir::Expr,
    evidence: Option<&core_ir::ApplyEvidence>,
) -> ApplyShape {
    let status = apply_shape_status(evidence);
    let missing_reasons = apply_shape_missing_reasons(evidence);
    ApplyShape {
        path: path.clone(),
        owner: path.owner(),
        target: core_apply_head_target(callee),
        callee_kind: apply_head_kind(callee),
        callee_intrinsic: evidence.map(|evidence| evidence.callee.clone()),
        callee_contextual: evidence.and_then(|evidence| evidence.expected_callee.clone()),
        arg_intrinsic: evidence.map(|evidence| evidence.arg.clone()),
        arg_contextual: evidence.and_then(|evidence| evidence.expected_arg.clone()),
        result_intrinsic: evidence.map(|evidence| evidence.result.clone()),
        callee_source_edge: evidence.and_then(|evidence| evidence.callee_source_edge),
        arg_source_edge: evidence.and_then(|evidence| evidence.arg_source_edge),
        principal_callee: evidence.and_then(|evidence| evidence.principal_callee.clone()),
        substitutions: evidence
            .map(|evidence| evidence.substitutions.clone())
            .unwrap_or_default(),
        substitution_candidates: evidence
            .map(|evidence| evidence.substitution_candidates.clone())
            .unwrap_or_default(),
        principal_elaboration: evidence.and_then(|evidence| evidence.principal_elaboration.clone()),
        status,
        missing_reasons,
    }
}

fn apply_shape_status(evidence: Option<&core_ir::ApplyEvidence>) -> ApplyShapeStatus {
    let Some(evidence) = evidence else {
        return ApplyShapeStatus::MissingEvidence;
    };
    if evidence.expected_callee.is_none() || evidence.expected_arg.is_none() {
        return ApplyShapeStatus::MissingContext;
    }
    if evidence.role_method && evidence.principal_callee.is_none() {
        return ApplyShapeStatus::MissingPrincipal;
    }
    if !bounds_present(&evidence.callee)
        || !bounds_present(&evidence.arg)
        || !bounds_present(&evidence.result)
    {
        return ApplyShapeStatus::Partial;
    }
    ApplyShapeStatus::Complete
}

fn bounds_present(bounds: &core_ir::TypeBounds) -> bool {
    bounds.lower.is_some() || bounds.upper.is_some()
}

fn apply_shape_missing_reasons(
    evidence: Option<&core_ir::ApplyEvidence>,
) -> Vec<ApplyShapeMissingReason> {
    let Some(evidence) = evidence else {
        return vec![ApplyShapeMissingReason::NoApplyEvidence];
    };
    let mut reasons = Vec::new();
    if evidence.expected_callee.is_none() {
        reasons.push(ApplyShapeMissingReason::NoExpectedCallee);
    }
    if evidence.expected_arg.is_none() {
        reasons.push(ApplyShapeMissingReason::NoExpectedArg);
    }
    if evidence.role_method && evidence.principal_callee.is_none() {
        reasons.push(ApplyShapeMissingReason::RoleMethodWithoutPrincipal);
    }
    if !bounds_present(&evidence.callee) {
        reasons.push(ApplyShapeMissingReason::EmptyCalleeBounds);
    }
    if !bounds_present(&evidence.arg) {
        reasons.push(ApplyShapeMissingReason::EmptyArgBounds);
    }
    if !bounds_present(&evidence.result) {
        reasons.push(ApplyShapeMissingReason::EmptyResultBounds);
    }
    if evidence.role_method && evidence.principal_callee.is_none() {
        reasons.push(ApplyShapeMissingReason::NoPrincipalCallee);
    }
    if evidence.principal_callee.is_some() && evidence.substitutions.is_empty() {
        reasons.push(ApplyShapeMissingReason::NoSubstitutions);
    }
    if evidence.principal_callee.is_some()
        && evidence.substitutions.is_empty()
        && evidence.substitution_candidates.is_empty()
    {
        reasons.push(ApplyShapeMissingReason::NoSubstitutionCandidates);
    }
    reasons
}

fn expr_shape_kind(expr: &core_ir::Expr) -> ExprShapeKind {
    match expr {
        core_ir::Expr::Var(_) => ExprShapeKind::Var,
        core_ir::Expr::PrimitiveOp(_) => ExprShapeKind::PrimitiveOp,
        core_ir::Expr::Lit(_) => ExprShapeKind::Lit,
        core_ir::Expr::Lambda { .. } => ExprShapeKind::Lambda,
        core_ir::Expr::Apply { .. } => ExprShapeKind::Apply,
        core_ir::Expr::If { .. } => ExprShapeKind::If,
        core_ir::Expr::Tuple(_) => ExprShapeKind::Tuple,
        core_ir::Expr::Record { .. } => ExprShapeKind::Record,
        core_ir::Expr::Variant { .. } => ExprShapeKind::Variant,
        core_ir::Expr::Select { .. } => ExprShapeKind::Select,
        core_ir::Expr::Match { .. } => ExprShapeKind::Match,
        core_ir::Expr::Block { .. } => ExprShapeKind::Block,
        core_ir::Expr::Handle { .. } => ExprShapeKind::Handle,
        core_ir::Expr::Coerce { .. } => ExprShapeKind::Coerce,
        core_ir::Expr::Pack { .. } => ExprShapeKind::Pack,
    }
}

fn print_debug_core_shapes(table: &ShapeTable) {
    eprintln!(
        "core-shapes: exprs={} applies={}",
        table.exprs.len(),
        table.applies.len()
    );
    print_debug_core_shape_missing_applies(table);
    print_debug_core_shape_principal_plans(table);
    if std::env::var_os("YULANG_TRACE_CORE_SHAPES").is_none() {
        return;
    }
    for apply in &table.applies {
        eprintln!(
            "  apply {:?}: owner={} target={} head={:?} status={:?} reasons={:?} callee_edge={:?} arg_edge={:?} principal={} substitutions={} candidates={}",
            apply.path,
            apply
                .owner
                .as_ref()
                .map(display_path)
                .unwrap_or_else(|| "<root>".to_string()),
            apply
                .target
                .as_ref()
                .map(display_path)
                .unwrap_or_else(|| "<unknown>".to_string()),
            apply.callee_kind,
            apply.status,
            apply.missing_reasons,
            apply.callee_source_edge,
            apply.arg_source_edge,
            apply.principal_callee.is_some(),
            apply.substitutions.len(),
            apply.substitution_candidates.len(),
        );
    }
}

fn print_debug_core_shape_principal_plans(table: &ShapeTable) {
    let mut counts: BTreeMap<String, PrincipalPlanDebugCounts> = BTreeMap::new();
    for apply in &table.applies {
        let Some(plan) = &apply.principal_elaboration else {
            continue;
        };
        let target = plan
            .target
            .as_ref()
            .map(display_path)
            .unwrap_or_else(|| apply_debug_target(apply));
        let counts = counts.entry(target).or_default();
        counts.total += 1;
        if plan.complete {
            counts.complete += 1;
        } else {
            counts.incomplete += 1;
            for reason in &plan.incomplete_reasons {
                *counts.reasons.entry(format!("{reason:?}")).or_default() += 1;
            }
        }
    }
    if counts.is_empty() {
        return;
    }
    eprintln!("core-shape principal plans:");
    for (target, counts) in counts {
        eprintln!(
            "  {target}: total={} complete={} incomplete={}",
            counts.total, counts.complete, counts.incomplete
        );
        for (reason, count) in counts.reasons {
            eprintln!("    {reason}: {count}");
        }
    }
}

#[derive(Default)]
struct PrincipalPlanDebugCounts {
    total: usize,
    complete: usize,
    incomplete: usize,
    reasons: BTreeMap<String, usize>,
}

fn print_debug_core_shape_missing_applies(table: &ShapeTable) {
    let mut counts: BTreeMap<String, BTreeMap<ApplyShapeMissingReason, usize>> = BTreeMap::new();
    for apply in &table.applies {
        if apply.missing_reasons.is_empty() {
            continue;
        }
        let target = apply_debug_target(apply);
        let target_counts = counts.entry(target).or_default();
        for reason in &apply.missing_reasons {
            *target_counts.entry(*reason).or_default() += 1;
        }
    }
    if counts.is_empty() {
        return;
    }
    eprintln!("core-shape missing applies:");
    for (target, reasons) in counts {
        eprintln!("  {target}:");
        for (reason, count) in reasons {
            eprintln!("    {reason:?}: {count}");
        }
    }
}

fn apply_debug_target(apply: &ApplyShape) -> String {
    apply
        .target
        .as_ref()
        .map(display_path)
        .unwrap_or_else(|| match &apply.callee_kind {
            ApplyHeadKind::Primitive(op) => format!("{op:?}"),
            ApplyHeadKind::Path(path) => display_path(path),
            ApplyHeadKind::Other => "<unknown>".to_string(),
        })
}

fn apply_head_kind(expr: &core_ir::Expr) -> ApplyHeadKind {
    match expr {
        core_ir::Expr::Var(path) => ApplyHeadKind::Path(path.clone()),
        core_ir::Expr::PrimitiveOp(op) => ApplyHeadKind::Primitive(*op),
        core_ir::Expr::Apply { callee, .. } => apply_head_kind(callee),
        _ => ApplyHeadKind::Other,
    }
}

fn core_apply_head_target(expr: &core_ir::Expr) -> Option<core_ir::Path> {
    match expr {
        core_ir::Expr::Var(path) => Some(path.clone()),
        core_ir::Expr::Apply { callee, .. } => core_apply_head_target(callee),
        _ => None,
    }
}

impl ExprPath {
    fn owner(&self) -> Option<core_ir::Path> {
        self.0.iter().find_map(|segment| match segment {
            ExprPathSegment::Binding(path) => Some(path.clone()),
            _ => None,
        })
    }
}

fn display_path(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn apply_with_evidence_fills_apply_shape_slots() {
        let evidence = core_ir::ApplyEvidence {
            callee_source_edge: Some(1),
            arg_source_edge: Some(2),
            callee: bounds(named_type("fun")),
            expected_callee: Some(bounds(named_type("expected_fun"))),
            arg: bounds(named_type("bool")),
            expected_arg: Some(bounds(named_type("int"))),
            result: bounds(named_type("str")),
            principal_callee: Some(named_type("principal")),
            substitutions: vec![core_ir::TypeSubstitution {
                var: core_ir::TypeVar("a".to_string()),
                ty: named_type("int"),
            }],
            substitution_candidates: vec![core_ir::PrincipalSubstitutionCandidate {
                var: core_ir::TypeVar("b".to_string()),
                relation: core_ir::PrincipalCandidateRelation::Exact,
                ty: named_type("bool"),
                source_edge: Some(2),
                path: vec![core_ir::PrincipalSlotPathSegment::Arg],
            }],
            role_method: false,
            principal_elaboration: None,
        };
        let program = program_with_root(core_ir::Expr::Apply {
            callee: Box::new(core_ir::Expr::Var(path("f"))),
            arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))),
            evidence: Some(evidence),
        });

        let table = collect_core_shape_table(&program);

        assert_eq!(table.applies.len(), 1);
        let apply = &table.applies[0];
        assert_eq!(apply.status, ApplyShapeStatus::Complete);
        assert_eq!(apply.callee_source_edge, Some(1));
        assert_eq!(apply.arg_source_edge, Some(2));
        assert!(apply.callee_intrinsic.is_some());
        assert!(apply.callee_contextual.is_some());
        assert!(apply.arg_intrinsic.is_some());
        assert!(apply.arg_contextual.is_some());
        assert!(apply.result_intrinsic.is_some());
        assert!(apply.principal_callee.is_some());
        assert_eq!(apply.substitutions.len(), 1);
        assert_eq!(apply.substitution_candidates.len(), 1);
    }

    #[test]
    fn apply_without_evidence_is_missing_evidence() {
        let program = program_with_root(core_ir::Expr::Apply {
            callee: Box::new(core_ir::Expr::Var(path("f"))),
            arg: Box::new(core_ir::Expr::Lit(core_ir::Lit::Unit)),
            evidence: None,
        });

        let profile = collect_core_shape_table(&program).profile();

        assert_eq!(profile.applies, 1);
        assert_eq!(profile.apply_missing_evidence, 1);
    }

    #[test]
    fn roots_and_bindings_produce_shape_entries_for_nested_exprs() {
        let binding_path = path("id");
        let program = core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: vec![core_ir::PrincipalBinding {
                    name: binding_path.clone(),
                    scheme: core_ir::Scheme {
                        requirements: Vec::new(),
                        body: named_type("int"),
                    },
                    body: core_ir::Expr::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(core_ir::Expr::Var(binding_path)),
                    },
                }],
                root_exprs: vec![core_ir::Expr::Tuple(vec![
                    core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string())),
                    core_ir::Expr::Lit(core_ir::Lit::Int("2".to_string())),
                ])],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView::default(),
            evidence: core_ir::PrincipalEvidence::default(),
        };

        let table = collect_core_shape_table(&program);

        assert_eq!(table.exprs.len(), 5);
        assert!(
            table
                .exprs
                .iter()
                .any(|shape| matches!(shape.path.0.as_slice(), [ExprPathSegment::Binding(_)]))
        );
        assert!(table.exprs.iter().any(|shape| matches!(
            shape.path.0.as_slice(),
            [ExprPathSegment::RootExpr(0), ExprPathSegment::TupleItem(1)]
        )));
    }

    fn program_with_root(expr: core_ir::Expr) -> core_ir::CoreProgram {
        core_ir::CoreProgram {
            program: core_ir::PrincipalModule {
                path: core_ir::Path::default(),
                bindings: Vec::new(),
                root_exprs: vec![expr],
                roots: vec![core_ir::PrincipalRoot::Expr(0)],
            },
            graph: core_ir::CoreGraphView::default(),
            evidence: core_ir::PrincipalEvidence::default(),
        }
    }

    fn bounds(ty: core_ir::Type) -> core_ir::TypeBounds {
        core_ir::TypeBounds::exact(ty)
    }

    fn named_type(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }
}
