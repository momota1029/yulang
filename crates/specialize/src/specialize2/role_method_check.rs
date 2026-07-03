use super::*;

impl RoleMethodChecker {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn check(mut self, arena: &poly_expr::Arena) -> Vec<RoleMethodCheckOutcome> {
        let mut pending = VecDeque::new();
        for root in &arena.runtime_roots {
            match root {
                poly_expr::RuntimeRoot::Expr(expr) => {
                    self.extend_task(
                        arena,
                        &mut pending,
                        TaskSolver::check_root_expr_role_methods(arena, *expr),
                    );
                }
                poly_expr::RuntimeRoot::ComputedDef(def) => {
                    if let Ok((body, signature)) = computed_def_body_signature(arena, *def) {
                        pending.push_back((*def, body, signature));
                    }
                }
            }
        }
        while let Some((def, body, signature)) = pending.pop_front() {
            let key = InstanceKey { def, ty: signature };
            if !self.checked_instances.insert(key.clone()) {
                continue;
            }
            self.extend_task(
                arena,
                &mut pending,
                TaskSolver::check_def_body_signature_role_methods(arena, body, key.ty),
            );
        }
        self.outcomes
            .sort_by_key(|outcome| (outcome.select.0, outcome.member.0));
        self.outcomes.dedup();
        self.outcomes
    }

    fn extend_task(
        &mut self,
        arena: &poly_expr::Arena,
        pending: &mut VecDeque<(poly_expr::DefId, poly_expr::ExprId, Type)>,
        result: Result<RoleMethodCheckTask, SpecializeError>,
    ) {
        let Ok(task) = result else {
            return;
        };
        self.outcomes.extend(task.outcomes);
        self.enqueue_ref_instances(arena, pending, task.ref_signatures);
        self.enqueue_select_instances(arena, pending, task.select_signatures);
        self.enqueue_typeclass_instances(arena, pending, task.typeclass_resolutions);
    }

    fn enqueue_ref_instances(
        &self,
        arena: &poly_expr::Arena,
        pending: &mut VecDeque<(poly_expr::DefId, poly_expr::ExprId, Type)>,
        signatures: HashMap<poly_expr::ExprId, Type>,
    ) {
        for (expr, signature) in signatures {
            let poly_expr::Expr::Var(ref_id) = arena.expr(expr) else {
                continue;
            };
            let Some(def) = arena.ref_target(*ref_id) else {
                continue;
            };
            if let Some(body) = let_body_if_instance(arena, def) {
                pending.push_back((def, body, signature));
            }
        }
    }

    fn enqueue_select_instances(
        &self,
        arena: &poly_expr::Arena,
        pending: &mut VecDeque<(poly_expr::DefId, poly_expr::ExprId, Type)>,
        signatures: HashMap<poly_expr::ExprId, Type>,
    ) {
        for (expr, signature) in signatures {
            let poly_expr::Expr::Select(_, select_id) = arena.expr(expr) else {
                continue;
            };
            let Some(poly_expr::SelectResolution::Method { def }) =
                arena.select(*select_id).resolution
            else {
                continue;
            };
            if arena.field_projections.contains(&def) {
                continue;
            }
            if let Some(body) = let_body_if_instance(arena, def) {
                pending.push_back((def, body, signature));
            }
        }
    }

    fn enqueue_typeclass_instances(
        &self,
        arena: &poly_expr::Arena,
        pending: &mut VecDeque<(poly_expr::DefId, poly_expr::ExprId, Type)>,
        resolutions: HashMap<poly_expr::ExprId, TypeclassResolution>,
    ) {
        for resolution in resolutions.into_values() {
            if let Some(body) = let_body_if_instance(arena, resolution.implementation) {
                pending.push_back((resolution.implementation, body, resolution.signature));
            }
        }
    }
}

fn let_body_if_instance(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
) -> Option<poly_expr::ExprId> {
    match arena.defs.get(def) {
        Some(poly_expr::Def::Let {
            body: Some(body), ..
        }) => Some(*body),
        _ => None,
    }
}

fn computed_def_body_signature(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
) -> Result<(poly_expr::ExprId, Type), SpecializeError> {
    let body = let_body(arena, def)?;
    let signature = TaskSolver::solve_computed_def_signature(arena, def, body)?;
    Ok((body, signature))
}
