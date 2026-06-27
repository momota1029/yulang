use super::*;

impl Specializer2 {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn specialize(self, arena: &poly_expr::Arena) -> Result<Program, SpecializeError> {
        Ok(self.specialize_with_runtime_evidence(arena)?.program)
    }

    pub(super) fn specialize_with_runtime_evidence(
        mut self,
        arena: &poly_expr::Arena,
    ) -> Result<SpecializeOutput, SpecializeError> {
        let mut roots = Vec::new();
        for root in &arena.runtime_roots {
            roots.push(match root {
                poly_expr::RuntimeRoot::Expr(expr) => {
                    let root_index = roots.len() as u32;
                    let expr_id = *expr;
                    let solved = TaskSolver::solve_root_expr(arena, expr_id)?;
                    self.runtime_evidence.push_solved_task(
                        RuntimeEvidenceTaskOwner::RootExpr {
                            root_index,
                            expr: expr_id.0,
                        },
                        &solved,
                    );
                    let expr = self.emit_expr_typed(arena, &solved, expr_id)?;
                    Root::Expr(force_emitted_expr_if_thunk(
                        solved.actual_type_of(expr_id),
                        expr,
                    ))
                }
                poly_expr::RuntimeRoot::ComputedDef(def) => {
                    Root::EvalInstance(self.ensure_computed_def_instance(arena, *def)?)
                }
            });
        }
        let instances = self
            .instances
            .into_iter()
            .enumerate()
            .map(|(index, instance)| {
                instance.ok_or(SpecializeError::InternalMissingInstance {
                    instance: InstanceId(index as u32),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let program = Program { roots, instances };
        if std::env::var_os("YULANG_DEBUG_MONO").is_some() {
            eprintln!("{}", mono::dump::dump_program(&program));
        }
        Ok(SpecializeOutput {
            program,
            runtime_evidence: self.runtime_evidence,
        })
    }

    pub(super) fn ensure_computed_def_instance(
        &mut self,
        arena: &poly_expr::Arena,
        def: poly_expr::DefId,
    ) -> Result<InstanceId, SpecializeError> {
        let body = let_body(arena, def)?;
        let signature = TaskSolver::solve_computed_def_signature(arena, def, body)?;
        self.ensure_def_instance(arena, def, signature)
    }

    pub(super) fn ensure_def_instance(
        &mut self,
        arena: &poly_expr::Arena,
        def: poly_expr::DefId,
        signature_ty: Type,
    ) -> Result<InstanceId, SpecializeError> {
        let inference_signature_ty = signature_ty;
        let runtime_signature_ty =
            close_resolved_runtime_surface(inference_signature_ty.clone(), TypeSlotKind::Value);
        let marker_signature_ty =
            close_resolved_inference_surface(inference_signature_ty.clone(), TypeSlotKind::Value);
        let key = InstanceKey {
            def,
            ty: runtime_signature_ty.clone(),
        };
        if let Some(instance) = self.instance_by_key.get(&key).copied() {
            return Ok(instance);
        }
        let Some(poly_def) = arena.defs.get(def) else {
            return Err(SpecializeError::MissingDef {
                def: convert_def(def),
            });
        };
        let poly_expr::Def::Let { scheme, body, .. } = poly_def else {
            return Err(SpecializeError::UnsupportedDefKind {
                def: convert_def(def),
                kind: def_kind(poly_def),
            });
        };
        let Some(_scheme) = scheme else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            });
        };
        let Some(body) = *body else {
            return Err(SpecializeError::MissingBody {
                def: convert_def(def),
            });
        };

        let id = InstanceId(self.instances.len() as u32);
        self.instance_by_key.insert(key, id);
        self.instances.push(None);
        self.active_instance_signatures
            .insert(id, runtime_signature_ty.clone());

        let solved = TaskSolver::solve_def_body(arena, def, body, inference_signature_ty)?;
        self.runtime_evidence.push_solved_task(
            RuntimeEvidenceTaskOwner::InstanceBody {
                instance: id.0,
                def: def.0,
                body: body.0,
            },
            &solved,
        );
        let mut body = self.emit_expr(arena, &solved, body)?;
        body = wrap_stack_handler_marker(&marker_signature_ty, body);
        self.instances[id.0 as usize] = Some(Instance {
            id,
            source: InstanceSource::Def(convert_def(def)),
            signature: Signature {
                ty: runtime_signature_ty,
            },
            body,
        });
        self.active_instance_signatures.remove(&id);
        Ok(id)
    }

    pub(super) fn emit_expr(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
    ) -> Result<Expr, SpecializeError> {
        Ok(self.emit_expr_typed(arena, solved, expr)?.expr)
    }

    pub(super) fn emit_expr_typed(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
    ) -> Result<EmittedExpr, SpecializeError> {
        self.emit_expr_with_boundary(arena, solved, expr, true)
    }

    pub(super) fn emit_expr_without_boundary(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
    ) -> Result<EmittedExpr, SpecializeError> {
        self.emit_expr_with_boundary(arena, solved, expr, false)
    }

    pub(super) fn emit_expr_with_boundary(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
        wrap_boundary: bool,
    ) -> Result<EmittedExpr, SpecializeError> {
        use poly_expr::Expr as PolyExpr;
        let kind = match arena.expr(expr) {
            PolyExpr::Lit(lit) => ExprKind::Lit(convert_lit(lit)),
            PolyExpr::PrimitiveOp(op) => ExprKind::PrimitiveOp {
                op: convert_primitive_op(*op),
                context: primitive_context(arena, *op, solved.actual_type_of(expr)),
            },
            PolyExpr::Var(ref_id) => self.emit_var(arena, solved, expr, *ref_id)?,
            PolyExpr::App(callee, arg) => {
                let callee_expr = self.emit_expr(arena, solved, *callee)?;
                let argument_effect_contract = callee_argument_effect_contract(arena, *callee);
                let arg_expr = self.emit_expr_without_boundary(arena, solved, *arg)?;
                let arg_expr = self.wrap_expr_boundary_with_argument_contract(
                    arena,
                    solved,
                    *arg,
                    arg_expr,
                    argument_effect_contract,
                )?;
                ExprKind::Apply(Box::new(callee_expr), Box::new(arg_expr.expr))
            }
            PolyExpr::RefSet(reference, value) => ExprKind::RefSet(
                Box::new(self.emit_expr(arena, solved, *reference)?),
                Box::new(self.emit_expr(arena, solved, *value)?),
            ),
            PolyExpr::Lambda(param, body) => ExprKind::Lambda(
                self.emit_pat(arena, solved, *param)?,
                Box::new(self.emit_lambda_body(arena, solved, expr, *body)?),
            ),
            PolyExpr::Tuple(items) => ExprKind::Tuple(self.emit_exprs(arena, solved, items)?),
            PolyExpr::Record { fields, spread } => ExprKind::Record {
                fields: fields
                    .iter()
                    .map(|(name, value)| {
                        Ok(RecordField {
                            name: name.clone(),
                            value: self.emit_expr(arena, solved, *value)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                spread: self.emit_record_spread(arena, solved, spread)?,
            },
            PolyExpr::PolyVariant(tag, payloads) => ExprKind::PolyVariant {
                tag: tag.clone(),
                payloads: self.emit_exprs(arena, solved, payloads)?,
            },
            PolyExpr::Select(base, select) => {
                let select_data = arena.select(*select);
                ExprKind::Select {
                    base: Box::new(self.emit_expr(arena, solved, *base)?),
                    name: select_data.name.clone(),
                    resolution: self.emit_select_resolution(arena, solved, *base, expr)?,
                }
            }
            PolyExpr::Case(scrutinee, arms) => ExprKind::Case {
                scrutinee: Box::new(self.emit_expr(arena, solved, *scrutinee)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CaseArm {
                            pat: self.emit_pat(arena, solved, arm.pat)?,
                            guard: self.emit_optional_expr(arena, solved, arm.guard)?,
                            body: self.emit_expr(arena, solved, arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            },
            PolyExpr::Catch(body, arms) => ExprKind::Catch {
                body: Box::new(self.emit_catch_body(arena, solved, *body)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CatchArm {
                            operation_path: arm
                                .operation
                                .as_ref()
                                .map(|operation| operation.path.clone()),
                            pat: self.emit_pat(arena, solved, arm.pat)?,
                            continuation: self.emit_optional_pat(
                                arena,
                                solved,
                                arm.continuation,
                            )?,
                            guard: self.emit_optional_expr(arena, solved, arm.guard)?,
                            body: self.emit_catch_body(arena, solved, arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            },
            PolyExpr::Block(stmts, tail) => {
                ExprKind::Block(self.emit_block(arena, solved, stmts, *tail)?)
            }
        };
        let expr_out = Expr::new(kind);
        let mut expr_out = EmittedExpr::pure(expr_out, raw_expr_value_type(arena, solved, expr));
        if raw_expr_is_computation(arena, solved, expr) {
            expr_out =
                self.lift_raw_expr_to_computation(arena, solved.actual_type_of(expr), expr_out)?;
        }
        if wrap_boundary {
            self.wrap_expr_boundary(arena, solved, expr, expr_out)
        } else {
            Ok(expr_out)
        }
    }

    pub(super) fn emit_var(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
        ref_id: poly_expr::RefId,
    ) -> Result<ExprKind, SpecializeError> {
        let Some(def) = arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if self.local_defs.contains_key(&def) {
            return Ok(ExprKind::Local(convert_def(def)));
        }
        if let Some(resolution) = solved.typeclass_resolution(expr) {
            return Ok(ExprKind::InstanceRef(self.ensure_def_instance(
                arena,
                resolution.implementation,
                resolution.signature.clone(),
            )?));
        }
        match arena.defs.get(def) {
            Some(poly_expr::Def::Arg) => Ok(ExprKind::Local(convert_def(def))),
            _ if let Some(constructor) = arena.constructors.get(&def) => {
                Ok(ExprKind::Constructor {
                    def: convert_def(def),
                    arity: constructor.arity,
                })
            }
            _ if let Some(operation) = arena.effect_operations.get(&def) => {
                Ok(ExprKind::EffectOp {
                    path: operation.path.clone(),
                })
            }
            Some(poly_expr::Def::Let { body: Some(_), .. }) => {
                let signature =
                    solved
                        .ref_signature(expr)
                        .ok_or(SpecializeError::MissingExprType {
                            expr: expr.0,
                            role: ExprTypeRole::Actual,
                        })?;
                let instance = self.ensure_def_instance(arena, def, signature.clone())?;
                Ok(ExprKind::InstanceRef(instance))
            }
            Some(poly_expr::Def::Let { body: None, .. }) => Ok(ExprKind::Local(convert_def(def))),
            Some(other) => Err(SpecializeError::UnsupportedDefKind {
                def: convert_def(def),
                kind: def_kind(other),
            }),
            None => Err(SpecializeError::MissingDef {
                def: convert_def(def),
            }),
        }
    }

    pub(super) fn emit_select_resolution(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        base: poly_expr::ExprId,
        select: poly_expr::ExprId,
    ) -> Result<Option<SelectResolution>, SpecializeError> {
        let poly_expr::Expr::Select(_, select_id) = arena.expr(select) else {
            return Ok(None);
        };
        match arena.select(*select_id).resolution {
            None => Ok(None),
            Some(poly_expr::SelectResolution::RecordField) => {
                Ok(Some(SelectResolution::RecordField))
            }
            Some(poly_expr::SelectResolution::Method { def }) => {
                if arena.field_projections.contains(&def) {
                    return Ok(Some(SelectResolution::RecordField));
                }
                let signature =
                    solved
                        .select_signature(select)
                        .ok_or(SpecializeError::MissingExprType {
                            expr: select.0,
                            role: ExprTypeRole::Actual,
                        })?;
                Ok(Some(SelectResolution::Method {
                    instance: self.ensure_def_instance(arena, def, signature.clone())?,
                }))
            }
            Some(poly_expr::SelectResolution::TypeclassMethod { .. }) => {
                let resolution = solved.typeclass_resolution(select).ok_or(
                    SpecializeError::MissingExprType {
                        expr: base.0,
                        role: ExprTypeRole::Actual,
                    },
                )?;
                Ok(Some(SelectResolution::Method {
                    instance: self.ensure_def_instance(
                        arena,
                        resolution.implementation,
                        resolution.signature.clone(),
                    )?,
                }))
            }
        }
    }

    pub(super) fn emit_pat(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        pat: poly_expr::PatId,
    ) -> Result<Pat, SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match arena.pat(pat) {
            PolyPat::Wild => Ok(Pat::Wild),
            PolyPat::Lit(lit) => Ok(Pat::Lit(convert_lit(lit))),
            PolyPat::Tuple(items) => Ok(Pat::Tuple(self.emit_pats(arena, solved, items)?)),
            PolyPat::List {
                prefix,
                spread,
                suffix,
            } => Ok(Pat::List {
                prefix: self.emit_pats(arena, solved, prefix)?,
                spread: self
                    .emit_optional_pat(arena, solved, *spread)?
                    .map(Box::new),
                suffix: self.emit_pats(arena, solved, suffix)?,
            }),
            PolyPat::Record { fields, spread } => Ok(Pat::Record {
                fields: fields
                    .iter()
                    .map(|field| {
                        Ok(mono::RecordPatField {
                            name: field.name.clone(),
                            pat: self.emit_pat(arena, solved, field.pat)?,
                            default: self.emit_optional_expr(arena, solved, field.default)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                spread: convert_def_spread(spread),
            }),
            PolyPat::PolyVariant(tag, payloads) => Ok(Pat::PolyVariant(
                tag.clone(),
                self.emit_pats(arena, solved, payloads)?,
            )),
            PolyPat::Con(ref_id, payloads) => {
                let Some(def) = arena.ref_target(*ref_id) else {
                    return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
                };
                Ok(Pat::Con(
                    convert_def(def),
                    self.emit_pats(arena, solved, payloads)?,
                ))
            }
            PolyPat::Ref(ref_id) => {
                let Some(def) = arena.ref_target(*ref_id) else {
                    return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
                };
                let Some(poly_expr::Def::Let { body: Some(_), .. }) = arena.defs.get(def) else {
                    return Ok(Pat::Ref(InstanceId(convert_def(def).0)));
                };
                let signature =
                    solved
                        .pat_ref_signature(pat)
                        .ok_or(SpecializeError::MissingExprType {
                            expr: pat.0,
                            role: ExprTypeRole::Actual,
                        })?;
                Ok(Pat::Ref(self.ensure_def_instance(
                    arena,
                    def,
                    signature.clone(),
                )?))
            }
            PolyPat::Var(def) => Ok(Pat::Var(convert_def(*def))),
            PolyPat::Or(left, right) => Ok(Pat::Or(
                Box::new(self.emit_pat(arena, solved, *left)?),
                Box::new(self.emit_pat(arena, solved, *right)?),
            )),
            PolyPat::As(inner, def) => Ok(Pat::As(
                Box::new(self.emit_pat(arena, solved, *inner)?),
                convert_def(*def),
            )),
        }
    }

    pub(super) fn emit_exprs(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        exprs: &[poly_expr::ExprId],
    ) -> Result<Vec<Expr>, SpecializeError> {
        exprs
            .iter()
            .map(|expr| self.emit_expr(arena, solved, *expr))
            .collect()
    }

    pub(super) fn emit_pats(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        pats: &[poly_expr::PatId],
    ) -> Result<Vec<Pat>, SpecializeError> {
        pats.iter()
            .map(|pat| self.emit_pat(arena, solved, *pat))
            .collect()
    }

    pub(super) fn emit_optional_expr(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: Option<poly_expr::ExprId>,
    ) -> Result<Option<Expr>, SpecializeError> {
        expr.map(|expr| self.emit_expr(arena, solved, expr))
            .transpose()
    }

    pub(super) fn emit_optional_pat(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        pat: Option<poly_expr::PatId>,
    ) -> Result<Option<Pat>, SpecializeError> {
        pat.map(|pat| self.emit_pat(arena, solved, pat)).transpose()
    }

    pub(super) fn emit_block(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        stmts: &[poly_expr::Stmt],
        tail: Option<poly_expr::ExprId>,
    ) -> Result<Block, SpecializeError> {
        let mut scoped_defs = Vec::new();
        let stmts = self.emit_stmts(arena, solved, stmts, &mut scoped_defs)?;
        let tail = self.emit_optional_expr(arena, solved, tail)?.map(Box::new);
        for def in scoped_defs {
            self.pop_local_def(def);
        }
        Ok(Block { stmts, tail })
    }

    pub(super) fn emit_stmts(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        stmts: &[poly_expr::Stmt],
        scoped_defs: &mut Vec<poly_expr::DefId>,
    ) -> Result<Vec<Stmt>, SpecializeError> {
        let mut out = Vec::with_capacity(stmts.len());
        for stmt in stmts {
            out.push(match stmt {
                poly_expr::Stmt::Let(vis, pat, value) => {
                    let mut defs = Vec::new();
                    collect_pattern_defs(arena, *pat, &mut defs);
                    for def in &defs {
                        self.push_local_def(*def);
                    }
                    let value = self.emit_expr(arena, solved, *value)?;
                    let pat = self.emit_pat(arena, solved, *pat)?;
                    for def in defs {
                        scoped_defs.push(def);
                    }
                    Stmt::Let(convert_vis(*vis), pat, value)
                }
                poly_expr::Stmt::Expr(expr) => {
                    if let poly_expr::Expr::Block(stmts, tail) = arena.expr(*expr) {
                        out.extend(self.emit_stmts(arena, solved, stmts, scoped_defs)?);
                        if let Some(tail) = tail {
                            let actual = solved.actual_type_of(*tail).cloned();
                            let tail = self.emit_expr_without_boundary(arena, solved, *tail)?;
                            out.push(Stmt::Expr(force_emitted_expr_if_thunk(
                                actual.as_ref(),
                                tail,
                            )));
                        }
                        continue;
                    }
                    let actual = solved.actual_type_of(*expr).cloned();
                    let expr = self.emit_expr_without_boundary(arena, solved, *expr)?;
                    Stmt::Expr(force_emitted_expr_if_thunk(actual.as_ref(), expr))
                }
                poly_expr::Stmt::Module(def, body) => {
                    let mut module_defs = Vec::new();
                    let body = self.emit_stmts(arena, solved, body, &mut module_defs)?;
                    for def in module_defs {
                        self.pop_local_def(def);
                    }
                    Stmt::Module(convert_def(*def), body)
                }
            });
        }
        Ok(out)
    }

    pub(super) fn push_local_def(&mut self, def: poly_expr::DefId) {
        let depth = self.local_defs.entry(def).or_insert(0);
        *depth += 1;
    }

    pub(super) fn pop_local_def(&mut self, def: poly_expr::DefId) {
        let Some(depth) = self.local_defs.get_mut(&def) else {
            return;
        };
        *depth -= 1;
        if *depth == 0 {
            self.local_defs.remove(&def);
        }
    }

    pub(super) fn emit_record_spread(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
    ) -> Result<RecordSpread<Box<Expr>>, SpecializeError> {
        match spread {
            poly_expr::RecordSpread::Head(expr) => Ok(RecordSpread::Head(Box::new(
                self.emit_expr(arena, solved, *expr)?,
            ))),
            poly_expr::RecordSpread::Tail(expr) => Ok(RecordSpread::Tail(Box::new(
                self.emit_expr(arena, solved, *expr)?,
            ))),
            poly_expr::RecordSpread::None => Ok(RecordSpread::None),
        }
    }

    pub(super) fn emit_lambda_body(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        lambda: poly_expr::ExprId,
        body: poly_expr::ExprId,
    ) -> Result<Expr, SpecializeError> {
        let expr = self.emit_expr_typed(arena, solved, body)?;
        let Some(expected) = solved
            .actual_type_of(lambda)
            .and_then(runtime_function_return_type)
        else {
            return Ok(expr.expr);
        };
        let Some(actual) = solved.actual_type_of(body) else {
            return Ok(expr.expr);
        };
        Ok(self
            .boundary_emitted_expr(arena, actual, &expected, expr)?
            .expr)
    }

    pub(super) fn emit_catch_body(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        body: poly_expr::ExprId,
    ) -> Result<Expr, SpecializeError> {
        let expr = self.emit_expr_typed(arena, solved, body)?;
        Ok(force_emitted_expr_if_thunk(
            solved.actual_type_of(body),
            expr,
        ))
    }

    pub(super) fn lift_raw_expr_to_computation(
        &mut self,
        arena: &poly_expr::Arena,
        actual: Option<&Type>,
        emitted: EmittedExpr,
    ) -> Result<EmittedExpr, SpecializeError> {
        let Some(actual) = actual else {
            return Ok(emitted);
        };
        let target = ComputationShape::from_runtime_type(actual);
        let Some(current) = emitted.computation.clone() else {
            return Ok(emitted);
        };
        if equivalent_boundary_types(&current.value, &target.value) {
            return Ok(EmittedExpr {
                computation: Some(target),
                ..emitted
            });
        }
        if matches!(current.value, Type::Thunk { .. }) {
            return Ok(force_emitted_value_thunk(emitted, target));
        }
        self.coerce_emitted_value(arena, emitted, &target.value, Some(target.effect))
    }

    pub(super) fn wrap_expr_boundary(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
        mono: EmittedExpr,
    ) -> Result<EmittedExpr, SpecializeError> {
        self.wrap_expr_boundary_with_argument_contract(
            arena,
            solved,
            expr,
            mono,
            expr_argument_effect_contract(arena, expr),
        )
    }

    fn wrap_expr_boundary_with_argument_contract(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
        mono: EmittedExpr,
        argument_effect_contract: Option<&poly_expr::ArgEffectContract>,
    ) -> Result<EmittedExpr, SpecializeError> {
        let Some(actual) = solved.actual_type_of(expr) else {
            return Ok(mono);
        };
        let Some(consumer) = solved.consumer_type_of(expr) else {
            return Ok(mono);
        };
        if matches!(consumer, Type::Any) {
            return Ok(mono);
        }
        self.boundary_emitted_expr_with_argument_contract(
            arena,
            actual,
            consumer,
            mono,
            argument_effect_contract,
        )
    }

    pub(super) fn boundary_emitted_expr(
        &mut self,
        arena: &poly_expr::Arena,
        actual: &Type,
        expected: &Type,
        emitted: EmittedExpr,
    ) -> Result<EmittedExpr, SpecializeError> {
        self.boundary_emitted_expr_with_argument_contract(arena, actual, expected, emitted, None)
    }

    fn boundary_emitted_expr_with_argument_contract(
        &mut self,
        arena: &poly_expr::Arena,
        actual: &Type,
        expected: &Type,
        emitted: EmittedExpr,
        argument_effect_contract: Option<&poly_expr::ArgEffectContract>,
    ) -> Result<EmittedExpr, SpecializeError> {
        if matches!(expected, Type::Any) {
            return Ok(emitted);
        }
        let Some(shape) = emitted.computation.clone() else {
            return Ok(EmittedExpr::pure(
                self.boundary_expr_with_argument_contract(
                    arena,
                    actual,
                    expected,
                    emitted.expr,
                    argument_effect_contract,
                )?,
                Some(expected.clone()),
            ));
        };
        if let Type::Thunk { effect, value } = expected {
            if shape.effect.is_pure_effect() && equivalent_boundary_types(&shape.value, expected) {
                return Ok(emitted);
            }
            let body = self.ensure_emitted_value_with_argument_contract(
                arena,
                emitted,
                actual,
                value,
                argument_effect_contract,
            )?;
            return Ok(make_thunk_from_computation(
                body,
                effect.as_ref().clone(),
                value.as_ref().clone(),
            ));
        }
        self.ensure_emitted_value_with_argument_contract(
            arena,
            emitted,
            actual,
            expected,
            argument_effect_contract,
        )
    }

    fn ensure_emitted_value_with_argument_contract(
        &mut self,
        arena: &poly_expr::Arena,
        emitted: EmittedExpr,
        actual: &Type,
        expected: &Type,
        argument_effect_contract: Option<&poly_expr::ArgEffectContract>,
    ) -> Result<EmittedExpr, SpecializeError> {
        let Some(shape) = emitted.computation.clone() else {
            return Ok(EmittedExpr::pure(
                self.boundary_expr_with_argument_contract(
                    arena,
                    actual,
                    expected,
                    emitted.expr,
                    argument_effect_contract,
                )?,
                Some(expected.clone()),
            ));
        };
        if equivalent_boundary_types(&shape.value, expected)
            && !requires_function_contract_boundary(
                &shape.value,
                expected,
                argument_effect_contract,
            )
        {
            return Ok(EmittedExpr {
                computation: Some(ComputationShape {
                    effect: shape.effect,
                    value: expected.clone(),
                }),
                ..emitted
            });
        }
        if same_record_boundary_shape(&shape.value, expected) {
            return Ok(EmittedExpr {
                computation: Some(ComputationShape {
                    effect: shape.effect,
                    value: expected.clone(),
                }),
                ..emitted
            });
        }
        if matches!(shape.value, Type::Thunk { .. }) {
            let target = forced_value_shape(actual, &shape, expected);
            let forced = force_emitted_value_thunk(emitted, target);
            let Some(forced_shape) = forced.computation.clone() else {
                return Ok(forced);
            };
            if equivalent_boundary_types(&forced_shape.value, expected) {
                return Ok(forced);
            }
            return self.coerce_emitted_value_with_argument_contract(
                arena,
                forced,
                expected,
                None,
                argument_effect_contract,
            );
        }
        self.coerce_emitted_value_with_argument_contract(
            arena,
            emitted,
            expected,
            None,
            argument_effect_contract,
        )
    }

    pub(super) fn coerce_emitted_value(
        &mut self,
        arena: &poly_expr::Arena,
        emitted: EmittedExpr,
        expected: &Type,
        effect: Option<Type>,
    ) -> Result<EmittedExpr, SpecializeError> {
        self.coerce_emitted_value_with_argument_contract(arena, emitted, expected, effect, None)
    }

    fn coerce_emitted_value_with_argument_contract(
        &mut self,
        arena: &poly_expr::Arena,
        emitted: EmittedExpr,
        expected: &Type,
        effect: Option<Type>,
        argument_effect_contract: Option<&poly_expr::ArgEffectContract>,
    ) -> Result<EmittedExpr, SpecializeError> {
        let Some(shape) = emitted.computation.clone() else {
            return Ok(EmittedExpr::pure(emitted.expr, Some(expected.clone())));
        };
        if equivalent_boundary_types(&shape.value, expected)
            && !requires_function_contract_boundary(
                &shape.value,
                expected,
                argument_effect_contract,
            )
        {
            return Ok(EmittedExpr {
                computation: Some(ComputationShape {
                    effect: effect.unwrap_or(shape.effect),
                    value: expected.clone(),
                }),
                ..emitted
            });
        }
        let expr = self.boundary_expr_with_argument_contract(
            arena,
            &shape.value,
            expected,
            emitted.expr,
            argument_effect_contract,
        )?;
        Ok(EmittedExpr {
            expr,
            computation: Some(ComputationShape {
                effect: effect.unwrap_or(shape.effect),
                value: expected.clone(),
            }),
        })
    }

    fn boundary_expr_with_argument_contract(
        &mut self,
        arena: &poly_expr::Arena,
        actual: &Type,
        expected: &Type,
        expr: Expr,
        argument_effect_contract: Option<&poly_expr::ArgEffectContract>,
    ) -> Result<Expr, SpecializeError> {
        let actual = close_runtime_type_surface(
            erase_negative_only_open_vars(actual.clone()),
            TypeSlotKind::Value,
        );
        let expected = close_runtime_type_surface(
            erase_negative_only_open_vars(expected.clone()),
            TypeSlotKind::Value,
        );
        if let Some(instance) = self.cast_boundary_instance(arena, &actual, &expected)? {
            return Ok(Expr::new(ExprKind::Apply(
                Box::new(Expr::new(ExprKind::InstanceRef(instance))),
                Box::new(expr),
            )));
        }
        Ok(boundary_expr_with_argument_contract(
            &actual,
            &expected,
            expr,
            argument_effect_contract,
        ))
    }

    pub(super) fn cast_boundary_instance(
        &mut self,
        arena: &poly_expr::Arena,
        actual: &Type,
        expected: &Type,
    ) -> Result<Option<InstanceId>, SpecializeError> {
        let Some(def) = direct_cast_rule(arena, actual, expected).map(|rule| rule.def) else {
            return Ok(None);
        };
        let signature = types::pure_function_type(actual.clone(), expected.clone());
        self.ensure_def_instance(arena, def, signature).map(Some)
    }
}

fn expr_argument_effect_contract(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
) -> Option<&poly_expr::ArgEffectContract> {
    match arena.expr(expr) {
        poly_expr::Expr::Lambda(param, _) => lambda_param_effect_contract(arena, *param),
        poly_expr::Expr::Var(ref_id) => arena
            .ref_target(*ref_id)
            .and_then(|def| def_argument_effect_contract(arena, def)),
        _ => None,
    }
}

fn callee_argument_effect_contract(
    arena: &poly_expr::Arena,
    callee: poly_expr::ExprId,
) -> Option<&poly_expr::ArgEffectContract> {
    let (head, index) = call_spine_head_and_arg_index(arena, callee);
    match arena.expr(head) {
        poly_expr::Expr::Var(ref_id) => arena
            .ref_target(*ref_id)
            .and_then(|def| def_lambda_param_effect_contract(arena, def, index)),
        poly_expr::Expr::Lambda(param, body) => {
            lambda_chain_param_effect_contract(arena, *param, *body, index)
        }
        _ => None,
    }
}

fn requires_function_contract_boundary(
    actual: &Type,
    expected: &Type,
    argument_effect_contract: Option<&poly_expr::ArgEffectContract>,
) -> bool {
    argument_effect_contract.is_some() && function_boundary_types(actual, expected)
}

fn call_spine_head_and_arg_index(
    arena: &poly_expr::Arena,
    mut callee: poly_expr::ExprId,
) -> (poly_expr::ExprId, usize) {
    let mut index = 0;
    while let poly_expr::Expr::App(next, _) = arena.expr(callee) {
        index += 1;
        callee = *next;
    }
    (callee, index)
}

fn def_argument_effect_contract(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
) -> Option<&poly_expr::ArgEffectContract> {
    def_lambda_param_effect_contract(arena, def, 0)
}

fn def_lambda_param_effect_contract(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    index: usize,
) -> Option<&poly_expr::ArgEffectContract> {
    let Some(poly_expr::Def::Let {
        body: Some(body), ..
    }) = arena.defs.get(def)
    else {
        return None;
    };
    let poly_expr::Expr::Lambda(param, next) = arena.expr(*body) else {
        return None;
    };
    lambda_chain_param_effect_contract(arena, *param, *next, index)
}

fn lambda_chain_param_effect_contract(
    arena: &poly_expr::Arena,
    param: poly_expr::PatId,
    body: poly_expr::ExprId,
    index: usize,
) -> Option<&poly_expr::ArgEffectContract> {
    if index == 0 {
        return lambda_param_effect_contract(arena, param);
    }
    let poly_expr::Expr::Lambda(param, body) = arena.expr(body) else {
        return None;
    };
    lambda_chain_param_effect_contract(arena, *param, *body, index - 1)
}

fn lambda_param_effect_contract(
    arena: &poly_expr::Arena,
    pat: poly_expr::PatId,
) -> Option<&poly_expr::ArgEffectContract> {
    let Some(def) = lambda_param_def(arena, pat) else {
        return None;
    };
    arena.arg_effect_contracts.get(&def)
}

fn lambda_param_def(arena: &poly_expr::Arena, pat: poly_expr::PatId) -> Option<poly_expr::DefId> {
    match arena.pat(pat) {
        poly_expr::Pat::Var(def) | poly_expr::Pat::As(_, def) => Some(*def),
        _ => None,
    }
}
