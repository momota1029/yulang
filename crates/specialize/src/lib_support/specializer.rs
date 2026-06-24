use super::{boundary::*, convert::*, debug::*, pattern_defs::*, *};

impl Specializer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn specialize(self, arena: &poly_expr::Arena) -> Result<Program, SpecializeError> {
        self.specialize_root_exprs(arena)
    }

    pub fn specialize_root_exprs(
        mut self,
        arena: &poly_expr::Arena,
    ) -> Result<Program, SpecializeError> {
        let roots = arena
            .runtime_roots
            .iter()
            .map(|root| self.runtime_root(arena, *root))
            .collect::<Result<Vec<_>, _>>()?;
        let instances = self.finish_instances()?;
        Ok(Program { roots, instances })
    }

    pub fn specialize_roots(
        mut self,
        arena: &poly_expr::Arena,
        roots: impl IntoIterator<Item = poly_expr::DefId>,
    ) -> Result<Program, SpecializeError> {
        let roots = roots
            .into_iter()
            .map(|def| self.ensure_def_instance(arena, def, None))
            .map(|instance| instance.map(Root::Instance))
            .collect::<Result<Vec<_>, _>>()?;
        let instances = self.finish_instances()?;
        Ok(Program { roots, instances })
    }

    fn finish_instances(self) -> Result<Vec<Instance>, SpecializeError> {
        self.instances
            .into_iter()
            .enumerate()
            .map(|(index, instance)| {
                instance.ok_or(SpecializeError::InternalMissingInstance {
                    instance: InstanceId(index as u32),
                })
            })
            .collect::<Result<Vec<_>, _>>()
    }

    fn runtime_root(
        &mut self,
        arena: &poly_expr::Arena,
        root: poly_expr::RuntimeRoot,
    ) -> Result<Root, SpecializeError> {
        match root {
            poly_expr::RuntimeRoot::Expr(expr) => {
                let expected = self.root_expr_expected_type(arena, expr)?;
                let plan = solve::solve_expr(arena, expr, expected.as_ref())?;
                let expr_id = expr;
                let expr = self.expr(arena, &plan, expr_id)?;
                Ok(Root::Expr(force_expr_if_thunk(
                    implicit_force_type(&plan, expr_id),
                    expr,
                )))
            }
            poly_expr::RuntimeRoot::ComputedDef(def) => Ok(Root::EvalInstance(
                self.ensure_def_instance(arena, def, None)?,
            )),
        }
    }

    fn root_expr_expected_type(
        &self,
        arena: &poly_expr::Arena,
        expr: poly_expr::ExprId,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(def) = arena.root_expr_def(expr) else {
            return Ok(None);
        };
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = arena.defs.get(def)
        else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            });
        };
        Ok(Some(
            types::signature_for_scheme(arena, def, scheme, None)?.ty,
        ))
    }

    fn ensure_def_instance(
        &mut self,
        arena: &poly_expr::Arena,
        def: poly_expr::DefId,
        expected: Option<&Type>,
    ) -> Result<InstanceId, SpecializeError> {
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
        let Some(scheme) = scheme else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            });
        };
        let signature = types::signature_for_scheme(arena, def, scheme, expected)?;
        let wraps_stack_handler = !scheme.stack_quantifiers.is_empty();
        let key = InstanceKey {
            def,
            ty: signature.ty.clone(),
        };
        if let Some(instance) = self.instance_by_key.get(&key).copied() {
            return Ok(instance);
        }
        let Some(body) = *body else {
            return Err(SpecializeError::MissingBody {
                def: convert_def(def),
            });
        };

        let id = InstanceId(self.instances.len() as u32);
        self.instance_by_key.insert(key, id);
        self.instances.push(None);
        self.active_instance_signatures
            .insert(id, signature.ty.clone());

        let plan = solve::solve_def_expr(arena, def, body, &signature.ty)?;
        let body = self.expr(arena, &plan, body)?;
        let body = if wraps_stack_handler {
            wrap_stack_handler_marker(&signature.ty, body)
        } else {
            body
        };
        self.instances[id.0 as usize] = Some(Instance {
            id,
            source: InstanceSource::Def(convert_def(def)),
            signature,
            body,
        });
        self.active_instance_signatures.remove(&id);
        Ok(id)
    }

    fn expr(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        expr: poly_expr::ExprId,
    ) -> Result<Expr, SpecializeError> {
        self.expr_with_boundary(arena, plan, expr, true)
    }

    fn expr_without_boundary(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        expr: poly_expr::ExprId,
    ) -> Result<Expr, SpecializeError> {
        self.expr_with_boundary(arena, plan, expr, false)
    }

    fn expr_with_boundary(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        expr: poly_expr::ExprId,
        wrap_boundary: bool,
    ) -> Result<Expr, SpecializeError> {
        use poly_expr::Expr as PolyExpr;
        let expr_id = expr;
        let is_raw_thunk_computation = matches!(arena.expr(expr_id), PolyExpr::Catch(_, _))
            || plan.is_raw_thunk_computation(expr_id);
        let kind = match arena.expr(expr_id) {
            PolyExpr::Lit(lit) => ExprKind::Lit(convert_lit(lit)),
            PolyExpr::PrimitiveOp(op) => ExprKind::PrimitiveOp {
                op: convert_primitive_op(*op),
                context: primitive_context(arena, *op, plan.actual_type_of(expr_id)),
            },
            PolyExpr::Var(ref_id) => self.var(arena, *ref_id, var_instance_type(plan, expr_id))?,
            PolyExpr::App(callee, arg) => ExprKind::Apply(
                Box::new(self.expr(arena, plan, *callee)?),
                Box::new(self.expr(arena, plan, *arg)?),
            ),
            PolyExpr::RefSet(reference, value) => ExprKind::RefSet(
                Box::new(self.expr(arena, plan, *reference)?),
                Box::new(self.expr(arena, plan, *value)?),
            ),
            PolyExpr::Lambda(param, body) => ExprKind::Lambda(
                self.pat(arena, plan, *param)?,
                Box::new(self.expr(arena, plan, *body)?),
            ),
            PolyExpr::Tuple(items) => ExprKind::Tuple(self.exprs(arena, plan, items)?),
            PolyExpr::Record { fields, spread } => ExprKind::Record {
                fields: fields
                    .iter()
                    .map(|(name, value)| {
                        Ok(RecordField {
                            name: name.clone(),
                            value: self.expr(arena, plan, *value)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                spread: self.expr_spread(arena, plan, spread)?,
            },
            PolyExpr::PolyVariant(tag, payloads) => ExprKind::PolyVariant {
                tag: tag.clone(),
                payloads: self.exprs(arena, plan, payloads)?,
            },
            PolyExpr::Select(base, select) => {
                let select = arena.select(*select);
                ExprKind::Select {
                    base: Box::new(self.expr(arena, plan, *base)?),
                    name: select.name.clone(),
                    resolution: self.select_resolution(
                        arena,
                        plan,
                        *base,
                        expr_id,
                        select.resolution,
                    )?,
                }
            }
            PolyExpr::Case(scrutinee, arms) => ExprKind::Case {
                scrutinee: Box::new(self.expr(arena, plan, *scrutinee)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CaseArm {
                            pat: self.pat(arena, plan, arm.pat)?,
                            guard: self.optional_expr(arena, plan, arm.guard)?,
                            body: self.expr(arena, plan, arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            },
            PolyExpr::Catch(body, arms) => ExprKind::Catch {
                body: Box::new(self.expr(arena, plan, *body)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CatchArm {
                            operation_path: arm
                                .operation
                                .as_ref()
                                .map(|operation| operation.path.clone()),
                            pat: self.pat(arena, plan, arm.pat)?,
                            continuation: self.optional_pat(arena, plan, arm.continuation)?,
                            guard: self.optional_expr(arena, plan, arm.guard)?,
                            body: self.expr(arena, plan, arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            },
            PolyExpr::Block(stmts, tail) => ExprKind::Block(self.block(arena, plan, stmts, *tail)?),
        };
        let mono_expr = Expr::new(kind);
        let mono_expr = if is_raw_thunk_computation {
            wrap_raw_thunk_computation(plan.actual_type_of(expr_id), mono_expr)
        } else {
            mono_expr
        };
        if wrap_boundary {
            self.wrap_boundary(arena, expr_id, mono_expr, plan)
        } else {
            Ok(mono_expr)
        }
    }

    fn wrap_boundary(
        &mut self,
        arena: &poly_expr::Arena,
        expr_id: poly_expr::ExprId,
        expr: Expr,
        plan: &solve::ExprTypePlan,
    ) -> Result<Expr, SpecializeError> {
        let Some(boundary) = plan.boundary(expr_id) else {
            return Ok(expr);
        };
        if equivalent_boundary_types(boundary.actual, boundary.expected) {
            return Ok(expr);
        }
        if function_boundary_types(boundary.actual, boundary.expected) {
            let argument_effect_contract = self.expr_argument_effect_contract(arena, expr_id);
            let hygiene = hygiene::function_adapter_hygiene_with_argument_contract(
                boundary.actual,
                boundary.expected,
                argument_effect_contract,
            );
            return Ok(boundary_expr_with_hygiene(
                boundary.actual,
                boundary.expected,
                expr,
                hygiene,
            ));
        }
        Ok(boundary_expr(boundary.actual, boundary.expected, expr))
    }

    fn expr_argument_effect_contract<'a>(
        &self,
        arena: &'a poly_expr::Arena,
        expr_id: poly_expr::ExprId,
    ) -> Option<&'a poly_expr::ArgEffectContract> {
        let poly_expr::Expr::Lambda(param, _) = arena.expr(expr_id) else {
            return None;
        };
        let Some(def) = lambda_param_def(arena, *param) else {
            return None;
        };
        arena.arg_effect_contracts.get(&def)
    }

    fn var(
        &mut self,
        arena: &poly_expr::Arena,
        ref_id: poly_expr::RefId,
        expected: Option<&Type>,
    ) -> Result<ExprKind, SpecializeError> {
        let Some(def) = arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if self.local_defs.contains(&def) {
            return Ok(ExprKind::Local(convert_def(def)));
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
            Some(poly_expr::Def::Let { body: Some(_), .. }) => self
                .instance_ref(arena, def, expected)
                .map(|expr| expr.kind),
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

    fn instance_ref(
        &mut self,
        arena: &poly_expr::Arena,
        def: poly_expr::DefId,
        expected: Option<&Type>,
    ) -> Result<Expr, SpecializeError> {
        let instance = self.ensure_def_instance(arena, def, expected)?;
        let expr = Expr::new(ExprKind::InstanceRef(instance));
        let Some(expected) = expected else {
            return Ok(expr);
        };
        let Some(actual) = self.instance_signature_type(instance) else {
            return Ok(expr);
        };
        if equivalent_boundary_types(actual, expected) {
            return Ok(expr);
        }
        if function_boundary_types(actual, expected) {
            let hygiene = hygiene::function_adapter_hygiene_with_argument_contract(
                actual,
                expected,
                def_argument_effect_contract(arena, def),
            );
            return Ok(boundary_expr_with_hygiene(actual, expected, expr, hygiene));
        }
        Ok(boundary_expr(actual, expected, expr))
    }

    fn instance_signature_type(&self, instance: InstanceId) -> Option<&Type> {
        self.instances
            .get(instance.0 as usize)
            .and_then(|instance| instance.as_ref())
            .map(|instance| &instance.signature.ty)
            .or_else(|| self.active_instance_signatures.get(&instance))
    }

    fn pat(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        pat: poly_expr::PatId,
    ) -> Result<Pat, SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match arena.pat(pat) {
            PolyPat::Wild => Ok(Pat::Wild),
            PolyPat::Lit(lit) => Ok(Pat::Lit(convert_lit(lit))),
            PolyPat::Tuple(items) => Ok(Pat::Tuple(self.pats(arena, plan, items)?)),
            PolyPat::List {
                prefix,
                spread,
                suffix,
            } => Ok(Pat::List {
                prefix: self.pats(arena, plan, prefix)?,
                spread: self.optional_pat(arena, plan, *spread)?.map(Box::new),
                suffix: self.pats(arena, plan, suffix)?,
            }),
            PolyPat::Record { fields, spread } => Ok(Pat::Record {
                fields: fields
                    .iter()
                    .map(|field| {
                        Ok(mono::RecordPatField {
                            name: field.name.clone(),
                            pat: self.pat(arena, plan, field.pat)?,
                            default: self.optional_expr(arena, plan, field.default)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                spread: convert_def_spread(spread),
            }),
            PolyPat::PolyVariant(tag, payloads) => Ok(Pat::PolyVariant(
                tag.clone(),
                self.pats(arena, plan, payloads)?,
            )),
            PolyPat::Con(ref_id, payloads) => {
                let Some(def) = arena.ref_target(*ref_id) else {
                    return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
                };
                Ok(Pat::Con(
                    convert_def(def),
                    self.pats(arena, plan, payloads)?,
                ))
            }
            PolyPat::Ref(ref_id) => Ok(Pat::Ref(self.ref_instance(arena, *ref_id)?)),
            PolyPat::Var(def) => Ok(Pat::Var(convert_def(*def))),
            PolyPat::Or(left, right) => Ok(Pat::Or(
                Box::new(self.pat(arena, plan, *left)?),
                Box::new(self.pat(arena, plan, *right)?),
            )),
            PolyPat::As(pat, def) => Ok(Pat::As(
                Box::new(self.pat(arena, plan, *pat)?),
                convert_def(*def),
            )),
        }
    }

    fn ref_instance(
        &mut self,
        arena: &poly_expr::Arena,
        ref_id: poly_expr::RefId,
    ) -> Result<InstanceId, SpecializeError> {
        let Some(def) = arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        self.ensure_def_instance(arena, def, None)
    }

    fn select_resolution(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        base: poly_expr::ExprId,
        select: poly_expr::ExprId,
        resolution: Option<poly_expr::SelectResolution>,
    ) -> Result<Option<SelectResolution>, SpecializeError> {
        match resolution {
            None => Ok(None),
            Some(poly_expr::SelectResolution::RecordField) => {
                Ok(Some(SelectResolution::RecordField))
            }
            Some(poly_expr::SelectResolution::Method { def }) => {
                if is_field_projection_method(arena, def) {
                    return Ok(Some(SelectResolution::RecordField));
                }
                let expected = method_instance_expected_type(plan, base, select);
                Ok(Some(SelectResolution::Method {
                    instance: self.ensure_def_instance(arena, def, expected.as_ref())?,
                }))
            }
            Some(poly_expr::SelectResolution::TypeclassMethod { member }) => {
                Ok(Some(SelectResolution::Method {
                    instance: self.typeclass_method_instance(arena, plan, base, select, member)?,
                }))
            }
        }
    }

    fn typeclass_method_instance(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        base: poly_expr::ExprId,
        select: poly_expr::ExprId,
        member: poly_expr::DefId,
    ) -> Result<InstanceId, SpecializeError> {
        let receiver =
            method_receiver_type(plan, base).ok_or(SpecializeError::MissingExprType {
                expr: base.0,
                role: ExprTypeRole::Actual,
            })?;
        let expected = method_instance_expected_type(plan, base, select);
        eprintln!(
            "typeclass method request member={member:?} base={} select={} receiver={receiver:?} expected={expected:?}",
            debug_expr_tree(arena, base, 2),
            debug_expr_tree(arena, select, 2)
        );
        let Some(poly_expr::Def::Let {
            body,
            scheme: Some(scheme),
            ..
        }) = arena.defs.get(member)
        else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(member),
            });
        };
        let predicates =
            types::role_predicates_for_scheme_signature(arena, member, scheme, expected.as_ref())?;
        let mut implementations = Vec::new();
        let mut matched_candidate_count = 0usize;
        for predicate in &predicates {
            let Some(input_types) = exact_role_input_types(predicate) else {
                continue;
            };
            for candidate in arena.role_impls.candidates(&predicate.role) {
                if roles::candidate_application(&arena.typ, predicate, candidate, &input_types)
                    .is_none()
                {
                    continue;
                }
                matched_candidate_count += 1;
                for method in &candidate.methods {
                    if method.requirement == member
                        && !implementations.contains(&method.implementation)
                    {
                        implementations.push(method.implementation);
                    }
                }
            }
        }

        match implementations.as_slice() {
            [implementation] => self.ensure_def_instance(arena, *implementation, expected.as_ref()),
            [] if body.is_some() && matched_candidate_count > 0 => {
                self.ensure_def_instance(arena, member, expected.as_ref())
            }
            [] => {
                eprintln!(
                    "typeclass method unresolved member={member:?} base={} select={} receiver={receiver:?}",
                    debug_expr_tree(arena, base, 3),
                    debug_expr_tree(arena, select, 3)
                );
                Err(SpecializeError::UnresolvedTypeclassMethod {
                    member: convert_def(member),
                    receiver,
                })
            }
            _ => {
                eprintln!(
                    "typeclass method ambiguous member={member:?} base={} select={} receiver={receiver:?} candidates={implementations:?}",
                    debug_expr_tree(arena, base, 3),
                    debug_expr_tree(arena, select, 3)
                );
                Err(SpecializeError::AmbiguousTypeclassMethod {
                    member: convert_def(member),
                    receiver,
                    candidates: implementations.into_iter().map(convert_def).collect(),
                })
            }
        }
    }

    fn exprs(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        exprs: &[poly_expr::ExprId],
    ) -> Result<Vec<Expr>, SpecializeError> {
        exprs
            .iter()
            .map(|expr| self.expr(arena, plan, *expr))
            .collect()
    }

    fn pats(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        pats: &[poly_expr::PatId],
    ) -> Result<Vec<Pat>, SpecializeError> {
        pats.iter().map(|pat| self.pat(arena, plan, *pat)).collect()
    }

    fn optional_expr(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        expr: Option<poly_expr::ExprId>,
    ) -> Result<Option<Expr>, SpecializeError> {
        expr.map(|expr| self.expr(arena, plan, expr)).transpose()
    }

    fn optional_pat(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        pat: Option<poly_expr::PatId>,
    ) -> Result<Option<Pat>, SpecializeError> {
        pat.map(|pat| self.pat(arena, plan, pat)).transpose()
    }

    fn block(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        stmts: &[poly_expr::Stmt],
        tail: Option<poly_expr::ExprId>,
    ) -> Result<Block, SpecializeError> {
        let mut scoped_defs = Vec::new();
        let stmts = self.stmts(arena, plan, stmts, &mut scoped_defs)?;
        let tail = self.optional_expr(arena, plan, tail)?.map(Box::new);
        for def in scoped_defs {
            self.local_defs.remove(&def);
        }
        Ok(Block { stmts, tail })
    }

    fn stmts(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
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
                        self.local_defs.insert(*def);
                    }
                    let value = self.expr(arena, plan, *value)?;
                    let pat_out = self.pat(arena, plan, *pat)?;
                    for def in defs {
                        scoped_defs.push(def);
                    }
                    Stmt::Let(convert_vis(*vis), pat_out, value)
                }
                poly_expr::Stmt::Expr(expr) => {
                    let discard_boundary = discards_unit_boundary(plan, *expr);
                    let actual = if discard_boundary {
                        plan.actual_type_of(*expr).cloned()
                    } else {
                        implicit_force_type(plan, *expr).cloned()
                    };
                    let expr = if discard_boundary {
                        self.expr_without_boundary(arena, plan, *expr)?
                    } else {
                        self.expr(arena, plan, *expr)?
                    };
                    Stmt::Expr(force_expr_if_thunk(actual.as_ref(), expr))
                }
                poly_expr::Stmt::Module(def, body) => {
                    let mut module_defs = Vec::new();
                    let body = self.stmts(arena, plan, body, &mut module_defs)?;
                    for def in module_defs {
                        self.local_defs.remove(&def);
                    }
                    Stmt::Module(convert_def(*def), body)
                }
            });
        }
        Ok(out)
    }

    fn expr_spread(
        &mut self,
        arena: &poly_expr::Arena,
        plan: &solve::ExprTypePlan,
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
    ) -> Result<RecordSpread<Box<Expr>>, SpecializeError> {
        match spread {
            poly_expr::RecordSpread::Head(expr) => {
                Ok(RecordSpread::Head(Box::new(self.expr(arena, plan, *expr)?)))
            }
            poly_expr::RecordSpread::Tail(expr) => {
                Ok(RecordSpread::Tail(Box::new(self.expr(arena, plan, *expr)?)))
            }
            poly_expr::RecordSpread::None => Ok(RecordSpread::None),
        }
    }
}

fn lambda_param_def(arena: &poly_expr::Arena, pat: poly_expr::PatId) -> Option<poly_expr::DefId> {
    match arena.pat(pat) {
        poly_expr::Pat::Var(def) | poly_expr::Pat::As(_, def) => Some(*def),
        _ => None,
    }
}

fn def_argument_effect_contract(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
) -> Option<&poly_expr::ArgEffectContract> {
    let Some(poly_expr::Def::Let {
        body: Some(body), ..
    }) = arena.defs.get(def)
    else {
        return None;
    };
    let poly_expr::Expr::Lambda(param, _) = arena.expr(*body) else {
        return None;
    };
    let Some(def) = lambda_param_def(arena, *param) else {
        return None;
    };
    arena.arg_effect_contracts.get(&def)
}
