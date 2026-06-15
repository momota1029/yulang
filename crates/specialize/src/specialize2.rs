//! mono 用 simple-sub 推論をもう一度走らせる `specialize2` の入口。
//!
//! 既存 `solve` は expression へ expected type を手渡す形に寄っている。ここでは task-local な
//! type variable と subtype 制約から concrete annotation を作り、その結果から次の mono demand を
//! 再帰的に展開する。

use std::collections::{HashMap, HashSet, VecDeque};

use mono::{
    Block, CaseArm, CatchArm, ComputationType, EffectFamilies, EffectFamily, EffectiveThunkType,
    Expr, ExprKind, Instance, InstanceId, InstanceSource, Pat, Program, RecordField, RecordSpread,
    Root, SelectResolution, Signature, StackWeight, StackWeightEntry, Stmt, Type, TypeField,
    TypeVariant,
};
use poly::expr as poly_expr;

use crate::{
    ExprTypeRole, SpecializeError, convert_def, convert_def_spread, convert_lit,
    convert_primitive_op, convert_vis, def_kind, equivalent_boundary_types, hygiene, lit_type,
    primitive_context, roles, std_types, types,
};

pub(crate) fn specialize(arena: &poly_expr::Arena) -> Result<Program, SpecializeError> {
    Specializer2::new().specialize(arena)
}

#[derive(Default)]
struct Specializer2 {
    instances: Vec<Option<Instance>>,
    instance_by_key: HashMap<InstanceKey, InstanceId>,
    active_instance_signatures: HashMap<InstanceId, Type>,
    local_defs: HashMap<poly_expr::DefId, usize>,
}

impl Specializer2 {
    fn new() -> Self {
        Self::default()
    }

    fn specialize(mut self, arena: &poly_expr::Arena) -> Result<Program, SpecializeError> {
        let mut roots = Vec::new();
        for root in &arena.runtime_roots {
            roots.push(match root {
                poly_expr::RuntimeRoot::Expr(expr) => {
                    let expr_id = *expr;
                    let solved = TaskSolver::solve_root_expr(arena, expr_id)?;
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
        Ok(program)
    }

    fn ensure_computed_def_instance(
        &mut self,
        arena: &poly_expr::Arena,
        def: poly_expr::DefId,
    ) -> Result<InstanceId, SpecializeError> {
        let body = let_body(arena, def)?;
        let signature = TaskSolver::solve_computed_def_signature(arena, def, body)?;
        self.ensure_def_instance(arena, def, signature)
    }

    fn ensure_def_instance(
        &mut self,
        arena: &poly_expr::Arena,
        def: poly_expr::DefId,
        signature_ty: Type,
    ) -> Result<InstanceId, SpecializeError> {
        let inference_signature_ty = signature_ty;
        let runtime_signature_ty =
            close_resolved_runtime_surface(inference_signature_ty.clone(), TypeSlotKind::Value);
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
        let mut body = self.emit_expr(arena, &solved, body)?;
        body = wrap_stack_handler_marker(&runtime_signature_ty, body);
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

    fn emit_expr(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
    ) -> Result<Expr, SpecializeError> {
        Ok(self.emit_expr_typed(arena, solved, expr)?.expr)
    }

    fn emit_expr_typed(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
    ) -> Result<EmittedExpr, SpecializeError> {
        self.emit_expr_with_boundary(arena, solved, expr, true)
    }

    fn emit_expr_without_boundary(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: poly_expr::ExprId,
    ) -> Result<EmittedExpr, SpecializeError> {
        self.emit_expr_with_boundary(arena, solved, expr, false)
    }

    fn emit_expr_with_boundary(
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
            PolyExpr::App(callee, arg) => ExprKind::Apply(
                Box::new(self.emit_expr(arena, solved, *callee)?),
                Box::new(self.emit_expr(arena, solved, *arg)?),
            ),
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
            expr_out = lift_raw_expr_to_computation(solved.actual_type_of(expr), expr_out);
        }
        if wrap_boundary {
            solved.wrap_expr_boundary(expr, expr_out)
        } else {
            Ok(expr_out)
        }
    }

    fn emit_var(
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

    fn emit_select_resolution(
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

    fn emit_pat(
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

    fn emit_exprs(
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

    fn emit_pats(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        pats: &[poly_expr::PatId],
    ) -> Result<Vec<Pat>, SpecializeError> {
        pats.iter()
            .map(|pat| self.emit_pat(arena, solved, *pat))
            .collect()
    }

    fn emit_optional_expr(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        expr: Option<poly_expr::ExprId>,
    ) -> Result<Option<Expr>, SpecializeError> {
        expr.map(|expr| self.emit_expr(arena, solved, expr))
            .transpose()
    }

    fn emit_optional_pat(
        &mut self,
        arena: &poly_expr::Arena,
        solved: &SolvedTask,
        pat: Option<poly_expr::PatId>,
    ) -> Result<Option<Pat>, SpecializeError> {
        pat.map(|pat| self.emit_pat(arena, solved, pat)).transpose()
    }

    fn emit_block(
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

    fn emit_stmts(
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

    fn push_local_def(&mut self, def: poly_expr::DefId) {
        let depth = self.local_defs.entry(def).or_insert(0);
        *depth += 1;
    }

    fn pop_local_def(&mut self, def: poly_expr::DefId) {
        let Some(depth) = self.local_defs.get_mut(&def) else {
            return;
        };
        *depth -= 1;
        if *depth == 0 {
            self.local_defs.remove(&def);
        }
    }

    fn emit_record_spread(
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

    fn emit_lambda_body(
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
        Ok(boundary_emitted_expr(actual, expected, expr).expr)
    }

    fn emit_catch_body(
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstanceKey {
    def: poly_expr::DefId,
    ty: Type,
}

#[derive(Debug, Clone)]
struct EmittedExpr {
    expr: Expr,
    computation: Option<ComputationShape>,
}

impl EmittedExpr {
    fn pure(expr: Expr, value: Option<Type>) -> Self {
        Self {
            expr,
            computation: value.map(ComputationShape::pure),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ComputationShape {
    effect: Type,
    value: Type,
}

impl ComputationShape {
    fn pure(value: Type) -> Self {
        Self {
            effect: Type::pure_effect(),
            value,
        }
    }

    fn from_runtime_type(ty: &Type) -> Self {
        match ty {
            Type::Thunk { effect, value } => Self {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            value => Self::pure(value.clone()),
        }
    }
}

struct SolvedTask {
    exprs: HashMap<poly_expr::ExprId, SolvedExprType>,
    ref_signatures: HashMap<poly_expr::ExprId, Type>,
    select_signatures: HashMap<poly_expr::ExprId, Type>,
    typeclass_resolutions: HashMap<poly_expr::ExprId, TypeclassResolution>,
    pat_ref_signatures: HashMap<poly_expr::PatId, Type>,
    raw_thunk_computations: HashSet<poly_expr::ExprId>,
}

impl SolvedTask {
    fn actual_type_of(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.exprs.get(&expr).map(|ty| &ty.actual)
    }

    fn consumer_type_of(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.exprs.get(&expr).and_then(|ty| ty.consumer.as_ref())
    }

    fn emitted_type_of(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.consumer_type_of(expr)
            .or_else(|| self.actual_type_of(expr))
    }

    fn ref_signature(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.ref_signatures.get(&expr)
    }

    fn select_signature(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.select_signatures.get(&expr)
    }

    fn typeclass_resolution(&self, expr: poly_expr::ExprId) -> Option<&TypeclassResolution> {
        self.typeclass_resolutions.get(&expr)
    }

    fn pat_ref_signature(&self, pat: poly_expr::PatId) -> Option<&Type> {
        self.pat_ref_signatures.get(&pat)
    }

    fn is_raw_thunk_computation(&self, expr: poly_expr::ExprId) -> bool {
        self.raw_thunk_computations.contains(&expr)
    }

    fn wrap_expr_boundary(
        &self,
        expr: poly_expr::ExprId,
        mono: EmittedExpr,
    ) -> Result<EmittedExpr, SpecializeError> {
        let Some(actual) = self.actual_type_of(expr) else {
            return Ok(mono);
        };
        let Some(consumer) = self.consumer_type_of(expr) else {
            return Ok(mono);
        };
        if matches!(consumer, Type::Any) {
            return Ok(mono);
        }
        Ok(boundary_emitted_expr(actual, consumer, mono))
    }
}

#[derive(Debug, Clone)]
struct SolvedExprType {
    actual: Type,
    consumer: Option<Type>,
}

#[derive(Debug, Clone)]
struct TypeclassResolution {
    implementation: poly_expr::DefId,
    signature: Type,
}

struct TaskSolver<'a> {
    arena: &'a poly_expr::Arena,
    graph: TypeGraph<'a>,
    exprs: HashMap<poly_expr::ExprId, ExprType>,
    locals: HashMap<poly_expr::DefId, Type>,
    discarded_exprs: HashSet<poly_expr::ExprId>,
    ref_uses: Vec<RefUse>,
    select_uses: Vec<SelectUse>,
    typeclass_uses: Vec<TypeclassUse>,
    pat_ref_uses: Vec<PatRefUse>,
    required_exprs: HashSet<poly_expr::ExprId>,
    raw_thunk_computations: HashSet<poly_expr::ExprId>,
}

impl<'a> TaskSolver<'a> {
    fn solve_root_expr(
        arena: &'a poly_expr::Arena,
        expr: poly_expr::ExprId,
    ) -> Result<SolvedTask, SpecializeError> {
        let mut solver = Self::new(arena);
        solver.required_exprs.insert(expr);
        solver.expr(expr)?;
        solver.finish()
    }

    fn solve_def_body(
        arena: &'a poly_expr::Arena,
        _def: poly_expr::DefId,
        body: poly_expr::ExprId,
        signature: Type,
    ) -> Result<SolvedTask, SpecializeError> {
        let mut solver = Self::new(arena);
        solver.required_exprs.insert(body);
        let actual = solver.expr(body)?;
        solver.consume_expr(body, signature.clone())?;
        solver.graph.constrain_exact(actual, signature)?;
        solver.finish()
    }

    fn solve_computed_def_signature(
        arena: &'a poly_expr::Arena,
        def: poly_expr::DefId,
        body: poly_expr::ExprId,
    ) -> Result<Type, SpecializeError> {
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = arena.defs.get(def)
        else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            });
        };
        let mut solver = Self::new(arena);
        solver.required_exprs.insert(body);
        let signature = solver.instantiate_scheme(def, scheme)?;
        let actual = solver.expr(body)?;
        solver.consume_expr(body, signature.clone())?;
        solver.graph.constrain_exact(actual, signature.clone())?;
        let solved = solver.finish()?;
        let actual =
            solved
                .actual_type_of(body)
                .cloned()
                .ok_or(SpecializeError::MissingExprType {
                    expr: body.0,
                    role: ExprTypeRole::Actual,
                })?;
        Ok(forced_computation_value_type(actual))
    }

    fn new(arena: &'a poly_expr::Arena) -> Self {
        Self {
            arena,
            graph: TypeGraph::new(arena),
            exprs: HashMap::new(),
            locals: HashMap::new(),
            discarded_exprs: HashSet::new(),
            ref_uses: Vec::new(),
            select_uses: Vec::new(),
            typeclass_uses: Vec::new(),
            pat_ref_uses: Vec::new(),
            required_exprs: HashSet::new(),
            raw_thunk_computations: HashSet::new(),
        }
    }

    fn expr(&mut self, expr: poly_expr::ExprId) -> Result<Type, SpecializeError> {
        if let Some(ty) = self.exprs.get(&expr) {
            return Ok(ty.actual.clone());
        }
        let ty = self.infer_expr(expr)?;
        self.exprs.entry(expr).or_insert_with(|| ExprType {
            actual: ty.clone(),
            consumer: None,
        });
        Ok(ty)
    }

    fn consume_expr(
        &mut self,
        expr: poly_expr::ExprId,
        consumer: Type,
    ) -> Result<(), SpecializeError> {
        let actual = self.expr(expr)?;
        self.add_expr_consumer(expr, actual.clone(), consumer.clone());
        self.graph.constrain_subtype(actual, consumer)
    }

    fn consume_expr_value(
        &mut self,
        expr: poly_expr::ExprId,
        consumer: Type,
    ) -> Result<(Type, Type), SpecializeError> {
        let actual = self.expr(expr)?;
        self.add_expr_consumer(expr, actual.clone(), consumer.clone());
        let (actual_value, actual_effect) = split_runtime_computation_shape(actual);
        self.graph
            .constrain_subtype(actual_value.clone(), consumer)?;
        Ok((actual_value, actual_effect))
    }

    fn consume_expr_computation(
        &mut self,
        expr: poly_expr::ExprId,
        effect: Type,
        value: Type,
    ) -> Result<Type, SpecializeError> {
        let actual = self.expr(expr)?;
        let (actual_value, actual_effect) = split_runtime_computation_shape(actual.clone());
        let consumer_effect = self
            .graph
            .constrain_consumed_computation_effect(actual_effect.clone(), effect)?;
        let consumer = types::runtime_shape(consumer_effect.clone(), value.clone());
        self.add_expr_consumer(expr, actual.clone(), consumer);
        self.graph.constrain_subtype(actual_value, value)?;
        Ok(consumer_effect)
    }

    fn add_expr_consumer(&mut self, expr: poly_expr::ExprId, actual: Type, consumer: Type) {
        let info = self.exprs.entry(expr).or_insert_with(|| ExprType {
            actual,
            consumer: None,
        });
        info.consumer = Some(match &info.consumer {
            Some(existing) => types::simplify_type(Type::Intersection(
                Box::new(existing.clone()),
                Box::new(consumer.clone()),
            )),
            None => consumer,
        });
    }

    fn infer_expr(&mut self, expr: poly_expr::ExprId) -> Result<Type, SpecializeError> {
        use poly_expr::Expr as PolyExpr;
        match self.arena.expr(expr) {
            PolyExpr::Lit(lit) => Ok(lit_type(lit)),
            PolyExpr::PrimitiveOp(op) => Ok(self.primitive_type(*op)),
            PolyExpr::Var(ref_id) => self.var_type(expr, *ref_id),
            PolyExpr::App(callee, arg) => self.apply_type(expr, *callee, *arg),
            PolyExpr::RefSet(reference, value) => self.ref_set_type(*reference, *value),
            PolyExpr::Lambda(param, body) => self.lambda_type(*param, *body),
            PolyExpr::Tuple(items) => self.tuple_type(expr, items),
            PolyExpr::Record { fields, spread } => self.record_type(expr, fields, spread),
            PolyExpr::PolyVariant(tag, payloads) => self.poly_variant_type(expr, tag, payloads),
            PolyExpr::Select(base, select) => self.select_type(expr, *base, *select),
            PolyExpr::Case(scrutinee, arms) => self.case_type(expr, *scrutinee, arms),
            PolyExpr::Catch(body, arms) => self.catch_type(*body, arms),
            PolyExpr::Block(stmts, tail) => self.block_type(expr, stmts, *tail),
        }
    }

    fn var_type(
        &mut self,
        expr: poly_expr::ExprId,
        ref_id: poly_expr::RefId,
    ) -> Result<Type, SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if let Some(local) = self.locals.get(&def).cloned() {
            return Ok(local);
        }
        if self.arena.constructors.contains_key(&def) {
            return self.instantiate_def_scheme(def);
        }
        if self.arena.effect_operations.contains_key(&def) {
            return self.instantiate_def_scheme(def);
        }
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                body,
                ..
            }) => {
                let ty = self.instantiate_scheme(def, scheme)?;
                if body.is_some() {
                    self.ref_uses.push(RefUse {
                        expr,
                        ty: ty.clone(),
                    });
                }
                Ok(ty)
            }
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => {
                Ok(self.graph.fresh_value())
            }
            Some(poly_expr::Def::Let { scheme: None, .. }) => Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            }),
            Some(other) => Err(SpecializeError::UnsupportedDefKind {
                def: convert_def(def),
                kind: def_kind(other),
            }),
            None => Err(SpecializeError::MissingDef {
                def: convert_def(def),
            }),
        }
    }

    fn apply_type(
        &mut self,
        expr: poly_expr::ExprId,
        callee: poly_expr::ExprId,
        arg: poly_expr::ExprId,
    ) -> Result<Type, SpecializeError> {
        if let poly_expr::Expr::Var(ref_id) = self.arena.expr(callee)
            && let Some(def) = self.arena.ref_target(*ref_id)
            && self.arena.effect_operations.contains_key(&def)
        {
            return self.effect_operation_apply_type(expr, arg, def);
        }

        let callee_ty = self.expr(callee)?;
        let (callee_value, callee_effect) = split_runtime_computation_shape(callee_ty.clone());
        let (call_arg_effect, ret_effect, ret_value) =
            match function_computation_parts(&callee_value) {
                Some(parts) => {
                    let (call_arg_effect, runtime_arg_effect) = if parts.arg_effect.is_pure_effect()
                    {
                        (
                            self.consume_expr_value(arg, parts.arg.clone())?.1,
                            Type::pure_effect(),
                        )
                    } else {
                        let runtime_arg_effect = self.consume_expr_computation(
                            arg,
                            parts.arg_effect.clone(),
                            parts.arg.clone(),
                        )?;
                        (Type::pure_effect(), runtime_arg_effect)
                    };
                    let callee_consumer = Type::Fun {
                        arg: Box::new(parts.arg.clone()),
                        arg_effect: Box::new(runtime_arg_effect),
                        ret_effect: Box::new(parts.ret_effect.clone()),
                        ret: Box::new(parts.ret.clone()),
                    };
                    self.add_expr_consumer(callee, callee_ty.clone(), callee_consumer.clone());
                    self.graph
                        .constrain_subtype(callee_value.clone(), callee_consumer)?;
                    (call_arg_effect, parts.ret_effect, parts.ret)
                }
                None => {
                    let arg_ty = self.graph.fresh_value();
                    let ret_ty = self.graph.fresh_value();
                    let ret_effect = self.graph.fresh_effect();
                    let callee_consumer = Type::Fun {
                        arg: Box::new(arg_ty.clone()),
                        arg_effect: Box::new(Type::pure_effect()),
                        ret_effect: Box::new(ret_effect.clone()),
                        ret: Box::new(ret_ty.clone()),
                    };
                    self.add_expr_consumer(callee, callee_ty.clone(), callee_consumer.clone());
                    self.graph
                        .constrain_subtype(callee_value.clone(), callee_consumer)?;
                    let call_arg_effect = self.consume_expr_value(arg, arg_ty.clone())?.1;
                    (call_arg_effect, ret_effect, ret_ty)
                }
            };
        let has_evaluation_effect =
            !callee_effect.is_pure_effect() || !call_arg_effect.is_pure_effect();
        let effect = self.join_effects([callee_effect, call_arg_effect, ret_effect])?;
        let result = self.runtime_shape(effect, ret_value)?;
        if has_evaluation_effect && matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    fn effect_operation_apply_type(
        &mut self,
        expr: poly_expr::ExprId,
        arg: poly_expr::ExprId,
        def: poly_expr::DefId,
    ) -> Result<Type, SpecializeError> {
        let operation_ty = self.instantiate_def_scheme(def)?;
        let Some(parts) = function_computation_parts(&operation_ty) else {
            let arg_ty = self.graph.fresh_value();
            self.consume_expr_value(arg, arg_ty)?;
            return self.runtime_shape(Type::pure_effect(), Type::Never);
        };
        let call_arg_effect = if parts.arg_effect.is_pure_effect() {
            self.consume_expr_value(arg, parts.arg.clone())?.1
        } else {
            self.consume_expr_computation(arg, parts.arg_effect.clone(), parts.arg.clone())?;
            Type::pure_effect()
        };
        let (ret_value, ret_runtime_effect) = split_runtime_computation_shape(parts.ret);
        let returns_never =
            matches!(ret_value, Type::Never) || operation_scheme_returns_never(self.arena, def);
        let operation_effect = self.join_effects([parts.ret_effect, ret_runtime_effect])?;
        let effect = self.join_effects([parts.arg_effect, call_arg_effect, operation_effect])?;
        let result = self.runtime_shape(effect, ret_value)?;
        if returns_never && matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    fn ref_set_type(
        &mut self,
        reference: poly_expr::ExprId,
        value: poly_expr::ExprId,
    ) -> Result<Type, SpecializeError> {
        let value_ty = self.expr(value)?;
        let (value_value, value_effect) = split_runtime_computation_shape(value_ty);
        let update_effect = self.graph.fresh_effect();
        let reference_consumer = std_types::ref_type(update_effect.clone(), value_value.clone());
        let (_, reference_effect) = self.consume_expr_value(reference, reference_consumer)?;
        let effect = self.join_effects([reference_effect, value_effect, update_effect])?;
        self.runtime_shape(effect, Type::unit())
    }

    fn lambda_type(
        &mut self,
        param: poly_expr::PatId,
        body: poly_expr::ExprId,
    ) -> Result<Type, SpecializeError> {
        let arg = self.graph.fresh_value();
        let arg_effect = self.graph.fresh_effect();
        self.bind_pat(param, types::runtime_shape(arg_effect.clone(), arg.clone()))?;
        let body_ty = self.expr(body)?;
        let (ret, ret_effect) = split_runtime_computation_shape(body_ty);
        self.consume_expr(body, types::runtime_shape(ret_effect.clone(), ret.clone()))?;
        Ok(Type::Fun {
            arg: Box::new(arg),
            arg_effect: Box::new(arg_effect),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        })
    }

    fn tuple_type(
        &mut self,
        expr: poly_expr::ExprId,
        items: &[poly_expr::ExprId],
    ) -> Result<Type, SpecializeError> {
        let mut values = Vec::with_capacity(items.len());
        let mut effects = Vec::new();
        for item in items {
            let item_ty = self.expr(*item)?;
            let (value, effect) = split_runtime_computation_shape(item_ty);
            self.consume_expr_value(*item, value.clone())?;
            values.push(value);
            effects.push(effect);
        }
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(effect, Type::Tuple(values))?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    fn record_type(
        &mut self,
        expr: poly_expr::ExprId,
        fields: &[(String, poly_expr::ExprId)],
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
    ) -> Result<Type, SpecializeError> {
        let mut effects = Vec::new();
        let mut typed = Vec::with_capacity(fields.len());
        for (name, value_expr) in fields {
            let value_ty = self.expr(*value_expr)?;
            let (value, effect) = split_runtime_computation_shape(value_ty);
            self.consume_expr_value(*value_expr, value.clone())?;
            effects.push(effect);
            typed.push(TypeField {
                name: name.clone(),
                value,
                optional: false,
            });
        }
        match spread {
            poly_expr::RecordSpread::None => {}
            poly_expr::RecordSpread::Head(expr) | poly_expr::RecordSpread::Tail(expr) => {
                let spread_ty = self.expr(*expr)?;
                let (spread_value, spread_effect) = split_runtime_computation_shape(spread_ty);
                self.consume_expr_value(*expr, spread_value.clone())?;
                effects.push(spread_effect);
                if let Type::Record(mut spread_fields) = spread_value {
                    if matches!(spread, poly_expr::RecordSpread::Head(_)) {
                        spread_fields.extend(typed);
                        typed = spread_fields;
                    } else {
                        typed.extend(spread_fields);
                    }
                }
            }
        }
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(effect, Type::Record(typed))?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    fn poly_variant_type(
        &mut self,
        expr: poly_expr::ExprId,
        tag: &str,
        payloads: &[poly_expr::ExprId],
    ) -> Result<Type, SpecializeError> {
        let mut values = Vec::with_capacity(payloads.len());
        let mut effects = Vec::new();
        for payload in payloads {
            let payload_ty = self.expr(*payload)?;
            let (value, effect) = split_runtime_computation_shape(payload_ty);
            self.consume_expr_value(*payload, value.clone())?;
            values.push(value);
            effects.push(effect);
        }
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(
            effect,
            Type::PolyVariant(vec![TypeVariant {
                name: tag.to_string(),
                payloads: values,
            }]),
        )?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    fn select_type(
        &mut self,
        expr: poly_expr::ExprId,
        base: poly_expr::ExprId,
        select: poly_expr::SelectId,
    ) -> Result<Type, SpecializeError> {
        let select_data = self.arena.select(select);
        match select_data.resolution {
            Some(poly_expr::SelectResolution::RecordField) => {
                let field = self.graph.fresh_value();
                let (_, base_effect) = self.consume_expr_value(
                    base,
                    Type::Record(vec![TypeField {
                        name: select_data.name.clone(),
                        value: field.clone(),
                        optional: false,
                    }]),
                )?;
                let result = self.runtime_shape(base_effect.clone(), field)?;
                if !base_effect.is_pure_effect() && matches!(result, Type::Thunk { .. }) {
                    self.mark_raw_thunk_computation(expr);
                }
                Ok(result)
            }
            Some(poly_expr::SelectResolution::Method { def }) => {
                let method = self.instantiate_def_scheme(def)?;
                let Some(parts) = function_computation_parts(&method) else {
                    self.expr(base)?;
                    return Ok(self.graph.fresh_value());
                };
                let demand = self.consume_selected_method_receiver(base, &parts)?;
                self.select_uses.push(SelectUse {
                    expr,
                    ty: demand.signature,
                });
                let base_effect = demand.evaluation_effect;
                let has_evaluation_effect = !base_effect.is_pure_effect();
                let effect = self.join_effects([base_effect, parts.ret_effect])?;
                let result = self.runtime_shape(effect, parts.ret)?;
                if has_evaluation_effect && matches!(result, Type::Thunk { .. }) {
                    self.mark_raw_thunk_computation(expr);
                }
                Ok(result)
            }
            Some(poly_expr::SelectResolution::TypeclassMethod { member }) => {
                let method = self.instantiate_def_scheme(member)?;
                let Some(parts) = function_computation_parts(&method) else {
                    self.expr(base)?;
                    return Ok(self.graph.fresh_value());
                };
                let demand = self.consume_selected_method_receiver(base, &parts)?;
                self.typeclass_uses.push(TypeclassUse {
                    expr,
                    member,
                    method_ty: demand.signature,
                });
                let base_effect = demand.evaluation_effect;
                let has_evaluation_effect = !base_effect.is_pure_effect();
                let effect = self.join_effects([base_effect, parts.ret_effect])?;
                let result = self.runtime_shape(effect, parts.ret)?;
                if has_evaluation_effect && matches!(result, Type::Thunk { .. }) {
                    self.mark_raw_thunk_computation(expr);
                }
                Ok(result)
            }
            None => {
                self.expr(base)?;
                Ok(self.graph.fresh_value())
            }
        }
    }

    fn consume_selected_method_receiver(
        &mut self,
        base: poly_expr::ExprId,
        parts: &FunctionComputationParts,
    ) -> Result<SelectedMethodDemand, SpecializeError> {
        let (evaluation_effect, receiver_effect) = if parts.arg_effect.is_pure_effect() {
            (
                self.consume_expr_value(base, parts.arg.clone())?.1,
                Type::pure_effect(),
            )
        } else {
            (
                Type::pure_effect(),
                self.consume_expr_computation(base, parts.arg_effect.clone(), parts.arg.clone())?,
            )
        };
        Ok(SelectedMethodDemand {
            evaluation_effect,
            signature: Type::Fun {
                arg: Box::new(parts.arg.clone()),
                arg_effect: Box::new(receiver_effect),
                ret_effect: Box::new(parts.ret_effect.clone()),
                ret: Box::new(parts.ret.clone()),
            },
        })
    }

    fn case_type(
        &mut self,
        expr: poly_expr::ExprId,
        scrutinee: poly_expr::ExprId,
        arms: &[poly_expr::CaseArm],
    ) -> Result<Type, SpecializeError> {
        let scrutinee_ty = self.expr(scrutinee)?;
        let (scrutinee_value, scrutinee_effect) = split_runtime_computation_shape(scrutinee_ty);
        let result = self.graph.fresh_value();
        let mut effects = vec![scrutinee_effect];
        for arm in arms {
            self.bind_pat(arm.pat, scrutinee_value.clone())?;
            if let Some(guard) = arm.guard {
                effects.push(self.consume_expr_value(guard, bool_type())?.1);
            }
            let (_, body_effect) = self.consume_expr_value(arm.body, result.clone())?;
            effects.push(body_effect);
        }
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(effect, result)?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    fn catch_type(
        &mut self,
        body: poly_expr::ExprId,
        arms: &[poly_expr::CatchArm],
    ) -> Result<Type, SpecializeError> {
        let body_ty = self.expr(body)?;
        let (body_value, body_effect) = self.catch_scrutinee_shape(body, body_ty)?;
        let result = self.graph.fresh_value();
        let has_value_arm = arms.iter().any(|arm| arm.operation.is_none());
        if !has_value_arm {
            self.graph
                .constrain_subtype(body_value.clone(), result.clone())?;
        }
        let mut effects = Vec::new();
        let mut handled_effects = Vec::new();
        for arm in arms {
            if let Some(operation) = &arm.operation {
                let op = self.catch_operation_types(operation.def, body_effect.clone())?;
                handled_effects.push(op.effect.clone());
                self.bind_pat(arm.pat, op.payload)?;
                self.bind_pat(
                    arm.continuation.ok_or(SpecializeError::MissingExprType {
                        expr: body.0,
                        role: ExprTypeRole::Actual,
                    })?,
                    Type::Fun {
                        arg: Box::new(op.continuation_input),
                        arg_effect: Box::new(Type::pure_effect()),
                        ret_effect: Box::new(op.residual_effect),
                        ret: Box::new(body_value.clone()),
                    },
                )?;
            } else {
                self.bind_pat(arm.pat, body_value.clone())?;
            }
            if let Some(guard) = arm.guard {
                effects.push(self.consume_expr_value(guard, bool_type())?.1);
            }
            let (_, arm_effect) = self.consume_expr_value(arm.body, result.clone())?;
            effects.push(arm_effect);
        }
        effects.push(self.residual_effect_after_handling(body_effect, &handled_effects)?);
        let effect = self.join_effects(effects)?;
        self.runtime_shape(effect, result)
    }

    fn catch_scrutinee_shape(
        &mut self,
        expr: poly_expr::ExprId,
        ty: Type,
    ) -> Result<(Type, Type), SpecializeError> {
        if let Type::OpenVar(_) = ty {
            let value = self.graph.fresh_value();
            let effect = self.graph.fresh_effect();
            self.consume_expr_computation(expr, effect.clone(), value.clone())?;
            return Ok((value, effect));
        }
        Ok(split_runtime_computation_shape(ty))
    }

    fn catch_operation_types(
        &mut self,
        def: Option<poly_expr::DefId>,
        scrutinee_effect: Type,
    ) -> Result<CatchOperationTypes, SpecializeError> {
        let Some(def) = def else {
            let payload = self.graph.fresh_value();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let operation_ty = self.instantiate_def_scheme(def)?;
        let Some(parts) = function_computation_parts(&operation_ty) else {
            let payload = self.graph.fresh_value();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let payload = parts.arg;
        let ret = parts.ret;
        let (continuation_input, ret_runtime_effect) = split_runtime_computation_shape(ret);
        let operation_effect = self.join_effects([parts.ret_effect, ret_runtime_effect])?;
        let handled_effect = self.constrain_operation_effect_to_scrutinee(
            operation_effect.clone(),
            scrutinee_effect.clone(),
        )?;
        let payload =
            refine_operation_type_from_handled_effect(payload, &operation_effect, &handled_effect);
        let continuation_input = refine_operation_type_from_handled_effect(
            continuation_input,
            &operation_effect,
            &handled_effect,
        );
        let residual_effect = self.residual_effect_after_handling(
            scrutinee_effect,
            std::slice::from_ref(&handled_effect),
        )?;
        Ok(CatchOperationTypes {
            payload,
            continuation_input,
            effect: handled_effect.clone(),
            residual_effect,
        })
    }

    fn residual_effect_after_handling(
        &mut self,
        scrutinee_effect: Type,
        handled_effects: &[Type],
    ) -> Result<Type, SpecializeError> {
        if handled_effects.is_empty() || scrutinee_effect.is_pure_effect() {
            return Ok(scrutinee_effect);
        }
        let residual = self.graph.fresh_effect();
        let mut upper_items = handled_effects
            .iter()
            .flat_map(effect_row_items)
            .cloned()
            .collect::<Vec<_>>();
        upper_items.push(residual.clone());
        self.graph
            .constrain_subtype(scrutinee_effect, Type::EffectRow(upper_items))?;
        Ok(residual)
    }

    fn constrain_operation_effect_to_scrutinee(
        &mut self,
        operation_effect: Type,
        scrutinee_effect: Type,
    ) -> Result<Type, SpecializeError> {
        if let (Type::EffectRow(operation_items), Type::EffectRow(scrutinee_items)) =
            (&operation_effect, &scrutinee_effect)
        {
            let mut handled_items = Vec::new();
            for operation_item in operation_items {
                let Some(scrutinee_item) =
                    matching_effect_row_item(operation_item, scrutinee_items)
                else {
                    continue;
                };
                self.graph
                    .constrain_subtype(operation_item.clone(), scrutinee_item.clone())?;
                self.graph
                    .constrain_subtype(scrutinee_item.clone(), operation_item.clone())?;
                handled_items.push(scrutinee_item);
            }
            if !handled_items.is_empty() {
                return Ok(Type::EffectRow(handled_items));
            }
        }
        self.graph
            .constrain_subtype(operation_effect.clone(), scrutinee_effect.clone())?;
        Ok(operation_effect)
    }

    fn block_type(
        &mut self,
        expr: poly_expr::ExprId,
        stmts: &[poly_expr::Stmt],
        tail: Option<poly_expr::ExprId>,
    ) -> Result<Type, SpecializeError> {
        let mut effects = Vec::new();
        for stmt in stmts {
            match stmt {
                poly_expr::Stmt::Let(_, pat, value) => {
                    let binding = self.graph.fresh_value();
                    self.bind_pat(*pat, binding.clone())?;
                    let value_ty = self.expr(*value)?;
                    let (value_value, value_effect) = split_runtime_computation_shape(value_ty);
                    self.consume_expr_value(*value, binding.clone())?;
                    self.graph.constrain_exact(value_value, binding)?;
                    effects.push(value_effect);
                }
                poly_expr::Stmt::Expr(expr) => {
                    self.discarded_exprs.insert(*expr);
                    let expr_ty = self.expr(*expr)?;
                    if !discarded_catch_has_open_result(self.arena.expr(*expr), &expr_ty)
                        && let Some(context) = discarded_value_context(&expr_ty)
                    {
                        self.consume_expr(*expr, context)?;
                    }
                    effects.push(split_runtime_computation_shape(expr_ty).1);
                }
                poly_expr::Stmt::Module(_, body) => {
                    let body_ty = self.block_type(expr, body, None)?;
                    effects.push(split_runtime_computation_shape(body_ty).1);
                }
            }
        }
        let tail_ty = match tail {
            Some(tail) => self.expr(tail)?,
            None => Type::unit(),
        };
        let (tail_value, tail_effect) = split_runtime_computation_shape(tail_ty);
        effects.push(tail_effect);
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(effect, tail_value)?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    fn mark_raw_thunk_computation(&mut self, expr: poly_expr::ExprId) {
        self.raw_thunk_computations.insert(expr);
    }

    fn bind_pat(&mut self, pat: poly_expr::PatId, ty: Type) -> Result<(), SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match self.arena.pat(pat) {
            PolyPat::Wild => {}
            PolyPat::Lit(lit) => self.graph.constrain_exact(ty, lit_type(lit))?,
            PolyPat::Var(def) => {
                self.locals.insert(*def, ty);
            }
            PolyPat::As(inner, def) => {
                self.locals.insert(*def, ty.clone());
                self.bind_pat(*inner, ty)?;
            }
            PolyPat::Tuple(items) => {
                let item_types = items
                    .iter()
                    .map(|_| self.graph.fresh_value())
                    .collect::<Vec<_>>();
                self.graph
                    .constrain_exact(ty, Type::Tuple(item_types.clone()))?;
                for (item, item_ty) in items.iter().zip(item_types) {
                    self.bind_pat(*item, item_ty)?;
                }
            }
            PolyPat::List {
                prefix,
                spread,
                suffix,
            } => {
                let item = self.graph.fresh_value();
                let list = list_type(item.clone());
                self.graph.constrain_exact(ty.clone(), list.clone())?;
                for pat in prefix.iter().chain(suffix) {
                    self.bind_pat(*pat, item.clone())?;
                }
                if let Some(spread) = spread {
                    self.bind_pat(*spread, list)?;
                }
            }
            PolyPat::Record { fields, spread } => {
                let field_types = fields
                    .iter()
                    .map(|field| TypeField {
                        name: field.name.clone(),
                        value: self.graph.fresh_value(),
                        optional: false,
                    })
                    .collect::<Vec<_>>();
                self.graph
                    .constrain_subtype(ty.clone(), Type::Record(field_types.clone()))?;
                for (field, field_ty) in fields.iter().zip(field_types) {
                    self.bind_pat(field.pat, field_ty.value)?;
                }
                if let Some(def) = record_spread_def(spread) {
                    self.locals.insert(def, self.graph.fresh_value());
                }
            }
            PolyPat::Con(ref_id, payloads) => self.bind_constructor_pat(*ref_id, payloads, ty)?,
            PolyPat::PolyVariant(tag, payloads) => {
                let payload_types = payloads
                    .iter()
                    .map(|_| self.graph.fresh_value())
                    .collect::<Vec<_>>();
                self.graph.constrain_subtype(
                    Type::PolyVariant(vec![TypeVariant {
                        name: tag.clone(),
                        payloads: payload_types.clone(),
                    }]),
                    ty,
                )?;
                for (payload, payload_ty) in payloads.iter().zip(payload_types) {
                    self.bind_pat(*payload, payload_ty)?;
                }
            }
            PolyPat::Or(left, right) => {
                self.bind_pat(*left, ty.clone())?;
                self.bind_pat(*right, ty)?;
            }
            PolyPat::Ref(ref_id) => self.bind_ref_pat(pat, *ref_id, ty)?,
        }
        Ok(())
    }

    fn bind_constructor_pat(
        &mut self,
        ref_id: poly_expr::RefId,
        payloads: &[poly_expr::PatId],
        scrutinee: Type,
    ) -> Result<(), SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        let constructor = self.instantiate_def_scheme(def)?;
        let Some((payload_tys, owner_ty)) = split_function_spine(constructor, payloads.len())
        else {
            return Ok(());
        };
        self.graph.constrain_exact(scrutinee, owner_ty)?;
        for (payload, payload_ty) in payloads.iter().zip(payload_tys) {
            self.bind_pat(*payload, payload_ty)?;
        }
        Ok(())
    }

    fn bind_ref_pat(
        &mut self,
        pat: poly_expr::PatId,
        ref_id: poly_expr::RefId,
        scrutinee: Type,
    ) -> Result<(), SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        let ty = self.instantiate_def_scheme(def)?;
        self.graph.constrain_exact(scrutinee, ty.clone())?;
        self.pat_ref_uses.push(PatRefUse { pat, ty });
        Ok(())
    }

    fn finish(mut self) -> Result<SolvedTask, SpecializeError> {
        self.graph.solve_role_demands()?;
        let solution = self.graph.solve_slots()?;
        let mut resolver = TypeResolver::new(&self.graph, &solution);
        let mut exprs = HashMap::new();
        // Monomorphization only needs concrete types at emitted boundaries and at
        // recursive demand edges. Slots that are not reachable from those uses may
        // stay undetermined; they are solver-local evidence, not mono output.
        for (expr, ty) in &self.exprs {
            let Some(actual) = self.resolve_expr_actual(&mut resolver, *expr, ty)? else {
                continue;
            };
            let consumer = self.resolve_expr_consumer(&mut resolver, ty)?;
            exprs.insert(*expr, SolvedExprType { actual, consumer });
        }
        let ref_signatures = self
            .ref_uses
            .iter()
            .map(|use_| {
                let ty = match self
                    .exprs
                    .get(&use_.expr)
                    .and_then(|ty| ty.consumer.as_ref())
                {
                    Some(consumer) => self.resolve_signature_type_with_context(
                        &mut resolver,
                        &use_.ty,
                        consumer,
                        TypeSlotKind::Value,
                    )?,
                    None => {
                        self.resolve_signature_type(&mut resolver, &use_.ty, TypeSlotKind::Value)?
                    }
                };
                Ok((use_.expr, ty))
            })
            .collect::<Result<HashMap<_, _>, SpecializeError>>()?;
        let select_signatures = self
            .select_uses
            .iter()
            .map(|use_| {
                let ty = match self
                    .exprs
                    .get(&use_.expr)
                    .and_then(|ty| ty.consumer.as_ref())
                {
                    Some(consumer) => self.resolve_signature_type_with_context(
                        &mut resolver,
                        &use_.ty,
                        consumer,
                        TypeSlotKind::Value,
                    )?,
                    None => {
                        self.resolve_signature_type(&mut resolver, &use_.ty, TypeSlotKind::Value)?
                    }
                };
                Ok((use_.expr, ty))
            })
            .collect::<Result<HashMap<_, _>, SpecializeError>>()?;
        let pat_ref_signatures = self
            .pat_ref_uses
            .iter()
            .map(|use_| {
                let ty =
                    self.resolve_signature_type(&mut resolver, &use_.ty, TypeSlotKind::Value)?;
                Ok((use_.pat, ty))
            })
            .collect::<Result<HashMap<_, _>, SpecializeError>>()?;
        let mut typeclass_resolutions = HashMap::new();
        for use_ in &self.typeclass_uses {
            let signature = match self
                .exprs
                .get(&use_.expr)
                .and_then(|ty| ty.consumer.as_ref())
            {
                Some(consumer) => self.resolve_signature_type_with_context(
                    &mut resolver,
                    &use_.method_ty,
                    consumer,
                    TypeSlotKind::Value,
                )?,
                None => self.resolve_signature_type(
                    &mut resolver,
                    &use_.method_ty,
                    TypeSlotKind::Value,
                )?,
            };
            let implementation = self.resolve_typeclass_use(use_.member, &signature)?;
            typeclass_resolutions.insert(
                use_.expr,
                TypeclassResolution {
                    implementation,
                    signature,
                },
            );
        }
        Ok(SolvedTask {
            exprs,
            ref_signatures,
            select_signatures,
            typeclass_resolutions,
            pat_ref_signatures,
            raw_thunk_computations: self.raw_thunk_computations,
        })
    }

    fn resolve_expr_actual(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        expr: poly_expr::ExprId,
        ty: &ExprType,
    ) -> Result<Option<Type>, SpecializeError> {
        if self.expr_is_defined_ref(expr)
            && let Some(consumer) = &ty.consumer
        {
            return match resolver.resolve(consumer) {
                Ok(actual) => Ok(Some(close_resolved_runtime_surface(
                    actual,
                    TypeSlotKind::Value,
                ))),
                Err(SpecializeError::UndeterminedTypeSlot { .. }) => self
                    .resolve_partial_output_type(resolver, consumer, TypeSlotKind::Value)
                    .map(Some),
                Err(error) => Err(error),
            };
        }
        if self.required_exprs.contains(&expr) {
            return match resolver.resolve(&ty.actual) {
                Ok(actual) => Ok(Some(close_resolved_runtime_surface(
                    actual,
                    TypeSlotKind::Value,
                ))),
                Err(SpecializeError::UndeterminedTypeSlot { .. }) => self
                    .resolve_partial_output_type(resolver, &ty.actual, TypeSlotKind::Value)
                    .map(Some),
                Err(error) => Err(error),
            };
        }
        match match &ty.consumer {
            Some(consumer) => resolver.resolve_with_context(&ty.actual, consumer),
            None => resolver.resolve(&ty.actual),
        } {
            Ok(actual) => Ok(Some(close_resolved_runtime_surface(
                actual,
                TypeSlotKind::Value,
            ))),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) if ty.consumer.is_some() => self
                .resolve_partial_output_type(
                    resolver,
                    ty.consumer.as_ref().expect("consumer checked above"),
                    TypeSlotKind::Value,
                )
                .map(Some),
            Err(SpecializeError::UndeterminedTypeSlot { .. })
                if self.discarded_exprs.contains(&expr) =>
            {
                self.resolve_partial_output_type(resolver, &ty.actual, TypeSlotKind::Value)
                    .map(Some)
            }
            Err(SpecializeError::UndeterminedTypeSlot { .. })
                if self.expr_can_omit_concrete_type(expr) =>
            {
                match &ty.consumer {
                    Some(consumer) => match resolver.resolve(consumer) {
                        Ok(consumer) => Ok(Some(close_resolved_runtime_surface(
                            consumer,
                            TypeSlotKind::Value,
                        ))),
                        Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(None),
                        Err(error) => Err(error),
                    },
                    None => Ok(None),
                }
            }
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(None),
            Err(error) => Err(error),
        }
    }

    fn expr_is_defined_ref(&self, expr: poly_expr::ExprId) -> bool {
        let poly_expr::Expr::Var(ref_id) = self.arena.expr(expr) else {
            return false;
        };
        let Some(def) = self.arena.ref_target(*ref_id) else {
            return false;
        };
        matches!(
            self.arena.defs.get(def),
            Some(poly_expr::Def::Let { body: Some(_), .. })
        )
    }

    fn resolve_expr_consumer(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &ExprType,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(consumer) = &ty.consumer else {
            return Ok(None);
        };
        match resolver.resolve(consumer) {
            Ok(consumer) => Ok(Some(close_resolved_runtime_surface(
                consumer,
                TypeSlotKind::Value,
            ))),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => self
                .resolve_partial_output_type(resolver, consumer, TypeSlotKind::Value)
                .map(Some),
            Err(error) => Err(error),
        }
    }

    fn resolve_signature_type(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &Type,
        context: TypeSlotKind,
    ) -> Result<Type, SpecializeError> {
        match resolver.resolve(ty) {
            Ok(ty) => Ok(close_resolved_inference_surface(ty, context)),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => {
                self.resolve_partial_signature_type(resolver, ty, context)
            }
            Err(error) => Err(error),
        }
    }

    fn resolve_signature_type_with_context(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &Type,
        consumer: &Type,
        context: TypeSlotKind,
    ) -> Result<Type, SpecializeError> {
        match resolver.resolve_with_context(ty, consumer) {
            Ok(ty) => Ok(close_resolved_inference_surface(ty, context)),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => {
                self.resolve_partial_signature_type(resolver, ty, context)
            }
            Err(error) => Err(error),
        }
    }

    fn resolve_partial_output_type(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &Type,
        context: TypeSlotKind,
    ) -> Result<Type, SpecializeError> {
        let partial = resolver
            .resolve_partial_candidate(ty, true)?
            .unwrap_or_else(|| ty.clone());
        Ok(close_resolved_runtime_surface(partial, context))
    }

    fn resolve_partial_signature_type(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &Type,
        context: TypeSlotKind,
    ) -> Result<Type, SpecializeError> {
        let partial = resolver
            .resolve_partial_candidate(ty, true)?
            .unwrap_or_else(|| ty.clone());
        Ok(close_resolved_inference_surface(partial, context))
    }

    fn expr_can_omit_concrete_type(&self, expr: poly_expr::ExprId) -> bool {
        let poly_expr::Expr::Var(ref_id) = self.arena.expr(expr) else {
            return false;
        };
        let Some(def) = self.arena.ref_target(*ref_id) else {
            return false;
        };
        matches!(
            self.arena.defs.get(def),
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. })
        )
    }

    fn resolve_typeclass_use(
        &self,
        member: poly_expr::DefId,
        signature: &Type,
    ) -> Result<poly_expr::DefId, SpecializeError> {
        let Some(poly_expr::Def::Let {
            body,
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(member)
        else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(member),
            });
        };
        let predicates = types::role_predicates_for_scheme_signature(
            self.arena,
            member,
            scheme,
            Some(signature),
        )?;
        let mut implementations = Vec::new();
        let mut matched_candidate_count = 0usize;
        for predicate in &predicates {
            let Some(input_types) = exact_role_input_types(predicate) else {
                continue;
            };
            for candidate in self.arena.role_impls.candidates(&predicate.role) {
                if roles::candidate_application(&self.arena.typ, predicate, candidate, &input_types)
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
            [implementation] => Ok(*implementation),
            [] if body.is_some() && matched_candidate_count > 0 => Ok(member),
            [] => Err(SpecializeError::UnresolvedTypeclassMethod {
                member: convert_def(member),
                receiver: signature.clone(),
            }),
            _ => Err(SpecializeError::AmbiguousTypeclassMethod {
                member: convert_def(member),
                receiver: signature.clone(),
                candidates: implementations.into_iter().map(convert_def).collect(),
            }),
        }
    }

    fn instantiate_def_scheme(&mut self, def: poly_expr::DefId) -> Result<Type, SpecializeError> {
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            });
        };
        self.instantiate_scheme(def, scheme)
    }

    fn instantiate_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let instantiated = types::instantiate_principal_scheme_for_inference_with_fresh_and_roles(
            self.arena,
            def,
            scheme,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.graph.fresh_value(),
                types::SchemeQuantifierKind::Effect => self.graph.fresh_effect(),
            },
        )?;
        self.graph.add_role_demands(instantiated.role_predicates);
        self.graph
            .constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    #[track_caller]
    fn join_effects(
        &mut self,
        effects: impl IntoIterator<Item = Type>,
    ) -> Result<Type, SpecializeError> {
        let effects = effects
            .into_iter()
            .filter(|effect| !effect.is_pure_effect())
            .collect::<Vec<_>>();
        match effects.as_slice() {
            [] => Ok(Type::pure_effect()),
            [single] => Ok(single.clone()),
            _ => {
                let effect = self.graph.fresh_effect();
                for item in effects {
                    self.graph.constrain_subtype(item, effect.clone())?;
                }
                Ok(effect)
            }
        }
    }

    fn runtime_shape(&self, effect: Type, value: Type) -> Result<Type, SpecializeError> {
        Ok(types::runtime_shape(effect, value))
    }

    fn primitive_type(&mut self, op: poly_expr::PrimitiveOp) -> Type {
        use poly_expr::PrimitiveOp;
        match op {
            PrimitiveOp::YadaYada => Type::Never,
            PrimitiveOp::BoolNot => unary_type(bool_type(), bool_type()),
            PrimitiveOp::BoolEq => binary_type(bool_type(), bool_type()),
            PrimitiveOp::ListEmpty => {
                let item = self.graph.fresh_value();
                unary_type(Type::unit(), list_type(item))
            }
            PrimitiveOp::ListSingleton => {
                let item = self.graph.fresh_value();
                unary_type(item.clone(), list_type(item))
            }
            PrimitiveOp::ListLen => {
                let item = self.graph.fresh_value();
                unary_type(list_type(item), int_type())
            }
            PrimitiveOp::ListMerge => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(vec![list.clone(), list.clone()], list)
            }
            PrimitiveOp::ListIndex => {
                let item = self.graph.fresh_value();
                function_type(vec![list_type(item.clone()), int_type()], item)
            }
            PrimitiveOp::ListIndexRange => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(vec![list.clone(), range_type()], list)
            }
            PrimitiveOp::ListSplice => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(vec![list.clone(), range_type(), list.clone()], list)
            }
            PrimitiveOp::ListIndexRangeRaw => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(vec![list.clone(), int_type(), int_type()], list)
            }
            PrimitiveOp::ListSpliceRaw => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(
                    vec![list.clone(), int_type(), int_type(), list.clone()],
                    list,
                )
            }
            PrimitiveOp::ListViewRaw => {
                let item = self.graph.fresh_value();
                unary_type(list_type(item.clone()), list_view_type(item))
            }
            PrimitiveOp::StringLen | PrimitiveOp::StringLineCount => {
                unary_type(str_type(), int_type())
            }
            PrimitiveOp::StringIndex => function_type(vec![str_type(), int_type()], char_type()),
            PrimitiveOp::StringIndexRange => {
                function_type(vec![str_type(), range_type()], str_type())
            }
            PrimitiveOp::StringSplice => {
                function_type(vec![str_type(), range_type(), str_type()], str_type())
            }
            PrimitiveOp::StringIndexRangeRaw => {
                function_type(vec![str_type(), int_type(), int_type()], str_type())
            }
            PrimitiveOp::StringSpliceRaw => function_type(
                vec![str_type(), int_type(), int_type(), str_type()],
                str_type(),
            ),
            PrimitiveOp::StringLineRange => {
                function_type(vec![str_type(), int_type()], range_type())
            }
            PrimitiveOp::IntAdd
            | PrimitiveOp::IntSub
            | PrimitiveOp::IntMul
            | PrimitiveOp::IntDiv
            | PrimitiveOp::IntMod => binary_type(int_type(), int_type()),
            PrimitiveOp::IntEq
            | PrimitiveOp::IntLt
            | PrimitiveOp::IntLe
            | PrimitiveOp::IntGt
            | PrimitiveOp::IntGe => binary_type(int_type(), bool_type()),
            PrimitiveOp::FloatAdd
            | PrimitiveOp::FloatSub
            | PrimitiveOp::FloatMul
            | PrimitiveOp::FloatDiv => binary_type(float_type(), float_type()),
            PrimitiveOp::FloatEq
            | PrimitiveOp::FloatLt
            | PrimitiveOp::FloatLe
            | PrimitiveOp::FloatGt
            | PrimitiveOp::FloatGe => binary_type(float_type(), bool_type()),
            PrimitiveOp::StringEq => binary_type(str_type(), bool_type()),
            PrimitiveOp::StringConcat => binary_type(str_type(), str_type()),
            PrimitiveOp::StringToBytes => unary_type(str_type(), bytes_type()),
            PrimitiveOp::CharEq => binary_type(char_type(), bool_type()),
            PrimitiveOp::CharToString => unary_type(char_type(), str_type()),
            PrimitiveOp::CharIsWhitespace
            | PrimitiveOp::CharIsPunctuation
            | PrimitiveOp::CharIsWord => unary_type(char_type(), bool_type()),
            PrimitiveOp::BytesLen => unary_type(bytes_type(), int_type()),
            PrimitiveOp::BytesEq => binary_type(bytes_type(), bool_type()),
            PrimitiveOp::BytesConcat => binary_type(bytes_type(), bytes_type()),
            PrimitiveOp::BytesIndex => function_type(vec![bytes_type(), int_type()], int_type()),
            PrimitiveOp::BytesIndexRange => {
                function_type(vec![bytes_type(), range_type()], bytes_type())
            }
            PrimitiveOp::BytesToUtf8Raw => {
                unary_type(bytes_type(), Type::Tuple(vec![str_type(), int_type()]))
            }
            PrimitiveOp::BytesToPath => unary_type(bytes_type(), path_type()),
            PrimitiveOp::PathToBytes => unary_type(path_type(), bytes_type()),
            PrimitiveOp::IntToString | PrimitiveOp::IntToHex | PrimitiveOp::IntToUpperHex => {
                unary_type(int_type(), str_type())
            }
            PrimitiveOp::FloatToString => unary_type(float_type(), str_type()),
            PrimitiveOp::BoolToString => unary_type(bool_type(), str_type()),
        }
    }
}

#[derive(Debug, Clone)]
struct ExprType {
    actual: Type,
    consumer: Option<Type>,
}

#[derive(Debug, Clone)]
struct RefUse {
    expr: poly_expr::ExprId,
    ty: Type,
}

#[derive(Debug, Clone)]
struct SelectUse {
    expr: poly_expr::ExprId,
    ty: Type,
}

#[derive(Debug, Clone)]
struct TypeclassUse {
    expr: poly_expr::ExprId,
    member: poly_expr::DefId,
    method_ty: Type,
}

struct SelectedMethodDemand {
    evaluation_effect: Type,
    signature: Type,
}

#[derive(Debug, Clone)]
struct PatRefUse {
    pat: poly_expr::PatId,
    ty: Type,
}

struct CatchOperationTypes {
    payload: Type,
    continuation_input: Type,
    effect: Type,
    residual_effect: Type,
}

struct TypeGraph<'a> {
    arena: &'a poly_expr::Arena,
    slots: Vec<TypeSlot>,
    pending: VecDeque<SubtypeConstraint>,
    row_residuals: HashMap<RowResidualKey, u32>,
    closed_effect_subtraction_consumers: HashSet<(u32, EffectSubtractionDemand)>,
    role_demands: Vec<types::InstantiatedRolePredicate>,
}

impl<'a> TypeGraph<'a> {
    fn new(arena: &'a poly_expr::Arena) -> Self {
        Self {
            arena,
            slots: Vec::new(),
            pending: VecDeque::new(),
            row_residuals: HashMap::new(),
            closed_effect_subtraction_consumers: HashSet::new(),
            role_demands: Vec::new(),
        }
    }

    fn fresh_value(&mut self) -> Type {
        self.fresh_slot(TypeSlotKind::Value)
    }

    fn fresh_effect(&mut self) -> Type {
        self.fresh_slot(TypeSlotKind::Effect)
    }

    fn fresh_slot(&mut self, kind: TypeSlotKind) -> Type {
        let id = self.slots.len() as u32;
        self.slots.push(TypeSlot::new(kind));
        Type::OpenVar(id)
    }

    fn constrain_exact(&mut self, left: Type, right: Type) -> Result<(), SpecializeError> {
        self.constrain_subtype(left.clone(), right.clone())?;
        self.constrain_subtype(right, left)
    }

    fn constrain_subtype(&mut self, lower: Type, upper: Type) -> Result<(), SpecializeError> {
        self.constrain_weighted_subtype(lower, empty_stack_weight(), upper, empty_stack_weight())
    }

    fn constrain_weighted_subtype(
        &mut self,
        lower: Type,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        if lower != upper {
            self.pending.push_back(SubtypeConstraint {
                lower,
                lower_weight,
                upper,
                upper_weight,
            });
        }
        Ok(())
    }

    fn add_role_demands(
        &mut self,
        demands: impl IntoIterator<Item = types::InstantiatedRolePredicate>,
    ) {
        self.role_demands.extend(demands);
    }

    fn constrain_recursive_bounds(
        &mut self,
        bounds: Vec<types::InstantiatedRecursiveBound>,
    ) -> Result<(), SpecializeError> {
        for bound in bounds {
            self.constrain_subtype(bound.lower, bound.value.clone())?;
            self.constrain_subtype(bound.value, bound.upper)?;
        }
        Ok(())
    }

    fn solve_role_demands(&mut self) -> Result<(), SpecializeError> {
        let mut applied = HashSet::new();
        loop {
            self.solve_constraints()?;
            let solution = self.solve_slots()?;
            let demands = self.role_demands.clone();
            let mut progressed = false;
            for demand in demands {
                if applied.contains(&demand) {
                    continue;
                }
                let input_types = {
                    let mut resolver = TypeResolver::new(self, &solution);
                    resolve_role_input_types(&mut resolver, &demand)?
                };
                let Some(input_types) = input_types else {
                    continue;
                };
                let applications = self
                    .arena
                    .role_impls
                    .candidates(&demand.role)
                    .iter()
                    .filter_map(|candidate| {
                        roles::candidate_application(
                            &self.arena.typ,
                            &demand,
                            candidate,
                            &input_types,
                        )
                    })
                    .collect::<Vec<_>>();
                let [application] = applications.as_slice() else {
                    continue;
                };
                let associated = application.associated.clone();
                let prerequisites = application.prerequisites.clone();
                for (lower, candidate, upper) in associated {
                    self.constrain_subtype(lower, candidate.clone())?;
                    self.constrain_subtype(candidate, upper)?;
                }
                self.add_role_demands(prerequisites);
                applied.insert(demand);
                progressed = true;
            }
            if !progressed {
                self.solve_constraints()?;
                self.close_pure_effect_subtraction_tails_until_stable()?;
                return Ok(());
            }
        }
    }

    fn solve_constraints(&mut self) -> Result<(), SpecializeError> {
        while let Some(constraint) = self.pending.pop_front() {
            self.process_subtype(
                constraint.lower,
                constraint.lower_weight,
                constraint.upper,
                constraint.upper_weight,
            )?;
        }
        Ok(())
    }

    fn close_pure_effect_subtraction_tails_until_stable(&mut self) -> Result<(), SpecializeError> {
        loop {
            while let Some(constraint) = self.pending.pop_front() {
                self.process_subtype(
                    constraint.lower,
                    constraint.lower_weight,
                    constraint.upper,
                    constraint.upper_weight,
                )?;
            }
            if !self.close_pure_effect_subtraction_tails()? {
                return Ok(());
            }
        }
    }

    fn process_subtype(
        &mut self,
        lower: Type,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        let (lower, lower_weight) = peel_stack_weight(lower, lower_weight);
        let (upper, upper_weight) = peel_stack_weight(upper, upper_weight);
        let unweighted =
            stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight);
        if lower == upper && unweighted {
            return Ok(());
        }
        if unweighted && self.effect_row_lower_returns_to_same_tail(&lower, &upper) {
            return Ok(());
        }
        match (lower, upper) {
            (Type::Never, _) | (_, Type::Any) => Ok(()),
            (Type::OpenVar(lower), Type::OpenVar(upper)) if unweighted => {
                self.add_edge(lower, upper)
            }
            (Type::OpenVar(lower), Type::OpenVar(upper)) => {
                self.add_weighted_edge(lower, upper, lower_weight, upper_weight)
            }
            (Type::Union(left, right), upper) => {
                self.constrain_weighted_subtype(
                    *left,
                    lower_weight.clone(),
                    upper.clone(),
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(*right, lower_weight, upper, upper_weight)
            }
            (lower, Type::Intersection(left, right)) => {
                self.constrain_weighted_subtype(
                    lower.clone(),
                    lower_weight.clone(),
                    *left,
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(lower, lower_weight, *right, upper_weight)
            }
            (Type::OpenVar(slot), upper) => {
                self.add_upper_weighted(slot, lower_weight, upper, upper_weight)
            }
            (lower, Type::OpenVar(slot)) => {
                self.add_lower_weighted(slot, lower, lower_weight, upper_weight)
            }
            (
                Type::Fun {
                    arg: lower_arg,
                    arg_effect: lower_arg_eff,
                    ret_effect: lower_ret_eff,
                    ret: lower_ret,
                },
                Type::Fun {
                    arg: upper_arg,
                    arg_effect: upper_arg_eff,
                    ret_effect: upper_ret_eff,
                    ret: upper_ret,
                },
            ) => {
                let (lower_arg, lower_arg_eff) =
                    split_declared_runtime_shape(*lower_arg, *lower_arg_eff);
                let (upper_arg, upper_arg_eff) =
                    split_declared_runtime_shape(*upper_arg, *upper_arg_eff);
                let (lower_ret, lower_ret_eff) =
                    split_declared_runtime_shape(*lower_ret, *lower_ret_eff);
                let (upper_ret, upper_ret_eff) =
                    split_declared_runtime_shape(*upper_ret, *upper_ret_eff);
                self.constrain_weighted_subtype(
                    upper_arg,
                    upper_weight.clone(),
                    lower_arg,
                    lower_weight.clone(),
                )?;
                self.constrain_weighted_subtype(
                    upper_arg_eff,
                    upper_weight.clone(),
                    lower_arg_eff,
                    lower_weight.clone(),
                )?;
                self.constrain_weighted_subtype(
                    lower_ret_eff,
                    lower_weight.clone(),
                    upper_ret_eff,
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(lower_ret, lower_weight, upper_ret, upper_weight)
            }
            (
                Type::Thunk {
                    effect: lower_effect,
                    value: lower_value,
                },
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) => {
                self.constrain_weighted_subtype(
                    *lower_effect,
                    lower_weight.clone(),
                    *upper_effect,
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(
                    *lower_value,
                    lower_weight,
                    *upper_value,
                    upper_weight,
                )
            }
            (
                lower,
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) => {
                self.constrain_weighted_subtype(
                    lower,
                    lower_weight.clone(),
                    *upper_value,
                    upper_weight.clone(),
                )?;
                self.constrain_weighted_subtype(
                    Type::pure_effect(),
                    lower_weight,
                    *upper_effect,
                    upper_weight,
                )
            }
            (
                Type::Thunk {
                    value: lower_value, ..
                },
                upper,
            ) => self.constrain_weighted_subtype(*lower_value, lower_weight, upper, upper_weight),
            (
                Type::Con {
                    path: lower_path,
                    args: lower_args,
                },
                Type::Con {
                    path: upper_path,
                    args: upper_args,
                },
            ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
                for (lower, upper) in lower_args.into_iter().zip(upper_args) {
                    self.constrain_weighted_subtype(
                        lower.clone(),
                        lower_weight.clone(),
                        upper.clone(),
                        upper_weight.clone(),
                    )?;
                    self.constrain_weighted_subtype(
                        upper,
                        upper_weight.clone(),
                        lower,
                        lower_weight.clone(),
                    )?;
                }
                Ok(())
            }
            (
                Type::Con {
                    path: lower_path,
                    args: lower_args,
                },
                Type::Con {
                    path: upper_path,
                    args: upper_args,
                },
            ) => {
                if !unweighted {
                    return Ok(());
                }
                let lower_ty = Type::Con {
                    path: lower_path.clone(),
                    args: lower_args,
                };
                let upper_ty = Type::Con {
                    path: upper_path.clone(),
                    args: upper_args,
                };
                self.constrain_direct_cast(&lower_path, &upper_path, lower_ty, upper_ty)
            }
            (Type::Tuple(lower_items), Type::Tuple(upper_items))
                if lower_items.len() == upper_items.len() =>
            {
                for (lower, upper) in lower_items.into_iter().zip(upper_items) {
                    self.constrain_weighted_subtype(
                        lower,
                        lower_weight.clone(),
                        upper,
                        upper_weight.clone(),
                    )?;
                }
                Ok(())
            }
            (Type::Record(lower_fields), Type::Record(upper_fields)) => {
                for upper_field in upper_fields {
                    if let Some(lower_field) = record_field_type(&lower_fields, &upper_field.name) {
                        self.constrain_weighted_subtype(
                            lower_field.value.clone(),
                            lower_weight.clone(),
                            upper_field.value,
                            upper_weight.clone(),
                        )?;
                    }
                }
                Ok(())
            }
            (Type::PolyVariant(lower_variants), Type::PolyVariant(upper_variants)) => {
                for lower_variant in lower_variants {
                    let Some(upper_variant) = upper_variants.iter().find(|variant| {
                        variant.name == lower_variant.name
                            && variant.payloads.len() == lower_variant.payloads.len()
                    }) else {
                        continue;
                    };
                    for (lower, upper) in lower_variant
                        .payloads
                        .into_iter()
                        .zip(upper_variant.payloads.iter().cloned())
                    {
                        self.constrain_weighted_subtype(
                            lower,
                            lower_weight.clone(),
                            upper,
                            upper_weight.clone(),
                        )?;
                    }
                }
                Ok(())
            }
            (Type::EffectRow(lower_items), Type::EffectRow(upper_items)) => self
                .constrain_effect_rows_weighted(
                    lower_items,
                    lower_weight,
                    upper_items,
                    upper_weight,
                ),
            _ => Ok(()),
        }
    }

    fn effect_row_lower_returns_to_same_tail(&self, lower: &Type, upper: &Type) -> bool {
        let (Type::EffectRow(items), Type::OpenVar(upper)) = (lower, upper) else {
            return false;
        };
        let Some(Type::OpenVar(tail)) = items.last() else {
            return false;
        };
        tail == upper
            && self
                .slots
                .get(*tail as usize)
                .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
    }

    fn constrain_direct_cast(
        &mut self,
        source: &[String],
        target: &[String],
        lower: Type,
        upper: Type,
    ) -> Result<(), SpecializeError> {
        let candidates = self
            .arena
            .cast_rules
            .iter()
            .filter(|rule| rule.source == source && rule.target == target)
            .cloned()
            .collect::<Vec<_>>();
        for candidate in candidates {
            let predicate = self.instantiate_cast_scheme(candidate.def, &candidate.scheme)?;
            self.constrain_subtype(
                predicate,
                types::pure_function_type(lower.clone(), upper.clone()),
            )?;
        }
        Ok(())
    }

    fn instantiate_cast_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let instantiated = types::instantiate_principal_scheme_for_inference_with_fresh_and_roles(
            self.arena,
            def,
            scheme,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.fresh_value(),
                types::SchemeQuantifierKind::Effect => self.fresh_effect(),
            },
        )?;
        self.add_role_demands(instantiated.role_predicates);
        self.constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    fn constrain_effect_rows_weighted(
        &mut self,
        lower_items: Vec<Type>,
        lower_weight: StackWeight,
        upper_items: Vec<Type>,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        let (lower_items, lower_tail) = self.split_effect_row_tail(lower_items);
        let (upper_items, upper_tail) = self.split_effect_row_tail(upper_items);
        let mut matched_upper = vec![false; upper_items.len()];
        let mut lower_extra = Vec::new();

        for lower in lower_items {
            let Some(upper_index) = upper_items.iter().enumerate().find_map(|(index, upper)| {
                (!matched_upper[index] && same_effect_row_family(&lower, upper)).then_some(index)
            }) else {
                lower_extra.push(lower);
                continue;
            };
            matched_upper[upper_index] = true;
            self.constrain_weighted_subtype(
                lower,
                lower_weight.clone(),
                upper_items[upper_index].clone(),
                upper_weight.clone(),
            )?;
        }

        let upper_extra = upper_items
            .into_iter()
            .enumerate()
            .filter_map(|(index, upper)| (!matched_upper[index]).then_some(upper))
            .collect::<Vec<_>>();
        if !lower_extra.is_empty() {
            if let Some(upper_tail) = upper_tail.clone() {
                self.constrain_weighted_subtype(
                    Type::EffectRow(lower_extra),
                    lower_weight.clone(),
                    upper_tail,
                    upper_weight.clone(),
                )?;
            }
        }
        let upper_extra_is_empty = upper_extra.is_empty();
        if !upper_extra_is_empty && let Some(lower_tail) = lower_tail.clone() {
            self.constrain_weighted_subtype(
                lower_tail,
                lower_weight.clone(),
                effect_row_from_parts(upper_extra, upper_tail.clone()),
                upper_weight.clone(),
            )?;
        }

        match (lower_tail, upper_tail) {
            (Some(lower_tail), Some(upper_tail)) if upper_extra_is_empty => {
                self.constrain_weighted_subtype(lower_tail, lower_weight, upper_tail, upper_weight)
            }
            _ => Ok(()),
        }
    }

    fn constrain_consumed_computation_effect(
        &mut self,
        actual_effect: Type,
        expected_effect: Type,
    ) -> Result<Type, SpecializeError> {
        if let Some(runtime_effect) =
            self.constrain_subtractable_computation_effect(actual_effect.clone(), &expected_effect)?
        {
            return Ok(runtime_effect);
        }
        self.constrain_subtype(actual_effect, expected_effect.clone())?;
        Ok(expected_effect)
    }

    fn constrain_subtractable_computation_effect(
        &mut self,
        actual_effect: Type,
        expected_effect: &Type,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(demand) = effect_consumption_demand(expected_effect) else {
            return Ok(None);
        };
        if let Type::OpenVar(slot) = actual_effect {
            if self
                .slots
                .get(slot as usize)
                .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
            {
                self.add_effect_subtraction_consumer(slot, demand.clone())?;
                let runtime_effect = demand.runtime_effect;
                self.constrain_subtype(Type::OpenVar(slot), runtime_effect.clone())?;
                return Ok(Some(runtime_effect));
            }
            return Ok(None);
        }
        let Some((actual_items, actual_tail)) = self.effect_row_parts(actual_effect.clone()) else {
            return Ok(None);
        };
        self.constrain_effect_lower_against_subtraction_demand(
            actual_items,
            actual_tail,
            &demand,
            true,
        )?;
        self.constrain_subtype(actual_effect, demand.runtime_effect.clone())?;
        Ok(Some(demand.runtime_effect))
    }

    fn add_effect_subtraction_consumer(
        &mut self,
        slot: u32,
        demand: EffectSubtractionDemand,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        if self.slots[index]
            .effect_subtraction_consumers
            .contains(&demand)
        {
            return Ok(());
        }
        self.slots[index]
            .effect_subtraction_consumers
            .push(demand.clone());
        let lowers = self.slots[index].lower.clone();
        for lower in lowers {
            let Some((items, tail)) = self.effect_row_parts(lower) else {
                continue;
            };
            self.constrain_effect_lower_against_subtraction_demand(items, tail, &demand, false)?;
        }
        Ok(())
    }

    fn constrain_effect_lower_against_subtraction_demand(
        &mut self,
        actual_items: Vec<Type>,
        actual_tail: Option<Type>,
        demand: &EffectSubtractionDemand,
        close_pure_tail: bool,
    ) -> Result<(), SpecializeError> {
        let residual = self.residual_effect_after_consuming_handled(
            actual_items,
            actual_tail,
            &demand.handled_items,
        )?;
        if close_pure_tail && residual.is_pure_effect() {
            return self.constrain_exact(demand.tail.clone(), residual);
        }
        if !residual.is_pure_effect() {
            self.constrain_subtype(residual, demand.tail.clone())?;
        }
        Ok(())
    }

    fn close_pure_effect_subtraction_tails(&mut self) -> Result<bool, SpecializeError> {
        let mut closed = false;
        for slot in 0..self.slots.len() {
            let demands = self.slots[slot].effect_subtraction_consumers.clone();
            for demand in demands {
                let key = (slot as u32, demand.clone());
                if self.closed_effect_subtraction_consumers.contains(&key) {
                    continue;
                }
                if !self.effect_subtraction_tail_is_pure(slot as u32, &demand) {
                    continue;
                }
                self.closed_effect_subtraction_consumers.insert(key);
                self.constrain_exact(demand.tail.clone(), Type::pure_effect())?;
                closed = true;
            }
        }
        Ok(closed)
    }

    fn effect_subtraction_tail_is_pure(&self, slot: u32, demand: &EffectSubtractionDemand) -> bool {
        let Some(slot) = self.slots.get(slot as usize) else {
            return false;
        };
        let mut saw_concrete_lower = false;
        for lower in &slot.lower {
            let Some((items, tail)) = self.effect_row_parts(lower.clone()) else {
                return false;
            };
            if items.is_empty() && matches!(tail, Some(Type::OpenVar(_))) {
                continue;
            }
            saw_concrete_lower = true;
            if !residual_effect_after_consuming_handled_candidate(
                items,
                tail,
                &demand.handled_items,
            )
            .is_pure_effect()
            {
                return false;
            }
        }
        saw_concrete_lower
    }

    fn residual_effect_after_consuming_handled(
        &mut self,
        actual_items: Vec<Type>,
        actual_tail: Option<Type>,
        handled_items: &[Type],
    ) -> Result<Type, SpecializeError> {
        let mut matched_handled = vec![false; handled_items.len()];
        let mut residual_items = Vec::new();
        for actual in actual_items {
            let Some(index) = handled_items
                .iter()
                .enumerate()
                .find_map(|(index, handled)| {
                    (!matched_handled[index] && same_effect_row_family(&actual, handled))
                        .then_some(index)
                })
            else {
                residual_items.push(actual);
                continue;
            };
            matched_handled[index] = true;
            self.constrain_exact(actual, handled_items[index].clone())?;
        }
        Ok(effect_row_from_parts(residual_items, actual_tail))
    }

    fn effect_row_parts(&self, effect: Type) -> Option<(Vec<Type>, Option<Type>)> {
        if effect.is_pure_effect() {
            return Some((Vec::new(), None));
        }
        let Type::EffectRow(items) = effect else {
            return None;
        };
        Some(self.split_effect_row_tail(items))
    }

    fn split_effect_row_tail(&self, mut items: Vec<Type>) -> (Vec<Type>, Option<Type>) {
        let Some(Type::OpenVar(slot)) = items.last().cloned() else {
            return (items, None);
        };
        if self
            .slots
            .get(slot as usize)
            .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
        {
            items.pop();
            return (items, Some(Type::OpenVar(slot)));
        }
        (items, None)
    }

    fn add_weighted_edge(
        &mut self,
        lower: u32,
        upper: u32,
        lower_weight: StackWeight,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(lower)?;
        self.ensure_slot(upper)?;
        if lower == upper && lower_weight == upper_weight {
            return Ok(());
        }
        if stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight) {
            return self.add_edge(lower, upper);
        }
        let forward = WeightedSlotEdge {
            slot: upper,
            lower_weight: lower_weight.clone(),
            upper_weight: upper_weight.clone(),
        };
        let backward = WeightedSlotEdge {
            slot: lower,
            lower_weight,
            upper_weight,
        };
        let lower_index = lower as usize;
        let upper_index = upper as usize;
        if !self.slots[lower_index]
            .weighted_successors
            .contains(&forward)
        {
            self.slots[lower_index].weighted_successors.push(forward);
        }
        if !self.slots[upper_index]
            .weighted_predecessors
            .contains(&backward)
        {
            self.slots[upper_index].weighted_predecessors.push(backward);
        }
        let lower_bounds = self.slots[lower_index].lower.clone();
        let successors = self.slots[lower_index].weighted_successors.clone();
        for bound in lower_bounds {
            for successor in &successors {
                self.constrain_weighted_subtype(
                    bound.clone(),
                    successor.lower_weight.clone(),
                    Type::OpenVar(successor.slot),
                    successor.upper_weight.clone(),
                )?;
            }
        }
        let weighted_lower_bounds = self.slots[lower_index].weighted_lower.clone();
        let successors = self.slots[lower_index].weighted_successors.clone();
        for bound in weighted_lower_bounds {
            for successor in &successors {
                self.constrain_weighted_subtype(
                    bound.ty.clone(),
                    compose_replay_stack_weights(
                        bound.lower_weight.clone(),
                        successor.lower_weight.clone(),
                    ),
                    Type::OpenVar(successor.slot),
                    compose_replay_stack_weights(
                        bound.upper_weight.clone(),
                        successor.upper_weight.clone(),
                    ),
                )?;
            }
        }
        let upper_bounds = self.slots[upper_index].upper.clone();
        let predecessors = self.slots[upper_index].weighted_predecessors.clone();
        for bound in upper_bounds {
            for predecessor in &predecessors {
                self.constrain_weighted_subtype(
                    Type::OpenVar(predecessor.slot),
                    predecessor.lower_weight.clone(),
                    bound.clone(),
                    predecessor.upper_weight.clone(),
                )?;
            }
        }
        let weighted_upper_bounds = self.slots[upper_index].weighted_upper.clone();
        let predecessors = self.slots[upper_index].weighted_predecessors.clone();
        for bound in weighted_upper_bounds {
            for predecessor in &predecessors {
                self.constrain_weighted_subtype(
                    Type::OpenVar(predecessor.slot),
                    compose_replay_stack_weights(
                        predecessor.lower_weight.clone(),
                        bound.lower_weight.clone(),
                    ),
                    bound.ty.clone(),
                    compose_replay_stack_weights(
                        predecessor.upper_weight.clone(),
                        bound.upper_weight.clone(),
                    ),
                )?;
            }
        }
        Ok(())
    }

    fn add_edge(&mut self, lower: u32, upper: u32) -> Result<(), SpecializeError> {
        self.ensure_slot(lower)?;
        self.ensure_slot(upper)?;
        if lower == upper {
            return Ok(());
        }
        let lower_index = lower as usize;
        let upper_index = upper as usize;
        if !self.slots[lower_index].successors.contains(&upper) {
            self.slots[lower_index].successors.push(upper);
        }
        if !self.slots[upper_index].predecessors.contains(&lower) {
            self.slots[upper_index].predecessors.push(lower);
        }
        let lowers = self.slots[lower_index].lower.clone();
        for bound in lowers {
            self.add_lower(upper, bound)?;
        }
        let uppers = self.slots[upper_index].upper.clone();
        for bound in uppers {
            self.add_upper(lower, bound)?;
        }
        Ok(())
    }

    fn add_lower(&mut self, slot: u32, lower: Type) -> Result<(), SpecializeError> {
        self.add_lower_weighted(slot, lower, empty_stack_weight(), empty_stack_weight())
    }

    fn add_lower_weighted(
        &mut self,
        slot: u32,
        lower: Type,
        lower_weight: StackWeight,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        if stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight) {
            return self.add_lower_unweighted(slot, lower);
        }
        if let Type::OpenVar(lower_slot) = lower {
            return self.add_weighted_edge(lower_slot, slot, lower_weight, upper_weight);
        }
        self.add_lower_bound_weighted(slot, lower, lower_weight, upper_weight)
    }

    fn add_lower_unweighted(&mut self, slot: u32, lower: Type) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        let lower = effect_slot_candidate(self.slots[index].kind, lower);
        if self.slots[index].lower.contains(&lower) {
            return Ok(());
        }
        for existing in self.slots[index].lower.clone() {
            self.constrain_same_path_invariant(existing, lower.clone())?;
        }
        self.slots[index].lower.push(lower.clone());
        let effect_consumers = self.slots[index].effect_subtraction_consumers.clone();
        for demand in effect_consumers {
            let Some((items, tail)) = self.effect_row_parts(lower.clone()) else {
                continue;
            };
            self.constrain_effect_lower_against_subtraction_demand(items, tail, &demand, false)?;
        }
        let uppers = self.slots[index].upper.clone();
        for upper in uppers {
            self.constrain_subtype(lower.clone(), upper)?;
        }
        let successors = self.slots[index].successors.clone();
        for successor in successors {
            self.add_lower_unweighted(successor, lower.clone())?;
        }
        let weighted_uppers = self.slots[index].weighted_upper.clone();
        for upper in weighted_uppers {
            self.constrain_weighted_subtype(
                lower.clone(),
                upper.lower_weight,
                upper.ty,
                upper.upper_weight,
            )?;
        }
        let weighted_successors = self.slots[index].weighted_successors.clone();
        for successor in weighted_successors {
            self.constrain_weighted_subtype(
                lower.clone(),
                successor.lower_weight,
                Type::OpenVar(successor.slot),
                successor.upper_weight,
            )?;
        }
        Ok(())
    }

    fn add_lower_bound_weighted(
        &mut self,
        slot: u32,
        lower: Type,
        lower_weight: StackWeight,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        let lower = effect_slot_candidate(self.slots[index].kind, lower);
        let bound = WeightedTypeBound {
            ty: lower.clone(),
            lower_weight,
            upper_weight,
        };
        if self.slots[index].weighted_lower.contains(&bound) {
            return Ok(());
        }
        self.slots[index].weighted_lower.push(bound.clone());

        let uppers = self.slots[index].upper.clone();
        for upper in uppers {
            self.constrain_weighted_subtype(
                lower.clone(),
                bound.lower_weight.clone(),
                upper,
                bound.upper_weight.clone(),
            )?;
        }
        let weighted_uppers = self.slots[index].weighted_upper.clone();
        for upper in weighted_uppers {
            self.constrain_weighted_subtype(
                lower.clone(),
                compose_replay_stack_weights(bound.lower_weight.clone(), upper.lower_weight),
                upper.ty,
                compose_replay_stack_weights(bound.upper_weight.clone(), upper.upper_weight),
            )?;
        }
        let successors = self.slots[index].successors.clone();
        for successor in successors {
            self.constrain_weighted_subtype(
                lower.clone(),
                bound.lower_weight.clone(),
                Type::OpenVar(successor),
                bound.upper_weight.clone(),
            )?;
        }
        let weighted_successors = self.slots[index].weighted_successors.clone();
        for successor in weighted_successors {
            self.constrain_weighted_subtype(
                lower.clone(),
                compose_replay_stack_weights(bound.lower_weight.clone(), successor.lower_weight),
                Type::OpenVar(successor.slot),
                compose_replay_stack_weights(bound.upper_weight.clone(), successor.upper_weight),
            )?;
        }
        Ok(())
    }

    fn add_upper(&mut self, slot: u32, upper: Type) -> Result<(), SpecializeError> {
        self.add_upper_weighted(slot, empty_stack_weight(), upper, empty_stack_weight())
    }

    fn add_upper_weighted(
        &mut self,
        slot: u32,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        if stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight) {
            return self.add_upper_unweighted(slot, upper);
        }
        if let Type::OpenVar(upper_slot) = upper {
            return self.add_weighted_edge(slot, upper_slot, lower_weight, upper_weight);
        }
        if self
            .slots
            .get(slot as usize)
            .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
        {
            return self.add_effect_upper_weighted(slot, lower_weight, upper, upper_weight);
        }
        self.add_upper_bound_weighted(slot, lower_weight, upper, upper_weight)
    }

    fn add_effect_upper_weighted(
        &mut self,
        slot: u32,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        if stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight) {
            return self.add_upper_unweighted(slot, upper);
        }
        let upper_row = match upper {
            Type::EffectRow(items) => items,
            item if item.is_pure_effect() => Vec::new(),
            item => vec![item],
        };
        let (items, tail) = self.split_effect_row_tail(upper_row);
        if matches!(tail, Some(Type::OpenVar(tail)) if tail == slot) {
            return Ok(());
        }
        if items.is_empty() && tail.is_none() {
            return self.add_upper_unweighted(slot, Type::pure_effect());
        }
        let combined_weight = compose_stack_weights(lower_weight, upper_weight);
        let retained = items
            .iter()
            .filter(|item| stack_weight_allows_effect_item(&combined_weight, item))
            .cloned()
            .collect::<Vec<_>>();
        let tail = tail.unwrap_or_else(Type::pure_effect);
        if retained.is_empty() {
            return self.constrain_weighted_subtype(
                Type::OpenVar(slot),
                combined_weight,
                tail,
                empty_stack_weight(),
            );
        }
        let retained_families = sorted_effect_families(effect_families_from_items(&retained));
        let residual_weight = subtract_stack_weight(combined_weight, &retained_families);
        let key = RowResidualKey {
            source: slot,
            retained_families,
            weight: residual_weight.clone(),
        };
        let residual = if let Some(residual) = self.row_residuals.get(&key).copied() {
            Type::OpenVar(residual)
        } else {
            let residual = self.fresh_effect();
            let Type::OpenVar(residual_slot) = residual else {
                unreachable!("fresh_effect returns an open slot");
            };
            self.row_residuals.insert(key, residual_slot);
            residual
        };
        let mut upper_items = retained;
        upper_items.push(residual.clone());
        self.constrain_subtype(Type::OpenVar(slot), Type::EffectRow(upper_items))?;
        self.constrain_weighted_subtype(residual, residual_weight, tail, empty_stack_weight())
    }

    fn add_upper_bound_weighted(
        &mut self,
        slot: u32,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        let upper = effect_slot_candidate(self.slots[index].kind, upper);
        let bound = WeightedTypeBound {
            ty: upper.clone(),
            lower_weight,
            upper_weight,
        };
        if self.slots[index].weighted_upper.contains(&bound) {
            return Ok(());
        }
        self.slots[index].weighted_upper.push(bound.clone());

        let lowers = self.slots[index].lower.clone();
        for lower in lowers {
            self.constrain_weighted_subtype(
                lower,
                bound.lower_weight.clone(),
                upper.clone(),
                bound.upper_weight.clone(),
            )?;
        }
        let weighted_lowers = self.slots[index].weighted_lower.clone();
        for lower in weighted_lowers {
            self.constrain_weighted_subtype(
                lower.ty,
                compose_replay_stack_weights(lower.lower_weight, bound.lower_weight.clone()),
                upper.clone(),
                compose_replay_stack_weights(lower.upper_weight, bound.upper_weight.clone()),
            )?;
        }
        let predecessors = self.slots[index].predecessors.clone();
        for predecessor in predecessors {
            self.constrain_weighted_subtype(
                Type::OpenVar(predecessor),
                bound.lower_weight.clone(),
                upper.clone(),
                bound.upper_weight.clone(),
            )?;
        }
        let weighted_predecessors = self.slots[index].weighted_predecessors.clone();
        for predecessor in weighted_predecessors {
            self.constrain_weighted_subtype(
                Type::OpenVar(predecessor.slot),
                compose_replay_stack_weights(predecessor.lower_weight, bound.lower_weight.clone()),
                upper.clone(),
                compose_replay_stack_weights(predecessor.upper_weight, bound.upper_weight.clone()),
            )?;
        }
        Ok(())
    }

    fn add_upper_unweighted(&mut self, slot: u32, upper: Type) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        let upper = effect_slot_candidate(self.slots[index].kind, upper);
        if self.slots[index].upper.contains(&upper) {
            return Ok(());
        }
        for existing in self.slots[index].upper.clone() {
            self.constrain_same_path_invariant(existing, upper.clone())?;
        }
        self.slots[index].upper.push(upper.clone());
        let lowers = self.slots[index].lower.clone();
        for lower in lowers {
            self.constrain_subtype(lower, upper.clone())?;
        }
        let weighted_lowers = self.slots[index].weighted_lower.clone();
        for lower in weighted_lowers {
            self.constrain_weighted_subtype(
                lower.ty,
                lower.lower_weight,
                upper.clone(),
                lower.upper_weight,
            )?;
        }
        let predecessors = self.slots[index].predecessors.clone();
        for predecessor in predecessors {
            self.add_upper_unweighted(predecessor, upper.clone())?;
        }
        let weighted_predecessors = self.slots[index].weighted_predecessors.clone();
        for predecessor in weighted_predecessors {
            self.constrain_weighted_subtype(
                Type::OpenVar(predecessor.slot),
                predecessor.lower_weight,
                upper.clone(),
                predecessor.upper_weight,
            )?;
        }
        Ok(())
    }

    fn ensure_slot(&self, slot: u32) -> Result<(), SpecializeError> {
        if (slot as usize) < self.slots.len() {
            Ok(())
        } else {
            Err(SpecializeError::InvalidTypeSlot { slot })
        }
    }

    fn constrain_same_path_invariant(
        &mut self,
        left: Type,
        right: Type,
    ) -> Result<(), SpecializeError> {
        if let (Type::EffectRow(left_items), Type::EffectRow(right_items)) = (&left, &right) {
            for left in left_items {
                for right in right_items {
                    if same_effect_row_family(left, right) {
                        self.constrain_same_path_invariant(left.clone(), right.clone())?;
                    }
                }
            }
            return Ok(());
        }
        if let (
            Type::Stack {
                inner: left_inner,
                weight: left_weight,
            },
            Type::Stack {
                inner: right_inner,
                weight: right_weight,
            },
        ) = (&left, &right)
            && left_weight == right_weight
        {
            self.constrain_subtype(left_inner.as_ref().clone(), right_inner.as_ref().clone())?;
            self.constrain_subtype(right_inner.as_ref().clone(), left_inner.as_ref().clone())?;
            return Ok(());
        }
        let (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) = (left, right)
        else {
            return Ok(());
        };
        if left_path != right_path || left_args.len() != right_args.len() {
            return Ok(());
        }
        for (left, right) in left_args.into_iter().zip(right_args) {
            self.constrain_subtype(left.clone(), right.clone())?;
            self.constrain_subtype(right, left)?;
        }
        Ok(())
    }

    fn solve_slots(&self) -> Result<Solution, SpecializeError> {
        let mut solution = Solution {
            slots: vec![None; self.slots.len()],
        };
        loop {
            let mut progressed = false;
            for slot in 0..self.slots.len() {
                if solution.slots[slot].is_some() {
                    continue;
                }
                let mut resolver = TypeResolver::new(self, &solution);
                if let Some(ty) = resolver.try_slot_solution(slot as u32)? {
                    solution.slots[slot] = Some(ty);
                    progressed = true;
                }
            }
            if !progressed {
                return Ok(solution);
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeSlotKind {
    Value,
    Effect,
}

fn effect_slot_candidate(slot_kind: TypeSlotKind, ty: Type) -> Type {
    if slot_kind != TypeSlotKind::Effect || matches!(ty, Type::EffectRow(_)) {
        return ty;
    }
    if ty.is_pure_effect() {
        return Type::pure_effect();
    }
    Type::EffectRow(vec![ty])
}

fn effect_candidate_items(ty: Type) -> Option<Vec<Type>> {
    match ty {
        Type::EffectRow(items) => Some(items),
        ty if ty.is_pure_effect() => Some(Vec::new()),
        ty @ Type::Con { .. } => Some(vec![ty]),
        _ => None,
    }
}

#[derive(Debug, Clone)]
struct TypeSlot {
    kind: TypeSlotKind,
    lower: Vec<Type>,
    upper: Vec<Type>,
    weighted_lower: Vec<WeightedTypeBound>,
    weighted_upper: Vec<WeightedTypeBound>,
    successors: Vec<u32>,
    predecessors: Vec<u32>,
    weighted_successors: Vec<WeightedSlotEdge>,
    weighted_predecessors: Vec<WeightedSlotEdge>,
    effect_subtraction_consumers: Vec<EffectSubtractionDemand>,
}

impl TypeSlot {
    fn new(kind: TypeSlotKind) -> Self {
        Self {
            kind,
            lower: Vec::new(),
            upper: Vec::new(),
            weighted_lower: Vec::new(),
            weighted_upper: Vec::new(),
            successors: Vec::new(),
            predecessors: Vec::new(),
            weighted_successors: Vec::new(),
            weighted_predecessors: Vec::new(),
            effect_subtraction_consumers: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SubtypeConstraint {
    lower: Type,
    lower_weight: StackWeight,
    upper: Type,
    upper_weight: StackWeight,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct WeightedTypeBound {
    ty: Type,
    lower_weight: StackWeight,
    upper_weight: StackWeight,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct WeightedSlotEdge {
    slot: u32,
    lower_weight: StackWeight,
    upper_weight: StackWeight,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RowResidualKey {
    source: u32,
    retained_families: Vec<EffectFamily>,
    weight: StackWeight,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct EffectSubtractionDemand {
    tail: Type,
    runtime_effect: Type,
    handled_items: Vec<Type>,
}

struct Solution {
    slots: Vec<Option<Type>>,
}

struct TypeResolver<'a, 'solution> {
    graph: &'a TypeGraph<'a>,
    solution: &'solution Solution,
    resolving: HashSet<u32>,
}

impl<'a, 'solution> TypeResolver<'a, 'solution> {
    fn new(graph: &'a TypeGraph<'a>, solution: &'solution Solution) -> Self {
        Self {
            graph,
            solution,
            resolving: HashSet::new(),
        }
    }

    fn resolve(&mut self, ty: &Type) -> Result<Type, SpecializeError> {
        match ty {
            Type::Any | Type::Never => Ok(ty.clone()),
            Type::OpenVar(slot) => self.slot_solution(*slot),
            Type::Con { path, args } => Ok(Type::Con {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.resolve(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => Ok(Type::Fun {
                arg: Box::new(self.resolve(arg)?),
                arg_effect: Box::new(self.resolve(arg_effect)?),
                ret_effect: Box::new(self.resolve(ret_effect)?),
                ret: Box::new(self.resolve(ret)?),
            }),
            Type::Thunk { effect, value } => {
                let effect = self.resolve(effect)?;
                let value = self.resolve(value)?;
                Ok(types::runtime_shape(effect, value))
            }
            Type::Record(fields) => Ok(Type::Record(
                fields
                    .iter()
                    .map(|field| {
                        Ok(TypeField {
                            name: field.name.clone(),
                            value: self.resolve(&field.value)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            )),
            Type::PolyVariant(variants) => Ok(Type::PolyVariant(
                variants
                    .iter()
                    .map(|variant| {
                        Ok(TypeVariant {
                            name: variant.name.clone(),
                            payloads: variant
                                .payloads
                                .iter()
                                .map(|payload| self.resolve(payload))
                                .collect::<Result<Vec<_>, _>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            )),
            Type::Tuple(items) => Ok(Type::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve(item))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Type::EffectRow(items) => Ok(types::simplify_type(Type::EffectRow(
                items
                    .iter()
                    .map(|item| self.resolve_effect_item(item))
                    .collect::<Result<Vec<_>, _>>()?,
            ))),
            Type::Stack { inner, weight } => {
                let resolved = types::simplify_stack_type(self.resolve(inner)?, weight.clone());
                if matches!(resolved, Type::Stack { .. }) {
                    return Err(SpecializeError::UnresolvedStackWeight { ty: resolved });
                }
                Ok(resolved)
            }
            Type::Union(left, right) => {
                join_type_candidates(self.graph, self.resolve(left)?, self.resolve(right)?)
            }
            Type::Intersection(left, right) => {
                meet_type_candidates(self.graph, self.resolve(left)?, self.resolve(right)?)
            }
        }
    }

    fn resolve_with_context(&mut self, ty: &Type, context: &Type) -> Result<Type, SpecializeError> {
        match self.resolve(ty) {
            Ok(resolved) if type_contains_open_var(&resolved) => {
                self.resolve_from_context(&resolved, context, true)
            }
            Ok(ty) => Ok(ty),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => {
                self.resolve_from_context(ty, context, false)
            }
            Err(error) => Err(error),
        }
    }

    fn resolve_with_context_leaf(
        &mut self,
        ty: &Type,
        context: &Type,
    ) -> Result<Type, SpecializeError> {
        match self.resolve(ty) {
            Ok(resolved) if type_contains_open_var(&resolved) => {
                self.resolve_from_context(&resolved, context, true)
            }
            Ok(ty) => Ok(ty),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => {
                self.resolve_from_context(ty, context, true)
            }
            Err(error) => Err(error),
        }
    }

    fn resolve_from_context(
        &mut self,
        ty: &Type,
        context: &Type,
        allow_leaf: bool,
    ) -> Result<Type, SpecializeError> {
        if let Type::OpenVar(slot) = ty {
            return match self.solution.slots.get(*slot as usize) {
                Some(Some(solution)) => {
                    let solution = solution.clone();
                    self.resolve_from_context(&solution, context, allow_leaf)
                }
                Some(None) if allow_leaf => self.resolve(context),
                Some(None) => Err(SpecializeError::UndeterminedTypeSlot { slot: *slot }),
                None => Err(SpecializeError::InvalidTypeSlot { slot: *slot }),
            };
        }
        match (ty, context) {
            (
                Type::Con { path, args },
                Type::Con {
                    path: context_path,
                    args: context_args,
                },
            ) if path == context_path && args.len() == context_args.len() => Ok(Type::Con {
                path: path.clone(),
                args: args
                    .iter()
                    .zip(context_args.iter())
                    .map(|(arg, context)| self.resolve_with_context_leaf(arg, context))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            (
                Type::Fun {
                    arg,
                    arg_effect,
                    ret_effect,
                    ret,
                },
                Type::Fun {
                    arg: context_arg,
                    arg_effect: context_arg_effect,
                    ret_effect: context_ret_effect,
                    ret: context_ret,
                },
            ) => Ok(Type::Fun {
                arg: Box::new(self.resolve_with_context_leaf(arg, context_arg)?),
                arg_effect: Box::new(
                    self.resolve_with_context_leaf(arg_effect, context_arg_effect)?,
                ),
                ret_effect: Box::new(
                    self.resolve_with_context_leaf(ret_effect, context_ret_effect)?,
                ),
                ret: Box::new(self.resolve_with_context_leaf(ret, context_ret)?),
            }),
            (
                Type::Thunk { effect, value },
                Type::Thunk {
                    effect: context_effect,
                    value: context_value,
                },
            ) => Ok(types::runtime_shape(
                self.resolve_with_context_leaf(effect, context_effect)?,
                self.resolve_with_context_leaf(value, context_value)?,
            )),
            (Type::Tuple(items), Type::Tuple(context_items))
                if items.len() == context_items.len() =>
            {
                Ok(Type::Tuple(
                    items
                        .iter()
                        .zip(context_items.iter())
                        .map(|(item, context)| self.resolve_with_context_leaf(item, context))
                        .collect::<Result<Vec<_>, _>>()?,
                ))
            }
            (Type::Record(fields), Type::Record(context_fields)) => Ok(Type::Record(
                fields
                    .iter()
                    .map(|field| {
                        let context = record_field_type(&context_fields, &field.name)
                            .map(|field| &field.value)
                            .unwrap_or(&field.value);
                        Ok(TypeField {
                            name: field.name.clone(),
                            value: self.resolve_with_context_leaf(&field.value, context)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            )),
            (Type::PolyVariant(variants), Type::PolyVariant(context_variants)) => {
                Ok(Type::PolyVariant(
                    variants
                        .iter()
                        .map(|variant| {
                            let context = context_variants.iter().find(|context| {
                                context.name == variant.name
                                    && context.payloads.len() == variant.payloads.len()
                            });
                            let payloads = match context {
                                Some(context) => variant
                                    .payloads
                                    .iter()
                                    .zip(context.payloads.iter())
                                    .map(|(payload, context)| {
                                        self.resolve_with_context_leaf(payload, context)
                                    })
                                    .collect::<Result<Vec<_>, _>>()?,
                                None => self.resolve_partial_candidates(&variant.payloads)?,
                            };
                            Ok(TypeVariant {
                                name: variant.name.clone(),
                                payloads,
                            })
                        })
                        .collect::<Result<Vec<_>, SpecializeError>>()?,
                ))
            }
            (Type::EffectRow(items), Type::EffectRow(context_items)) => {
                let mut resolved = Vec::with_capacity(items.len());
                for item in items {
                    let context = context_items
                        .iter()
                        .find(|context| same_effect_row_family(item, context))
                        .unwrap_or(item);
                    resolved.push(self.resolve_with_context_leaf(item, context)?);
                }
                Ok(types::simplify_type(Type::EffectRow(resolved)))
            }
            (Type::Stack { inner, weight }, Type::Stack { inner: context, .. }) => {
                Ok(types::simplify_stack_type(
                    self.resolve_with_context_leaf(inner, context)?,
                    weight.clone(),
                ))
            }
            (Type::Union(left, right), context) => join_type_candidates(
                self.graph,
                self.resolve_with_context_leaf(left, &context)?,
                self.resolve_with_context_leaf(right, &context)?,
            ),
            (Type::Intersection(left, right), context) => meet_type_candidates(
                self.graph,
                self.resolve_with_context_leaf(left, &context)?,
                self.resolve_with_context_leaf(right, &context)?,
            ),
            _ => self.resolve(ty),
        }
    }

    fn resolve_effect_item(&mut self, item: &Type) -> Result<Type, SpecializeError> {
        let Type::Con { path, args } = item else {
            return self.resolve(item);
        };
        Ok(Type::Con {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| self.resolve(arg))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    fn slot_solution(&mut self, slot: u32) -> Result<Type, SpecializeError> {
        let ty = match self.solution.slots.get(slot as usize) {
            Some(Some(ty)) => ty.clone(),
            Some(None) => return Err(SpecializeError::UndeterminedTypeSlot { slot }),
            None => return Err(SpecializeError::InvalidTypeSlot { slot }),
        };
        if !self.resolving.insert(slot) {
            return Ok(ty);
        }
        let resolved = self.resolve(&ty);
        self.resolving.remove(&slot);
        resolved
    }

    fn try_slot_solution(&mut self, slot: u32) -> Result<Option<Type>, SpecializeError> {
        if !self.resolving.insert(slot) {
            return Ok(None);
        }
        let slot_data = self
            .graph
            .slots
            .get(slot as usize)
            .ok_or(SpecializeError::InvalidTypeSlot { slot })?;
        let solution = self.compute_slot_solution(slot, slot_data)?;
        self.resolving.remove(&slot);
        Ok(solution)
    }

    fn compute_slot_solution(
        &mut self,
        slot: u32,
        slot_data: &TypeSlot,
    ) -> Result<Option<Type>, SpecializeError> {
        let mut lower = self.join_bounds(slot_data.kind, &slot_data.lower)?;
        for bound in &slot_data.weighted_lower {
            let Some(bound) = self.resolve_weight_inert_bound_candidate(bound)? else {
                continue;
            };
            let bound = effect_slot_candidate(slot_data.kind, bound);
            lower = Some(match lower {
                Some(existing) => join_type_candidates(self.graph, existing, bound)?,
                None => bound,
            });
        }
        for predecessor in &slot_data.predecessors {
            let Some(predecessor) = self.try_slot_solution(*predecessor)? else {
                continue;
            };
            let predecessor = effect_slot_candidate(slot_data.kind, predecessor);
            lower = Some(match lower {
                Some(existing) => join_type_candidates(self.graph, existing, predecessor)?,
                None => predecessor,
            });
        }
        let mut upper = self.meet_bounds(slot_data.kind, &slot_data.upper)?;
        for bound in &slot_data.weighted_upper {
            let Some(bound) = self.resolve_weight_inert_bound_candidate(bound)? else {
                continue;
            };
            let bound = effect_slot_candidate(slot_data.kind, bound);
            upper = Some(match upper {
                Some(existing) => meet_type_candidates(self.graph, existing, bound)?,
                None => bound,
            });
        }
        for successor in &slot_data.successors {
            let Some(successor) = self.try_slot_solution(*successor)? else {
                continue;
            };
            let successor = effect_slot_candidate(slot_data.kind, successor);
            upper = Some(match upper {
                Some(existing) => meet_type_candidates(self.graph, existing, successor)?,
                None => successor,
            });
        }
        let candidate = match (lower, upper) {
            (Some(lower), Some(upper))
                if value_candidate_subtype_thunk(self.graph, &lower, &upper) =>
            {
                Some(lower)
            }
            (Some(lower), Some(upper))
                if thunk_value_candidate_subtype(self.graph, &lower, &upper) =>
            {
                Some(lower)
            }
            (Some(lower), Some(upper)) if slot_data.kind == TypeSlotKind::Effect => {
                if type_candidate_subtype(self.graph, &lower, &upper) {
                    Some(lower)
                } else if let Some(refined) =
                    refine_effect_lower_with_upper(self.graph, &lower, &upper)?
                {
                    Some(refined)
                } else if effect_rows_have_same_families(self.graph, &lower, &upper) {
                    Some(meet_type_candidates(self.graph, lower, upper)?)
                } else {
                    Err(SpecializeError::ConflictingTypeCandidates {
                        slot,
                        existing: lower,
                        incoming: upper,
                    })?
                }
            }
            (Some(Type::OpenVar(_)), Some(upper)) => Some(upper),
            (Some(lower), Some(Type::OpenVar(_))) => Some(lower),
            (Some(lower), Some(upper)) if type_candidate_subtype(self.graph, &lower, &upper) => {
                Some(upper)
            }
            (Some(lower), Some(upper)) if type_candidate_subtype(self.graph, &upper, &lower) => {
                Some(lower)
            }
            (Some(lower), Some(upper)) if lower == upper => Some(lower),
            (Some(lower), Some(upper)) if same_candidate_head(&lower, &upper) => {
                Some(prefer_more_resolved_candidate(lower, upper))
            }
            (Some(lower), Some(upper)) => Err(SpecializeError::ConflictingTypeCandidates {
                slot,
                existing: lower,
                incoming: upper,
            })?,
            (Some(lower), None) => Some(lower),
            (None, Some(_)) if slot_data.kind == TypeSlotKind::Effect => Some(Type::pure_effect()),
            (None, Some(upper)) => Some(upper),
            (None, None) => None,
        };
        self.erase_stack_solution_candidate(candidate)
    }

    fn erase_stack_solution_candidate(
        &mut self,
        candidate: Option<Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(candidate) = candidate else {
            return Ok(None);
        };
        self.erase_stack_type_candidate(candidate)
    }

    fn erase_stack_type_candidate(
        &mut self,
        candidate: Type,
    ) -> Result<Option<Type>, SpecializeError> {
        match candidate {
            Type::Stack { inner, weight } => {
                let Some(inner) = self.resolve_partial_candidate(&inner, false)? else {
                    return Ok(None);
                };
                let candidate = types::simplify_stack_type(inner, weight);
                if matches!(candidate, Type::Stack { .. }) {
                    Ok(None)
                } else {
                    self.erase_stack_type_candidate(candidate)
                }
            }
            Type::Con { path, args } => {
                let Some(args) = self.erase_stack_type_candidates(args)? else {
                    return Ok(None);
                };
                Ok(Some(Type::Con { path, args }))
            }
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => {
                let Some(arg) = self.erase_stack_type_candidate(*arg)? else {
                    return Ok(None);
                };
                let Some(arg_effect) = self.erase_stack_type_candidate(*arg_effect)? else {
                    return Ok(None);
                };
                let Some(ret_effect) = self.erase_stack_type_candidate(*ret_effect)? else {
                    return Ok(None);
                };
                let Some(ret) = self.erase_stack_type_candidate(*ret)? else {
                    return Ok(None);
                };
                Ok(Some(Type::Fun {
                    arg: Box::new(arg),
                    arg_effect: Box::new(arg_effect),
                    ret_effect: Box::new(ret_effect),
                    ret: Box::new(ret),
                }))
            }
            Type::Thunk { effect, value } => {
                let Some(effect) = self.erase_stack_type_candidate(*effect)? else {
                    return Ok(None);
                };
                let Some(value) = self.erase_stack_type_candidate(*value)? else {
                    return Ok(None);
                };
                Ok(Some(types::runtime_shape(effect, value)))
            }
            Type::Record(fields) => {
                let mut out = Vec::with_capacity(fields.len());
                for field in fields {
                    let Some(value) = self.erase_stack_type_candidate(field.value)? else {
                        return Ok(None);
                    };
                    out.push(TypeField {
                        name: field.name,
                        value,
                        optional: field.optional,
                    });
                }
                Ok(Some(Type::Record(out)))
            }
            Type::PolyVariant(variants) => {
                let mut out = Vec::with_capacity(variants.len());
                for variant in variants {
                    let Some(payloads) = self.erase_stack_type_candidates(variant.payloads)? else {
                        return Ok(None);
                    };
                    out.push(TypeVariant {
                        name: variant.name,
                        payloads,
                    });
                }
                Ok(Some(Type::PolyVariant(out)))
            }
            Type::Tuple(items) => {
                let Some(items) = self.erase_stack_type_candidates(items)? else {
                    return Ok(None);
                };
                Ok(Some(Type::Tuple(items)))
            }
            Type::EffectRow(items) => {
                let Some(items) = self.erase_stack_type_candidates(items)? else {
                    return Ok(None);
                };
                Ok(Some(types::simplify_type(Type::EffectRow(items))))
            }
            Type::Union(left, right) => {
                let left = self.erase_stack_type_candidate(*left)?;
                let right = self.erase_stack_type_candidate(*right)?;
                match (left, right) {
                    (Some(left), Some(right)) => {
                        Ok(Some(join_type_candidates(self.graph, left, right)?))
                    }
                    (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                }
            }
            Type::Intersection(left, right) => {
                let left = self.erase_stack_type_candidate(*left)?;
                let right = self.erase_stack_type_candidate(*right)?;
                match (left, right) {
                    (Some(left), Some(right)) => {
                        Ok(Some(meet_type_candidates(self.graph, left, right)?))
                    }
                    (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                }
            }
            Type::Any | Type::Never | Type::OpenVar(_) => Ok(Some(candidate)),
        }
    }

    fn erase_stack_type_candidates(
        &mut self,
        items: Vec<Type>,
    ) -> Result<Option<Vec<Type>>, SpecializeError> {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            let Some(item) = self.erase_stack_type_candidate(item)? else {
                return Ok(None);
            };
            out.push(item);
        }
        Ok(Some(out))
    }

    fn resolve_weight_inert_bound_candidate(
        &mut self,
        bound: &WeightedTypeBound,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(ty) = self.resolve_candidate(&bound.ty)? else {
            return Ok(None);
        };
        if stack_weight_cannot_affect_type(&ty) {
            Ok(Some(ty))
        } else {
            Ok(None)
        }
    }

    fn join_bounds(
        &mut self,
        slot_kind: TypeSlotKind,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut out = None;
        for bound in bounds {
            let Some(bound) = self.resolve_candidate(bound)? else {
                continue;
            };
            if type_contains_stack(&bound) {
                continue;
            }
            let bound = effect_slot_candidate(slot_kind, bound);
            out = Some(match out {
                Some(existing) => join_type_candidates(self.graph, existing, bound)?,
                None => bound,
            });
        }
        Ok(out)
    }

    fn meet_bounds(
        &mut self,
        slot_kind: TypeSlotKind,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut out = None;
        for bound in bounds {
            let Some(bound) = self.resolve_candidate(bound)? else {
                continue;
            };
            if type_contains_stack(&bound) {
                continue;
            }
            let bound = effect_slot_candidate(slot_kind, bound);
            out = Some(match out {
                Some(existing) => meet_type_candidates(self.graph, existing, bound)?,
                None => bound,
            });
        }
        Ok(out)
    }

    fn resolve_candidate(&mut self, ty: &Type) -> Result<Option<Type>, SpecializeError> {
        self.resolve_partial_candidate(ty, false)
    }

    fn resolve_partial_candidate(
        &mut self,
        ty: &Type,
        allow_unresolved_leaf: bool,
    ) -> Result<Option<Type>, SpecializeError> {
        match ty {
            Type::Any | Type::Never => Ok(Some(ty.clone())),
            Type::OpenVar(slot) => {
                let Some(solution) = self.solution.slots.get(*slot as usize) else {
                    return Err(SpecializeError::InvalidTypeSlot { slot: *slot });
                };
                let Some(ty) = solution else {
                    return if allow_unresolved_leaf {
                        Ok(Some(Type::OpenVar(*slot)))
                    } else {
                        Ok(None)
                    };
                };
                if !self.resolving.insert(*slot) {
                    return if allow_unresolved_leaf {
                        Ok(Some(Type::OpenVar(*slot)))
                    } else {
                        Ok(None)
                    };
                }
                let resolved = self.resolve_partial_candidate(ty, allow_unresolved_leaf);
                self.resolving.remove(slot);
                resolved
            }
            Type::Con { path, args } => Ok(Some(Type::Con {
                path: path.clone(),
                args: self.resolve_partial_candidates(args)?,
            })),
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => Ok(Some(Type::Fun {
                arg: Box::new(
                    self.resolve_partial_candidate(arg, true)?
                        .unwrap_or_else(|| arg.as_ref().clone()),
                ),
                arg_effect: Box::new(
                    self.resolve_partial_candidate(arg_effect, true)?
                        .unwrap_or_else(|| arg_effect.as_ref().clone()),
                ),
                ret_effect: Box::new(
                    self.resolve_partial_candidate(ret_effect, true)?
                        .unwrap_or_else(|| ret_effect.as_ref().clone()),
                ),
                ret: Box::new(
                    self.resolve_partial_candidate(ret, true)?
                        .unwrap_or_else(|| ret.as_ref().clone()),
                ),
            })),
            Type::Thunk { effect, value } => Ok(Some(types::runtime_shape(
                self.resolve_partial_candidate(effect, true)?
                    .unwrap_or_else(|| effect.as_ref().clone()),
                self.resolve_partial_candidate(value, true)?
                    .unwrap_or_else(|| value.as_ref().clone()),
            ))),
            Type::Record(fields) => Ok(Some(Type::Record(
                fields
                    .iter()
                    .map(|field| {
                        Ok(TypeField {
                            name: field.name.clone(),
                            value: self
                                .resolve_partial_candidate(&field.value, true)?
                                .unwrap_or_else(|| field.value.clone()),
                            optional: field.optional,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            ))),
            Type::PolyVariant(variants) => Ok(Some(Type::PolyVariant(
                variants
                    .iter()
                    .map(|variant| {
                        Ok(TypeVariant {
                            name: variant.name.clone(),
                            payloads: self.resolve_partial_candidates(&variant.payloads)?,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecializeError>>()?,
            ))),
            Type::Tuple(items) => Ok(Some(Type::Tuple(self.resolve_partial_candidates(items)?))),
            Type::EffectRow(items) => Ok(Some(types::simplify_type(Type::EffectRow(
                self.resolve_partial_candidates(items)?,
            )))),
            Type::Stack { inner, weight } => {
                let Some(inner) = self.resolve_partial_candidate(inner, allow_unresolved_leaf)?
                else {
                    return Ok(None);
                };
                let candidate = types::simplify_stack_type(inner, weight.clone());
                if type_contains_stack(&candidate) {
                    Ok(None)
                } else {
                    Ok(Some(candidate))
                }
            }
            Type::Union(left, right) => {
                let left = self.resolve_partial_candidate(left, true)?;
                let right = self.resolve_partial_candidate(right, true)?;
                match (left, right) {
                    (Some(left), Some(right)) => {
                        Ok(Some(join_type_candidates(self.graph, left, right)?))
                    }
                    (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                }
            }
            Type::Intersection(left, right) => {
                let left = self.resolve_partial_candidate(left, true)?;
                let right = self.resolve_partial_candidate(right, true)?;
                match (left, right) {
                    (Some(left), Some(right)) => {
                        Ok(Some(meet_type_candidates(self.graph, left, right)?))
                    }
                    (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                }
            }
        }
    }

    fn resolve_partial_candidates(&mut self, items: &[Type]) -> Result<Vec<Type>, SpecializeError> {
        items
            .iter()
            .map(|item| {
                let fallback = item.clone();
                self.resolve_partial_candidate(item, true)
                    .map(|resolved| resolved.unwrap_or(fallback))
            })
            .collect()
    }
}

fn join_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    match (&left, &right) {
        (Type::Record(_), Type::Record(_)) => {
            return join_record_type_candidates(graph, left, right);
        }
        (Type::PolyVariant(_), Type::PolyVariant(_)) => {
            return join_poly_variant_type_candidates(graph, left, right);
        }
        (Type::EffectRow(_), Type::EffectRow(_)) => {
            let (Type::EffectRow(left), Type::EffectRow(right)) = (left, right) else {
                unreachable!("effect row candidates checked by caller");
            };
            return merge_effect_row_candidates(graph, left, right, CandidateMerge::Join);
        }
        (Type::EffectRow(_), _) | (_, Type::EffectRow(_)) => {
            let left_items = effect_candidate_items(left.clone());
            let right_items = effect_candidate_items(right.clone());
            if let (Some(left), Some(right)) = (left_items, right_items) {
                return merge_effect_row_candidates(graph, left, right, CandidateMerge::Join);
            }
        }
        _ => {}
    }
    if left == right || type_candidate_subtype(graph, &right, &left) {
        return Ok(left);
    }
    if type_candidate_subtype(graph, &left, &right) {
        return Ok(right);
    }
    match (left, right) {
        (Type::OpenVar(_), right) => Ok(right),
        (left, Type::OpenVar(_)) => Ok(left),
        (Type::Never, right) => Ok(right),
        (left, Type::Never) => Ok(left),
        (left, right) if left.is_pure_effect() && right.is_pure_effect() => Ok(Type::pure_effect()),
        (
            Type::Thunk {
                effect: left_effect,
                value: left_value,
            },
            Type::Thunk {
                effect: right_effect,
                value: right_value,
            },
        ) => Ok(types::runtime_shape(
            join_type_candidates(graph, *left_effect, *right_effect)?,
            join_type_candidates(graph, *left_value, *right_value)?,
        )),
        (Type::Thunk { effect, value }, right) => Ok(types::runtime_shape(
            *effect,
            join_type_candidates(graph, *value, right)?,
        )),
        (left, Type::Thunk { effect, value }) => Ok(types::runtime_shape(
            *effect,
            join_type_candidates(graph, left, *value)?,
        )),
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if left_path == right_path && left_args.len() == right_args.len() => {
            merge_same_head_con_candidate(
                graph,
                left_path,
                left_args,
                right_args,
                CandidateMerge::Join,
            )
        }
        (
            Type::Fun {
                arg: left_arg,
                arg_effect: left_arg_effect,
                ret_effect: left_ret_effect,
                ret: left_ret,
            },
            Type::Fun { .. },
        ) => Ok(Type::Fun {
            arg: left_arg,
            arg_effect: left_arg_effect,
            ret_effect: left_ret_effect,
            ret: left_ret,
        }),
        (Type::EffectRow(left), Type::EffectRow(right)) => {
            merge_effect_row_candidates(graph, left, right, CandidateMerge::Join)
        }
        (
            Type::Stack {
                inner: left,
                weight,
            },
            Type::Stack {
                inner: right,
                weight: right_weight,
            },
        ) if weight == right_weight => Ok(types::simplify_stack_type(
            join_type_candidates(graph, *left, *right)?,
            weight,
        )),
        (left, right) => Err(SpecializeError::ConflictingTypeCandidates {
            slot: 0,
            existing: left,
            incoming: right,
        }),
    }
}

fn meet_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    match (&left, &right) {
        (Type::Record(_), Type::Record(_)) => {
            return meet_record_type_candidates(graph, left, right);
        }
        (Type::PolyVariant(_), Type::PolyVariant(_)) => {
            return meet_poly_variant_type_candidates(graph, left, right);
        }
        (Type::EffectRow(_), Type::EffectRow(_)) => {
            let (Type::EffectRow(left), Type::EffectRow(right)) = (left, right) else {
                unreachable!("effect row candidates checked by caller");
            };
            return merge_effect_row_candidates(graph, left, right, CandidateMerge::Meet);
        }
        (Type::EffectRow(_), _) | (_, Type::EffectRow(_)) => {
            let left_items = effect_candidate_items(left.clone());
            let right_items = effect_candidate_items(right.clone());
            if let (Some(left), Some(right)) = (left_items, right_items) {
                return merge_effect_row_candidates(graph, left, right, CandidateMerge::Meet);
            }
        }
        _ => {}
    }
    if left == right || type_candidate_subtype(graph, &left, &right) {
        return Ok(left);
    }
    if type_candidate_subtype(graph, &right, &left) {
        return Ok(right);
    }
    match (left, right) {
        (Type::OpenVar(_), right) => Ok(right),
        (left, Type::OpenVar(_)) => Ok(left),
        (Type::Any, right) => Ok(right),
        (left, Type::Any) => Ok(left),
        (left, right) if left.is_pure_effect() && right.is_pure_effect() => Ok(Type::pure_effect()),
        (
            Type::Thunk {
                effect: left_effect,
                value: left_value,
            },
            Type::Thunk {
                effect: right_effect,
                value: right_value,
            },
        ) => Ok(types::runtime_shape(
            meet_type_candidates(graph, *left_effect, *right_effect)?,
            meet_type_candidates(graph, *left_value, *right_value)?,
        )),
        (Type::Thunk { value, .. }, right) => meet_type_candidates(graph, *value, right),
        (left, Type::Thunk { value, .. }) => meet_type_candidates(graph, left, *value),
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if left_path == right_path && left_args.len() == right_args.len() => {
            merge_same_head_con_candidate(
                graph,
                left_path,
                left_args,
                right_args,
                CandidateMerge::Meet,
            )
        }
        (
            Type::Fun {
                arg: left_arg,
                arg_effect: left_arg_effect,
                ret_effect: left_ret_effect,
                ret: left_ret,
            },
            Type::Fun { .. },
        ) => Ok(Type::Fun {
            arg: left_arg,
            arg_effect: left_arg_effect,
            ret_effect: left_ret_effect,
            ret: left_ret,
        }),
        (Type::EffectRow(left), Type::EffectRow(right)) => {
            merge_effect_row_candidates(graph, left, right, CandidateMerge::Meet)
        }
        (
            Type::Stack {
                inner: left,
                weight,
            },
            Type::Stack {
                inner: right,
                weight: right_weight,
            },
        ) if weight == right_weight => Ok(types::simplify_stack_type(
            meet_type_candidates(graph, *left, *right)?,
            weight,
        )),
        (left, right) => Err(SpecializeError::ConflictingTypeCandidates {
            slot: 0,
            existing: left,
            incoming: right,
        }),
    }
}

fn join_record_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::Record(left_fields), Type::Record(right_fields)) = (left, right) else {
        unreachable!("record candidates checked by caller");
    };
    merge_record_type_candidates(graph, left_fields, right_fields, RecordMerge::Join)
        .map(Type::Record)
}

fn meet_record_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::Record(left_fields), Type::Record(right_fields)) = (left, right) else {
        unreachable!("record candidates checked by caller");
    };
    merge_record_type_candidates(graph, left_fields, right_fields, RecordMerge::Meet)
        .map(Type::Record)
}

fn merge_record_type_candidates(
    graph: &TypeGraph<'_>,
    left_fields: Vec<TypeField>,
    right_fields: Vec<TypeField>,
    merge: RecordMerge,
) -> Result<Vec<TypeField>, SpecializeError> {
    let mut out = Vec::new();
    for left in &left_fields {
        match record_field_type(&right_fields, &left.name) {
            Some(right) => {
                let value = match merge {
                    RecordMerge::Join => {
                        join_type_candidates(graph, left.value.clone(), right.value.clone())?
                    }
                    RecordMerge::Meet => {
                        meet_type_candidates(graph, left.value.clone(), right.value.clone())?
                    }
                };
                out.push(TypeField {
                    name: left.name.clone(),
                    value,
                    optional: match merge {
                        RecordMerge::Join => left.optional || right.optional,
                        RecordMerge::Meet => left.optional && right.optional,
                    },
                });
            }
            None => out.push(TypeField {
                name: left.name.clone(),
                value: left.value.clone(),
                optional: match merge {
                    RecordMerge::Join => true,
                    RecordMerge::Meet => left.optional,
                },
            }),
        }
    }
    for right in right_fields {
        if left_fields.iter().any(|left| left.name == right.name) {
            continue;
        }
        out.push(TypeField {
            name: right.name,
            value: right.value,
            optional: match merge {
                RecordMerge::Join => true,
                RecordMerge::Meet => right.optional,
            },
        });
    }
    Ok(out)
}

fn join_poly_variant_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::PolyVariant(left_variants), Type::PolyVariant(right_variants)) = (left, right)
    else {
        unreachable!("poly variant candidates checked by caller");
    };
    merge_poly_variant_type_candidates(graph, left_variants, right_variants, VariantMerge::Join)
        .map(Type::PolyVariant)
}

fn meet_poly_variant_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::PolyVariant(left_variants), Type::PolyVariant(right_variants)) = (left, right)
    else {
        unreachable!("poly variant candidates checked by caller");
    };
    let variants = merge_poly_variant_type_candidates(
        graph,
        left_variants,
        right_variants,
        VariantMerge::Meet,
    )?;
    if variants.is_empty() {
        return Ok(Type::Never);
    }
    Ok(Type::PolyVariant(variants))
}

fn merge_poly_variant_type_candidates(
    graph: &TypeGraph<'_>,
    left_variants: Vec<TypeVariant>,
    right_variants: Vec<TypeVariant>,
    merge: VariantMerge,
) -> Result<Vec<TypeVariant>, SpecializeError> {
    let mut out = Vec::new();
    for left in &left_variants {
        match matching_variant(&right_variants, left) {
            Some(right) => {
                let payloads = left
                    .payloads
                    .iter()
                    .cloned()
                    .zip(right.payloads.iter().cloned())
                    .map(|(left, right)| match merge {
                        VariantMerge::Join => join_type_candidates(graph, left, right),
                        VariantMerge::Meet => meet_type_candidates(graph, left, right),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                out.push(TypeVariant {
                    name: left.name.clone(),
                    payloads,
                });
            }
            None if merge == VariantMerge::Join => out.push(left.clone()),
            None => {}
        }
    }
    if merge == VariantMerge::Join {
        for right in right_variants {
            if left_variants
                .iter()
                .any(|left| variants_match(left, &right))
            {
                continue;
            }
            out.push(right);
        }
    }
    Ok(out)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RecordMerge {
    Join,
    Meet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VariantMerge {
    Join,
    Meet,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CandidateMerge {
    Join,
    Meet,
}

fn merge_same_head_con_candidate(
    graph: &TypeGraph<'_>,
    path: Vec<String>,
    left_args: Vec<Type>,
    right_args: Vec<Type>,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    let args = left_args
        .into_iter()
        .zip(right_args)
        .map(|(left, right)| merge_candidate_component(graph, left, right, merge))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Type::Con { path, args })
}

fn merge_effect_row_candidates(
    graph: &TypeGraph<'_>,
    left: Vec<Type>,
    right: Vec<Type>,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    let (left_items, left_tail) = split_effect_candidate_tail_owned(graph, left);
    let (right_items, right_tail) = split_effect_candidate_tail_owned(graph, right);
    let left_has_tail = left_tail.is_some();
    let right_has_tail = right_tail.is_some();
    let mut out = Vec::new();
    let mut right_used = vec![false; right_items.len()];
    for left_item in left_items {
        match right_items
            .iter()
            .enumerate()
            .find_map(|(index, right_item)| {
                (!right_used[index] && same_effect_row_family(&left_item, right_item))
                    .then_some(index)
            }) {
            Some(index) => {
                right_used[index] = true;
                out.push(merge_effect_row_item_candidate(
                    graph,
                    left_item,
                    right_items[index].clone(),
                    merge,
                )?);
            }
            None if merge == CandidateMerge::Join || right_has_tail => out.push(left_item),
            None => {}
        }
    }
    for (index, right_item) in right_items.into_iter().enumerate() {
        if right_used[index] {
            continue;
        }
        if merge == CandidateMerge::Join || left_has_tail {
            out.push(right_item);
        }
    }
    match (merge, left_tail, right_tail) {
        (CandidateMerge::Join, Some(left), Some(right)) => {
            out.push(join_type_candidates(graph, left, right)?);
        }
        (CandidateMerge::Meet, Some(left), Some(right)) => {
            out.push(meet_type_candidates(graph, left, right)?);
        }
        (CandidateMerge::Join, Some(tail), None) | (CandidateMerge::Join, None, Some(tail)) => {
            out.push(tail);
        }
        _ => {}
    }
    Ok(types::simplify_type(Type::EffectRow(out)))
}

fn merge_effect_row_item_candidate(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    if left == right {
        return Ok(left);
    }
    match (left, right) {
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if left_path == right_path && left_args.len() == right_args.len() => {
            merge_same_family_effect_item_candidate(graph, left_path, left_args, right_args, merge)
        }
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if effect_path_contains_family(&left_path, &right_path) => Ok(match merge {
            CandidateMerge::Join => Type::Con {
                path: left_path,
                args: left_args,
            },
            CandidateMerge::Meet => Type::Con {
                path: right_path,
                args: right_args,
            },
        }),
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if effect_path_contains_family(&right_path, &left_path) => Ok(match merge {
            CandidateMerge::Join => Type::Con {
                path: right_path,
                args: right_args,
            },
            CandidateMerge::Meet => Type::Con {
                path: left_path,
                args: left_args,
            },
        }),
        (left, right) => merge_candidate_component(graph, left, right, merge),
    }
}

fn merge_same_family_effect_item_candidate(
    graph: &TypeGraph<'_>,
    path: Vec<String>,
    left_args: Vec<Type>,
    right_args: Vec<Type>,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    let args = left_args
        .into_iter()
        .zip(right_args)
        .map(|(left, right)| merge_effect_payload_candidate(graph, left, right, merge))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Type::Con { path, args })
}

fn merge_effect_payload_candidate(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    match merge_candidate_component(graph, left.clone(), right.clone(), merge) {
        Ok(merged) => Ok(merged),
        Err(SpecializeError::ConflictingTypeCandidates { .. }) => Ok(match merge {
            CandidateMerge::Join => {
                types::simplify_type(Type::Union(Box::new(left), Box::new(right)))
            }
            CandidateMerge::Meet => {
                types::simplify_type(Type::Intersection(Box::new(left), Box::new(right)))
            }
        }),
        Err(error) => Err(error),
    }
}

fn merge_candidate_component(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    match merge {
        CandidateMerge::Join => join_type_candidates(graph, left, right),
        CandidateMerge::Meet => meet_type_candidates(graph, left, right),
    }
}

fn same_candidate_head(left: &Type, right: &Type) -> bool {
    match (left, right) {
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) => left_path == right_path && left_args.len() == right_args.len(),
        (Type::Fun { .. }, Type::Fun { .. }) => true,
        (Type::Thunk { .. }, Type::Thunk { .. }) => true,
        (Type::Tuple(left), Type::Tuple(right)) => left.len() == right.len(),
        _ => false,
    }
}

fn value_candidate_subtype_thunk(graph: &TypeGraph<'_>, lower: &Type, upper: &Type) -> bool {
    let Type::Thunk { value, .. } = upper else {
        return false;
    };
    value_candidate_matches_thunk_value(graph, lower, value)
}

fn thunk_value_candidate_subtype(graph: &TypeGraph<'_>, lower: &Type, upper: &Type) -> bool {
    let Type::Thunk { value, .. } = lower else {
        return false;
    };
    thunk_value_matches_candidate(graph, value, upper)
}

fn value_candidate_matches_thunk_value(
    graph: &TypeGraph<'_>,
    value: &Type,
    thunk_value: &Type,
) -> bool {
    matches!(value, Type::OpenVar(_))
        || matches!(thunk_value, Type::OpenVar(_))
        || type_candidate_subtype(graph, value, thunk_value)
        || same_candidate_head(value, thunk_value)
        || match thunk_value {
            Type::Thunk { value: nested, .. } => {
                value_candidate_matches_thunk_value(graph, value, nested)
            }
            _ => false,
        }
}

fn thunk_value_matches_candidate(graph: &TypeGraph<'_>, thunk_value: &Type, value: &Type) -> bool {
    matches!(value, Type::OpenVar(_))
        || matches!(thunk_value, Type::OpenVar(_))
        || type_candidate_subtype(graph, thunk_value, value)
        || same_candidate_head(thunk_value, value)
        || match thunk_value {
            Type::Thunk { value: nested, .. } => {
                thunk_value_matches_candidate(graph, nested, value)
            }
            _ => false,
        }
}

fn prefer_more_resolved_candidate(left: Type, right: Type) -> Type {
    if open_var_count(&right) < open_var_count(&left) {
        right
    } else {
        left
    }
}

fn open_var_count(ty: &Type) -> usize {
    match ty {
        Type::OpenVar(_) => 1,
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().map(open_var_count).sum()
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            open_var_count(arg)
                + open_var_count(arg_effect)
                + open_var_count(ret_effect)
                + open_var_count(ret)
        }
        Type::Thunk { effect, value } => open_var_count(effect) + open_var_count(value),
        Type::Record(fields) => fields
            .iter()
            .map(|field| open_var_count(&field.value))
            .sum(),
        Type::PolyVariant(variants) => variants
            .iter()
            .flat_map(|variant| &variant.payloads)
            .map(open_var_count)
            .sum(),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            open_var_count(left) + open_var_count(right)
        }
        Type::Stack { inner, .. } => open_var_count(inner),
        Type::Any | Type::Never => 0,
    }
}

fn stack_weight_cannot_affect_type(ty: &Type) -> bool {
    match ty {
        Type::Never => true,
        Type::Con { args, .. } | Type::Tuple(args) => {
            args.iter().all(stack_weight_cannot_affect_type)
        }
        Type::Record(fields) => fields
            .iter()
            .all(|field| stack_weight_cannot_affect_type(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .all(|variant| variant.payloads.iter().all(stack_weight_cannot_affect_type)),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            stack_weight_cannot_affect_type(left) && stack_weight_cannot_affect_type(right)
        }
        Type::Any
        | Type::OpenVar(_)
        | Type::EffectRow(_)
        | Type::Fun { .. }
        | Type::Thunk { .. }
        | Type::Stack { .. } => false,
    }
}

fn type_contains_stack(ty: &Type) -> bool {
    match ty {
        Type::Stack { .. } => true,
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(type_contains_stack)
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_contains_stack(arg)
                || type_contains_stack(arg_effect)
                || type_contains_stack(ret_effect)
                || type_contains_stack(ret)
        }
        Type::Thunk { effect, value } => type_contains_stack(effect) || type_contains_stack(value),
        Type::Record(fields) => fields.iter().any(|field| type_contains_stack(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_contains_stack)),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_contains_stack(left) || type_contains_stack(right)
        }
        Type::Any | Type::Never | Type::OpenVar(_) => false,
    }
}

fn type_contains_open_var(ty: &Type) -> bool {
    match ty {
        Type::OpenVar(_) => true,
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(type_contains_open_var)
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_contains_open_var(arg)
                || type_contains_open_var(arg_effect)
                || type_contains_open_var(ret_effect)
                || type_contains_open_var(ret)
        }
        Type::Thunk { effect, value } => {
            type_contains_open_var(effect) || type_contains_open_var(value)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_contains_open_var(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_contains_open_var)),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_contains_open_var(left) || type_contains_open_var(right)
        }
        Type::Stack { inner, .. } => type_contains_open_var(inner),
        Type::Any | Type::Never => false,
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct OpenVarUse {
    positive: bool,
    negative: bool,
    effect: bool,
}

#[derive(Debug, Clone, Copy)]
enum TypePolarity {
    Positive,
    Negative,
}

impl TypePolarity {
    fn flip(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

fn erase_negative_only_open_vars(ty: Type) -> Type {
    let mut uses = HashMap::new();
    collect_open_var_uses(&ty, TypePolarity::Positive, TypeSlotKind::Value, &mut uses);
    substitute_negative_only_open_vars(ty, &uses, TypeSlotKind::Value)
}

fn collect_open_var_uses(
    ty: &Type,
    polarity: TypePolarity,
    context: TypeSlotKind,
    uses: &mut HashMap<u32, OpenVarUse>,
) {
    match ty {
        Type::OpenVar(slot) => {
            let use_ = uses.entry(*slot).or_default();
            match polarity {
                TypePolarity::Positive => use_.positive = true,
                TypePolarity::Negative => use_.negative = true,
            }
            if context == TypeSlotKind::Effect {
                use_.effect = true;
            }
        }
        Type::Con { args, .. } | Type::Tuple(args) => {
            for arg in args {
                collect_open_var_uses(arg, TypePolarity::Positive, TypeSlotKind::Value, uses);
                collect_open_var_uses(arg, TypePolarity::Negative, TypeSlotKind::Value, uses);
            }
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            let negative = polarity.flip();
            collect_open_var_uses(arg, negative, TypeSlotKind::Value, uses);
            collect_open_var_uses(arg_effect, negative, TypeSlotKind::Effect, uses);
            collect_open_var_uses(ret_effect, polarity, TypeSlotKind::Effect, uses);
            collect_open_var_uses(ret, polarity, TypeSlotKind::Value, uses);
        }
        Type::Thunk { effect, value } => {
            collect_open_var_uses(effect, polarity, TypeSlotKind::Effect, uses);
            collect_open_var_uses(value, polarity, TypeSlotKind::Value, uses);
        }
        Type::Record(fields) => {
            for field in fields {
                collect_open_var_uses(&field.value, polarity, TypeSlotKind::Value, uses);
            }
        }
        Type::PolyVariant(variants) => {
            for variant in variants {
                for payload in &variant.payloads {
                    collect_open_var_uses(payload, polarity, TypeSlotKind::Value, uses);
                }
            }
        }
        Type::EffectRow(items) => {
            for item in items {
                collect_open_var_uses(item, polarity, TypeSlotKind::Effect, uses);
            }
        }
        Type::Stack { inner, .. } => {
            collect_open_var_uses(inner, polarity, context, uses);
        }
        Type::Union(left, right) | Type::Intersection(left, right) => {
            collect_open_var_uses(left, polarity, context, uses);
            collect_open_var_uses(right, polarity, context, uses);
        }
        Type::Any | Type::Never => {}
    }
}

fn substitute_negative_only_open_vars(
    ty: Type,
    uses: &HashMap<u32, OpenVarUse>,
    context: TypeSlotKind,
) -> Type {
    match ty {
        Type::OpenVar(slot) => {
            if uses
                .get(&slot)
                .is_some_and(|use_| use_.negative && !use_.positive)
            {
                if context == TypeSlotKind::Effect {
                    Type::pure_effect()
                } else {
                    Type::unit()
                }
            } else {
                Type::OpenVar(slot)
            }
        }
        Type::Con { path, args } => Type::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| substitute_negative_only_open_vars(arg, uses, TypeSlotKind::Value))
                .collect(),
        },
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(substitute_negative_only_open_vars(
                *arg,
                uses,
                TypeSlotKind::Value,
            )),
            arg_effect: Box::new(substitute_negative_only_open_vars(
                *arg_effect,
                uses,
                TypeSlotKind::Effect,
            )),
            ret_effect: Box::new(substitute_negative_only_open_vars(
                *ret_effect,
                uses,
                TypeSlotKind::Effect,
            )),
            ret: Box::new(substitute_negative_only_open_vars(
                *ret,
                uses,
                TypeSlotKind::Value,
            )),
        },
        Type::Thunk { effect, value } => types::runtime_shape(
            substitute_negative_only_open_vars(*effect, uses, TypeSlotKind::Effect),
            substitute_negative_only_open_vars(*value, uses, TypeSlotKind::Value),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    value: substitute_negative_only_open_vars(
                        field.value,
                        uses,
                        TypeSlotKind::Value,
                    ),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::PolyVariant(variants) => Type::PolyVariant(
            variants
                .into_iter()
                .map(|variant| TypeVariant {
                    name: variant.name,
                    payloads: variant
                        .payloads
                        .into_iter()
                        .map(|payload| {
                            substitute_negative_only_open_vars(payload, uses, TypeSlotKind::Value)
                        })
                        .collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(|item| substitute_negative_only_open_vars(item, uses, TypeSlotKind::Value))
                .collect(),
        ),
        Type::EffectRow(items) => types::simplify_type(Type::EffectRow(
            items
                .into_iter()
                .map(|item| substitute_negative_only_open_vars(item, uses, TypeSlotKind::Effect))
                .collect(),
        )),
        Type::Stack { inner, weight } => types::simplify_stack_type(
            substitute_negative_only_open_vars(*inner, uses, context),
            weight,
        ),
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(substitute_negative_only_open_vars(*left, uses, context)),
            Box::new(substitute_negative_only_open_vars(*right, uses, context)),
        )),
        Type::Intersection(left, right) => types::simplify_type(Type::Intersection(
            Box::new(substitute_negative_only_open_vars(*left, uses, context)),
            Box::new(substitute_negative_only_open_vars(*right, uses, context)),
        )),
        Type::Any | Type::Never => ty,
    }
}

fn close_resolved_runtime_surface(ty: Type, context: TypeSlotKind) -> Type {
    close_runtime_type_surface(erase_negative_only_open_vars(ty), context)
}

fn close_resolved_inference_surface(ty: Type, context: TypeSlotKind) -> Type {
    close_inference_type_surface(erase_negative_only_open_vars(ty), context)
}

fn close_inference_type_surface(ty: Type, context: TypeSlotKind) -> Type {
    match ty {
        Type::OpenVar(_) => match context {
            TypeSlotKind::Value => Type::unit(),
            TypeSlotKind::Effect => Type::pure_effect(),
        },
        Type::Con { path, args } => Type::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| close_inference_type_surface(arg, TypeSlotKind::Value))
                .collect(),
        },
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(close_inference_type_surface(*arg, TypeSlotKind::Value)),
            arg_effect: Box::new(close_inference_type_surface(
                *arg_effect,
                TypeSlotKind::Effect,
            )),
            ret_effect: Box::new(close_inference_type_surface(
                *ret_effect,
                TypeSlotKind::Effect,
            )),
            ret: Box::new(close_inference_type_surface(*ret, TypeSlotKind::Value)),
        },
        Type::Thunk { effect, value } => types::runtime_shape(
            close_inference_type_surface(*effect, TypeSlotKind::Effect),
            close_inference_type_surface(*value, TypeSlotKind::Value),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    value: close_inference_type_surface(field.value, TypeSlotKind::Value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::PolyVariant(variants) => Type::PolyVariant(
            variants
                .into_iter()
                .map(|variant| TypeVariant {
                    name: variant.name,
                    payloads: variant
                        .payloads
                        .into_iter()
                        .map(|payload| close_inference_type_surface(payload, TypeSlotKind::Value))
                        .collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(|item| close_inference_type_surface(item, TypeSlotKind::Value))
                .collect(),
        ),
        Type::EffectRow(items) => types::simplify_type(Type::EffectRow(
            items
                .into_iter()
                .map(|item| close_inference_type_surface(item, TypeSlotKind::Effect))
                .collect(),
        )),
        Type::Stack { inner, weight } => {
            types::simplify_stack_type(close_inference_type_surface(*inner, context), weight)
        }
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(close_inference_type_surface(*left, context)),
            Box::new(close_inference_type_surface(*right, context)),
        )),
        Type::Intersection(left, right) => types::simplify_type(Type::Intersection(
            Box::new(close_inference_type_surface(*left, context)),
            Box::new(close_inference_type_surface(*right, context)),
        )),
        Type::Any | Type::Never => ty,
    }
}

fn close_runtime_type_surface(ty: Type, context: TypeSlotKind) -> Type {
    match ty {
        Type::OpenVar(_) => match context {
            TypeSlotKind::Value => Type::unit(),
            TypeSlotKind::Effect => Type::pure_effect(),
        },
        Type::Con { path, args } => Type::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| close_runtime_type_surface(arg, TypeSlotKind::Value))
                .collect(),
        },
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            let arg = close_runtime_type_surface(*arg, TypeSlotKind::Value);
            let arg_effect = close_runtime_type_surface(*arg_effect, TypeSlotKind::Effect);
            let ret_effect = close_runtime_type_surface(*ret_effect, TypeSlotKind::Effect);
            let ret = close_runtime_type_surface(*ret, TypeSlotKind::Value);
            Type::Fun {
                arg: Box::new(types::runtime_shape(arg_effect, arg)),
                arg_effect: Box::new(Type::pure_effect()),
                ret_effect: Box::new(Type::pure_effect()),
                ret: Box::new(types::runtime_shape(ret_effect, ret)),
            }
        }
        Type::Thunk { effect, value } => types::runtime_shape(
            close_runtime_type_surface(*effect, TypeSlotKind::Effect),
            close_runtime_type_surface(*value, TypeSlotKind::Value),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    value: close_runtime_type_surface(field.value, TypeSlotKind::Value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::PolyVariant(variants) => Type::PolyVariant(
            variants
                .into_iter()
                .map(|variant| TypeVariant {
                    name: variant.name,
                    payloads: variant
                        .payloads
                        .into_iter()
                        .map(|payload| close_runtime_type_surface(payload, TypeSlotKind::Value))
                        .collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(|item| close_runtime_type_surface(item, TypeSlotKind::Value))
                .collect(),
        ),
        Type::EffectRow(items) => types::simplify_type(Type::EffectRow(
            items
                .into_iter()
                .map(|item| close_runtime_type_surface(item, TypeSlotKind::Effect))
                .collect(),
        )),
        Type::Stack { inner, weight } => {
            types::simplify_stack_type(close_runtime_type_surface(*inner, context), weight)
        }
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(close_runtime_type_surface(*left, context)),
            Box::new(close_runtime_type_surface(*right, context)),
        )),
        Type::Intersection(left, right) => types::simplify_type(Type::Intersection(
            Box::new(close_runtime_type_surface(*left, context)),
            Box::new(close_runtime_type_surface(*right, context)),
        )),
        Type::Any | Type::Never => ty,
    }
}

fn type_candidate_subtype(graph: &TypeGraph<'_>, lower: &Type, upper: &Type) -> bool {
    if lower == upper || matches!(lower, Type::Never) || matches!(upper, Type::Any) {
        return true;
    }
    match (lower, upper) {
        (Type::Con { path: lower, .. }, Type::Con { path: upper, .. }) if lower != upper => graph
            .arena
            .cast_rules
            .iter()
            .any(|rule| rule.source == *lower && rule.target == *upper),
        (
            Type::Con {
                path: lower_path,
                args: lower_args,
            },
            Type::Con {
                path: upper_path,
                args: upper_args,
            },
        ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
            lower_args.iter().zip(upper_args).all(|(lower, upper)| {
                type_candidate_subtype(graph, lower, upper)
                    && type_candidate_subtype(graph, upper, lower)
            })
        }
        (
            Type::Fun {
                arg: lower_arg,
                ret: lower_ret,
                ..
            },
            Type::Fun {
                arg: upper_arg,
                ret: upper_ret,
                ..
            },
        ) => {
            type_candidate_subtype(graph, upper_arg, lower_arg)
                && type_candidate_subtype(graph, lower_ret, upper_ret)
        }
        (Type::Tuple(lower), Type::Tuple(upper)) if lower.len() == upper.len() => lower
            .iter()
            .zip(upper)
            .all(|(lower, upper)| type_candidate_subtype(graph, lower, upper)),
        (Type::Record(lower), Type::Record(upper)) => upper.iter().all(|upper| {
            upper.optional
                || record_field_type(lower, &upper.name)
                    .is_some_and(|lower| type_candidate_subtype(graph, &lower.value, &upper.value))
        }),
        (Type::PolyVariant(lower), Type::PolyVariant(upper)) => lower.iter().all(|lower| {
            matching_variant(upper, lower).is_some_and(|upper| {
                lower
                    .payloads
                    .iter()
                    .zip(&upper.payloads)
                    .all(|(lower, upper)| type_candidate_subtype(graph, lower, upper))
            })
        }),
        (Type::EffectRow(lower), Type::EffectRow(upper)) => {
            effect_row_candidate_subtype(graph, lower, upper)
        }
        (Type::Union(left, right), upper) => {
            type_candidate_subtype(graph, left, upper)
                && type_candidate_subtype(graph, right, upper)
        }
        (lower, Type::Intersection(left, right)) => {
            type_candidate_subtype(graph, lower, left)
                && type_candidate_subtype(graph, lower, right)
        }
        _ => false,
    }
}

fn effect_row_candidate_subtype(
    graph: &TypeGraph<'_>,
    lower_items: &[Type],
    upper_items: &[Type],
) -> bool {
    let (lower_items, lower_has_top_tail) = split_effect_candidate_tail(graph, lower_items);
    let (upper_items, upper_has_top_tail) = split_effect_candidate_tail(graph, upper_items);
    if lower_items.is_empty() && !lower_has_top_tail {
        return true;
    }
    let mut matched_upper = vec![false; upper_items.len()];
    for lower in lower_items {
        let Some(upper_index) = upper_items.iter().enumerate().find_map(|(index, upper)| {
            (!matched_upper[index] && effect_row_item_candidate_subtype(graph, lower, upper))
                .then_some(index)
        }) else {
            if upper_has_top_tail {
                continue;
            }
            return false;
        };
        matched_upper[upper_index] = true;
    }
    !lower_has_top_tail || upper_has_top_tail
}

fn effect_rows_have_same_families(graph: &TypeGraph<'_>, left: &Type, right: &Type) -> bool {
    let (Type::EffectRow(left), Type::EffectRow(right)) = (left, right) else {
        return false;
    };
    let (left, left_has_tail) = split_effect_candidate_tail(graph, left);
    let (right, right_has_tail) = split_effect_candidate_tail(graph, right);
    !left_has_tail
        && !right_has_tail
        && left.len() == right.len()
        && left.iter().all(|left| {
            right
                .iter()
                .any(|right| same_effect_row_family(left, right))
        })
}

fn refine_effect_lower_with_upper(
    graph: &TypeGraph<'_>,
    lower: &Type,
    upper: &Type,
) -> Result<Option<Type>, SpecializeError> {
    let (Type::EffectRow(lower_items), Type::EffectRow(upper_items)) = (lower, upper) else {
        return Ok(None);
    };
    let (lower_items, lower_has_tail) = split_effect_candidate_tail(graph, lower_items);
    let (upper_items, upper_has_tail) = split_effect_candidate_tail(graph, upper_items);
    if lower_has_tail {
        if upper_has_tail
            || !lower_items.iter().all(|lower_item| {
                upper_items
                    .iter()
                    .any(|upper_item| same_effect_row_family(lower_item, upper_item))
            })
        {
            return Ok(None);
        }
        return meet_type_candidates(graph, lower.clone(), upper.clone()).map(Some);
    }
    let mut refined = Vec::with_capacity(lower_items.len());
    for lower_item in lower_items {
        match upper_items
            .iter()
            .find(|upper_item| same_effect_row_family(lower_item, upper_item))
        {
            Some(upper_item) => refined.push(merge_effect_row_item_candidate(
                graph,
                lower_item.clone(),
                upper_item.clone(),
                CandidateMerge::Meet,
            )?),
            None if upper_has_tail => refined.push(lower_item.clone()),
            None => return Ok(None),
        }
    }
    Ok(Some(types::simplify_type(Type::EffectRow(refined))))
}

fn effect_row_item_candidate_subtype(graph: &TypeGraph<'_>, lower: &Type, upper: &Type) -> bool {
    match (lower, upper) {
        (
            Type::Con {
                path: lower_path,
                args: lower_args,
            },
            Type::Con {
                path: upper_path,
                args: upper_args,
            },
        ) if lower_path == upper_path && lower_args.len() == upper_args.len() => lower_args
            .iter()
            .zip(upper_args)
            .all(|(lower, upper)| effect_payload_candidate_subtype(graph, lower, upper)),
        (
            Type::Con {
                path: lower_path,
                args: lower_args,
            },
            Type::Con {
                path: upper_path,
                args: upper_args,
            },
        ) if effect_path_contains_family(upper_path, lower_path) => {
            effect_payloads_candidate_subtype(graph, lower_args, upper_args)
        }
        _ => same_effect_row_family(lower, upper) && type_candidate_subtype(graph, lower, upper),
    }
}

fn effect_payloads_candidate_subtype(
    graph: &TypeGraph<'_>,
    lower_args: &[Type],
    upper_args: &[Type],
) -> bool {
    upper_args.is_empty()
        || (lower_args.len() == upper_args.len()
            && lower_args
                .iter()
                .zip(upper_args)
                .all(|(lower, upper)| effect_payload_candidate_subtype(graph, lower, upper)))
}

fn effect_payload_candidate_subtype(graph: &TypeGraph<'_>, lower: &Type, upper: &Type) -> bool {
    if lower == upper || matches!(upper, Type::OpenVar(_)) {
        return true;
    }
    if matches!(lower, Type::OpenVar(_)) {
        return false;
    }
    type_candidate_subtype(graph, lower, upper)
}

fn split_effect_candidate_tail<'a>(graph: &TypeGraph<'_>, items: &'a [Type]) -> (&'a [Type], bool) {
    match items.last() {
        Some(Type::OpenVar(slot))
            if graph
                .slots
                .get(*slot as usize)
                .is_some_and(|slot| slot.kind == TypeSlotKind::Effect) =>
        {
            (&items[..items.len() - 1], true)
        }
        _ => (items, false),
    }
}

fn split_effect_candidate_tail_owned(
    graph: &TypeGraph<'_>,
    mut items: Vec<Type>,
) -> (Vec<Type>, Option<Type>) {
    let Some(Type::OpenVar(slot)) = items.last().cloned() else {
        return (items, None);
    };
    if graph
        .slots
        .get(slot as usize)
        .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
    {
        let tail = items.pop();
        return (items, tail);
    }
    (items, None)
}

fn effect_consumption_demand(expected: &Type) -> Option<EffectSubtractionDemand> {
    effect_intersection_consumption_demand(expected)
        .or_else(|| effect_row_consumption_demand(expected))
}

fn effect_intersection_consumption_demand(expected: &Type) -> Option<EffectSubtractionDemand> {
    let Type::Intersection(left, right) = expected else {
        return None;
    };
    effect_intersection_consumption_demand_pair(left, right)
        .or_else(|| effect_intersection_consumption_demand_pair(right, left))
}

fn effect_intersection_consumption_demand_pair(
    tail: &Type,
    row: &Type,
) -> Option<EffectSubtractionDemand> {
    let Type::EffectRow(items) = row else {
        return None;
    };
    let Some(last) = items.last() else {
        return None;
    };
    if last != tail {
        return None;
    }
    let handled_items = items[..items.len() - 1].to_vec();
    if handled_items.is_empty() {
        return None;
    }
    Some(EffectSubtractionDemand {
        tail: tail.clone(),
        runtime_effect: row.clone(),
        handled_items,
    })
}

fn effect_row_consumption_demand(expected: &Type) -> Option<EffectSubtractionDemand> {
    let Type::EffectRow(items) = expected else {
        return None;
    };
    let Some(Type::OpenVar(_)) = items.last() else {
        return None;
    };
    let handled_items = items[..items.len() - 1].to_vec();
    if handled_items.is_empty() {
        return None;
    }
    Some(EffectSubtractionDemand {
        tail: items[items.len() - 1].clone(),
        runtime_effect: expected.clone(),
        handled_items,
    })
}

fn effect_row_from_parts(mut items: Vec<Type>, tail: Option<Type>) -> Type {
    if items.is_empty() && tail.is_some() {
        return tail.expect("tail is present");
    }
    match tail {
        Some(Type::EffectRow(tail_items)) => items.extend(tail_items),
        Some(tail) if tail.is_pure_effect() => {}
        Some(tail) => items.push(tail),
        None => {}
    }
    if items.is_empty() {
        Type::pure_effect()
    } else {
        types::simplify_type(Type::EffectRow(items))
    }
}

fn residual_effect_after_consuming_handled_candidate(
    actual_items: Vec<Type>,
    actual_tail: Option<Type>,
    handled_items: &[Type],
) -> Type {
    let mut matched_handled = vec![false; handled_items.len()];
    let mut residual_items = Vec::new();
    for actual in actual_items {
        let Some(index) = handled_items
            .iter()
            .enumerate()
            .find_map(|(index, handled)| {
                (!matched_handled[index] && same_effect_row_family(&actual, handled))
                    .then_some(index)
            })
        else {
            residual_items.push(actual);
            continue;
        };
        matched_handled[index] = true;
    }
    effect_row_from_parts(residual_items, actual_tail)
}

fn empty_stack_weight() -> StackWeight {
    StackWeight {
        entries: Vec::new(),
    }
}

fn stack_weight_is_empty(weight: &StackWeight) -> bool {
    weight.entries.is_empty()
}

fn peel_stack_weight(mut ty: Type, mut weight: StackWeight) -> (Type, StackWeight) {
    while let Type::Stack {
        inner,
        weight: stack_weight,
    } = ty
    {
        weight = compose_stack_weights(stack_weight, weight);
        ty = *inner;
    }
    (ty, weight)
}

fn compose_stack_weights(left: StackWeight, right: StackWeight) -> StackWeight {
    if left.entries.is_empty() {
        return right;
    }
    if right.entries.is_empty() {
        return left;
    }
    let mut out = left;
    for entry in right.entries {
        for families in entry.floor {
            push_stack_floor(&mut out, entry.id, families);
        }
        push_stack_pops(&mut out, entry.id, entry.pops);
        for families in entry.stack {
            push_stack_item(&mut out, entry.id, families);
        }
    }
    out
}

fn compose_replay_stack_weights(left: StackWeight, right: StackWeight) -> StackWeight {
    saturate_unmatched_pops(compose_stack_weights(left, right))
}

fn saturate_unmatched_pops(mut weight: StackWeight) -> StackWeight {
    for entry in &mut weight.entries {
        if entry.pops > 0 {
            entry.pops = u32::MAX;
        }
    }
    weight
}

fn push_stack_floor(weight: &mut StackWeight, id: u32, families: EffectFamilies) {
    let entry = stack_weight_entry_mut(weight, id);
    let combined = entry
        .floor
        .drain(..)
        .fold(families, intersect_effect_families);
    if !matches!(combined, EffectFamilies::All) {
        entry.floor.push(normalize_effect_families(combined));
    }
    remove_empty_stack_weight_entry(weight, id);
}

fn push_stack_item(weight: &mut StackWeight, id: u32, families: EffectFamilies) {
    let entry = stack_weight_entry_mut(weight, id);
    entry.stack.push(normalize_effect_families(families));
}

fn push_stack_pops(weight: &mut StackWeight, id: u32, count: u32) {
    if count == 0 {
        return;
    }
    let entry = stack_weight_entry_mut(weight, id);
    if count == u32::MAX {
        entry.stack.clear();
        entry.pops = u32::MAX;
        return;
    }
    let removable = entry.stack.len().min(count as usize);
    if removable > 0 {
        entry.stack.truncate(entry.stack.len() - removable);
    }
    let remaining = count.saturating_sub(removable as u32);
    if remaining > 0 {
        entry.pops = entry.pops.saturating_add(remaining);
        if entry.pops == u32::MAX {
            entry.stack.clear();
        }
    }
    remove_empty_stack_weight_entry(weight, id);
}

fn stack_weight_entry_mut(weight: &mut StackWeight, id: u32) -> &mut StackWeightEntry {
    match weight.entries.binary_search_by_key(&id, |entry| entry.id) {
        Ok(index) => &mut weight.entries[index],
        Err(index) => {
            weight.entries.insert(
                index,
                StackWeightEntry {
                    id,
                    pops: 0,
                    floor: Vec::new(),
                    stack: Vec::new(),
                },
            );
            &mut weight.entries[index]
        }
    }
}

fn remove_empty_stack_weight_entry(weight: &mut StackWeight, id: u32) {
    if let Ok(index) = weight.entries.binary_search_by_key(&id, |entry| entry.id)
        && weight.entries[index].pops == 0
        && weight.entries[index].floor.is_empty()
        && weight.entries[index].stack.is_empty()
    {
        weight.entries.remove(index);
    }
}

fn subtract_stack_weight(weight: StackWeight, removed: &[EffectFamily]) -> StackWeight {
    if removed.is_empty() {
        return weight;
    }

    let mut out = StackWeight {
        entries: Vec::new(),
    };
    for entry in weight.entries {
        let mut residual_parts = Vec::new();
        if entry.floor.is_empty() && entry.stack.is_empty() {
            residual_parts.push(subtract_effect_families(EffectFamilies::All, removed));
        } else {
            for families in &entry.floor {
                residual_parts.push(subtract_effect_families(families.clone(), removed));
            }
            for families in &entry.stack {
                residual_parts.push(subtract_effect_families(families.clone(), removed));
            }
        }
        if let Some(floor) = residual_parts.into_iter().reduce(intersect_effect_families) {
            push_stack_floor(&mut out, entry.id, floor);
        }
        push_stack_pops(&mut out, entry.id, entry.pops);
        for families in entry.stack {
            push_stack_item(
                &mut out,
                entry.id,
                subtract_effect_families(families, removed),
            );
        }
    }
    out
}

fn subtract_effect_families(families: EffectFamilies, removed: &[EffectFamily]) -> EffectFamilies {
    match families {
        EffectFamilies::Empty => EffectFamilies::Empty,
        EffectFamilies::All => all_except_effect_families(removed.iter().cloned()),
        EffectFamilies::Set(items) => set_effect_families(
            items
                .into_iter()
                .filter(|family| !effect_family_path_is_in(family, removed)),
        ),
        EffectFamilies::AllExcept(items) => {
            all_except_effect_families(items.into_iter().chain(removed.iter().cloned()))
        }
    }
}

fn intersect_effect_families(left: EffectFamilies, right: EffectFamilies) -> EffectFamilies {
    match (left, right) {
        (EffectFamilies::Empty, _) | (_, EffectFamilies::Empty) => EffectFamilies::Empty,
        (EffectFamilies::All, right) | (right, EffectFamilies::All) => {
            normalize_effect_families(right)
        }
        (EffectFamilies::Set(left), EffectFamilies::Set(right)) => set_effect_families(
            left.into_iter()
                .filter(|family| effect_family_path_is_in(family, &right)),
        ),
        (EffectFamilies::Set(set), EffectFamilies::AllExcept(excluded))
        | (EffectFamilies::AllExcept(excluded), EffectFamilies::Set(set)) => set_effect_families(
            set.into_iter()
                .filter(|family| !effect_family_path_is_in(family, &excluded)),
        ),
        (EffectFamilies::AllExcept(left), EffectFamilies::AllExcept(right)) => {
            all_except_effect_families(left.into_iter().chain(right))
        }
    }
}

fn normalize_effect_families(families: EffectFamilies) -> EffectFamilies {
    match families {
        EffectFamilies::Empty => EffectFamilies::Empty,
        EffectFamilies::All => EffectFamilies::All,
        EffectFamilies::Set(items) => set_effect_families(items),
        EffectFamilies::AllExcept(items) => all_except_effect_families(items),
    }
}

fn stack_weight_allows_effect_item(weight: &StackWeight, item: &Type) -> bool {
    weight
        .entries
        .iter()
        .flat_map(|entry| entry.floor.iter().chain(&entry.stack))
        .all(|families| effect_families_allow_item(families, item))
}

fn effect_families_allow_item(families: &EffectFamilies, item: &Type) -> bool {
    match families {
        EffectFamilies::Empty => false,
        EffectFamilies::All => true,
        EffectFamilies::Set(allowed) => allowed
            .iter()
            .any(|family| effect_family_matches_item(family, item)),
        EffectFamilies::AllExcept(excluded) => !excluded
            .iter()
            .any(|family| effect_family_matches_item(family, item)),
    }
}

fn effect_family_matches_item(family: &EffectFamily, item: &Type) -> bool {
    let Type::Con { path, args } = item else {
        return false;
    };
    effect_path_contains_family(&family.path, path)
        && (family.args.is_empty() || args.len() == family.args.len())
}

fn effect_families_from_items(items: &[Type]) -> Vec<EffectFamily> {
    let mut out = Vec::new();
    for item in items {
        if let Some(family) = effect_family_from_item(item)
            && !out
                .iter()
                .any(|existing: &EffectFamily| existing.path == family.path)
        {
            out.push(family);
        }
    }
    out
}

fn sorted_effect_families(mut families: Vec<EffectFamily>) -> Vec<EffectFamily> {
    families.sort_by(|left, right| left.path.cmp(&right.path));
    families
}

fn set_effect_families(items: impl IntoIterator<Item = EffectFamily>) -> EffectFamilies {
    let items = collect_effect_families(items);
    match items.as_slice() {
        [] => EffectFamilies::Empty,
        _ => EffectFamilies::Set(items),
    }
}

fn all_except_effect_families(items: impl IntoIterator<Item = EffectFamily>) -> EffectFamilies {
    let items = collect_effect_families(items);
    match items.as_slice() {
        [] => EffectFamilies::All,
        _ => EffectFamilies::AllExcept(items),
    }
}

fn collect_effect_families(items: impl IntoIterator<Item = EffectFamily>) -> Vec<EffectFamily> {
    let mut out = Vec::new();
    for family in items {
        if !out
            .iter()
            .any(|existing: &EffectFamily| existing.path == family.path)
        {
            out.push(family);
        }
    }
    out.sort_by(|left, right| left.path.cmp(&right.path));
    out
}

fn effect_family_path_is_in(family: &EffectFamily, items: &[EffectFamily]) -> bool {
    items
        .iter()
        .any(|item| effect_paths_same_family(&item.path, &family.path))
}

fn resolve_role_input_types(
    resolver: &mut TypeResolver<'_, '_>,
    demand: &types::InstantiatedRolePredicate,
) -> Result<Option<Vec<Type>>, SpecializeError> {
    let mut inputs = Vec::with_capacity(demand.inputs.len());
    for input in &demand.inputs {
        let lower = match resolver.resolve(&input.lower) {
            Ok(lower) => lower,
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => return Ok(None),
            Err(error) => return Err(error),
        };
        let upper = match resolver.resolve(&input.upper) {
            Ok(upper) => upper,
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => return Ok(None),
            Err(error) => return Err(error),
        };
        let Some(ty) = choose_role_arg_exact_type(lower, upper) else {
            return Ok(None);
        };
        inputs.push(role_input_value_type(ty));
    }
    Ok(Some(inputs))
}

fn exact_role_input_types(predicate: &types::InstantiatedRolePredicate) -> Option<Vec<Type>> {
    predicate
        .inputs
        .iter()
        .map(|input| {
            choose_role_arg_exact_type(input.lower.clone(), input.upper.clone())
                .map(role_input_value_type)
        })
        .collect()
}

fn role_input_value_type(ty: Type) -> Type {
    split_runtime_computation_shape(ty).0
}

fn choose_role_arg_exact_type(lower: Type, upper: Type) -> Option<Type> {
    if lower == upper {
        return Some(lower);
    }
    if matches!(lower, Type::Never) && !matches!(upper, Type::Any) {
        return Some(upper);
    }
    if matches!(upper, Type::Any) && !matches!(lower, Type::Never) {
        return Some(lower);
    }
    None
}

fn split_runtime_computation_shape(ty: Type) -> (Type, Type) {
    match ty {
        Type::Thunk { effect, value } => (*value, *effect),
        ty => (ty, Type::pure_effect()),
    }
}

fn runtime_function_return_type(ty: &Type) -> Option<&Type> {
    let Type::Fun { ret, .. } = ty else {
        return None;
    };
    Some(ret)
}

fn discarded_value_context(ty: &Type) -> Option<Type> {
    match ty {
        Type::Thunk { effect, value } => Some(types::runtime_shape(
            effect.as_ref().clone(),
            discarded_value_type(value),
        )),
        _ => None,
    }
}

fn discarded_value_type(ty: &Type) -> Type {
    match ty {
        Type::Thunk { effect, value } => {
            types::runtime_shape(effect.as_ref().clone(), discarded_value_type(value))
        }
        Type::OpenVar(_) => Type::unit(),
        Type::Con { path, args } => Type::Con {
            path: path.clone(),
            args: args.iter().map(discarded_value_type).collect(),
        },
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(discarded_value_type(arg)),
            arg_effect: Box::new(discarded_effect_type(arg_effect)),
            ret_effect: Box::new(discarded_effect_type(ret_effect)),
            ret: Box::new(discarded_value_type(ret)),
        },
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|field| TypeField {
                    name: field.name.clone(),
                    value: discarded_value_type(&field.value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::PolyVariant(variants) => Type::PolyVariant(
            variants
                .iter()
                .map(|variant| TypeVariant {
                    name: variant.name.clone(),
                    payloads: variant.payloads.iter().map(discarded_value_type).collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(items.iter().map(discarded_value_type).collect()),
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(discarded_value_type(left)),
            Box::new(discarded_value_type(right)),
        )),
        Type::Intersection(left, right) => types::simplify_type(Type::Intersection(
            Box::new(discarded_value_type(left)),
            Box::new(discarded_value_type(right)),
        )),
        Type::Stack { inner, weight } => {
            types::simplify_stack_type(discarded_value_type(inner), weight.clone())
        }
        Type::EffectRow(_) => Type::unit(),
        Type::Any | Type::Never => ty.clone(),
    }
}

fn discarded_effect_type(ty: &Type) -> Type {
    match ty {
        Type::OpenVar(_) => Type::pure_effect(),
        Type::EffectRow(items) => types::simplify_type(Type::EffectRow(
            items.iter().map(discarded_effect_type).collect(),
        )),
        Type::Stack { inner, weight } => {
            types::simplify_stack_type(discarded_effect_type(inner), weight.clone())
        }
        ty => discarded_value_type(ty),
    }
}

fn discarded_catch_has_open_result(expr: &poly_expr::Expr, ty: &Type) -> bool {
    matches!(expr, poly_expr::Expr::Catch(_, _))
        && matches!(ty, Type::Thunk { value, .. } if matches!(value.as_ref(), Type::OpenVar(_)))
}

struct FunctionComputationParts {
    arg: Type,
    arg_effect: Type,
    ret_effect: Type,
    ret: Type,
}

fn function_computation_parts(ty: &Type) -> Option<FunctionComputationParts> {
    let Type::Fun {
        arg,
        arg_effect,
        ret_effect,
        ret,
    } = ty
    else {
        return None;
    };
    let (arg, arg_effect) =
        split_declared_runtime_shape(arg.as_ref().clone(), arg_effect.as_ref().clone());
    let (ret, ret_effect) =
        split_declared_runtime_shape(ret.as_ref().clone(), ret_effect.as_ref().clone());
    Some(FunctionComputationParts {
        arg,
        arg_effect,
        ret_effect,
        ret,
    })
}

fn split_declared_runtime_shape(shape: Type, legacy_effect: Type) -> (Type, Type) {
    match shape {
        Type::Thunk { effect, value } => (*value, *effect),
        value => (value, legacy_effect),
    }
}

fn split_function_spine(mut ty: Type, arity: usize) -> Option<(Vec<Type>, Type)> {
    let mut args = Vec::with_capacity(arity);
    for _ in 0..arity {
        let Type::Fun { arg, ret, .. } = ty else {
            return None;
        };
        args.push(*arg);
        ty = *ret;
    }
    Some((args, ty))
}

fn unary_type(arg: Type, ret: Type) -> Type {
    types::pure_function_type(arg, ret)
}

fn binary_type(param: Type, ret: Type) -> Type {
    function_type(vec![param.clone(), param], ret)
}

fn function_type(args: Vec<Type>, ret: Type) -> Type {
    args.into_iter()
        .rev()
        .fold(ret, |ret, arg| types::pure_function_type(arg, ret))
}

fn int_type() -> Type {
    con(&["int"], Vec::new())
}

fn float_type() -> Type {
    con(&["float"], Vec::new())
}

fn bool_type() -> Type {
    con(&["bool"], Vec::new())
}

fn str_type() -> Type {
    std_types::str_type()
}

fn char_type() -> Type {
    std_types::char_type()
}

fn bytes_type() -> Type {
    std_types::bytes_type()
}

fn path_type() -> Type {
    std_types::path_type()
}

fn range_type() -> Type {
    std_types::range_type()
}

fn list_type(item: Type) -> Type {
    std_types::list_type(item)
}

fn list_view_type(item: Type) -> Type {
    std_types::list_view_type(item)
}

fn con(path: &[&str], args: Vec<Type>) -> Type {
    Type::Con {
        path: path.iter().map(|segment| (*segment).to_string()).collect(),
        args,
    }
}

fn record_field_type<'a>(fields: &'a [TypeField], name: &str) -> Option<&'a TypeField> {
    fields.iter().find(|field| field.name == name)
}

fn matching_variant<'a>(
    variants: &'a [TypeVariant],
    target: &TypeVariant,
) -> Option<&'a TypeVariant> {
    variants
        .iter()
        .find(|variant| variants_match(variant, target))
}

fn variants_match(left: &TypeVariant, right: &TypeVariant) -> bool {
    left.name == right.name && left.payloads.len() == right.payloads.len()
}

fn record_spread_def(
    spread: &poly_expr::RecordSpread<poly_expr::DefId>,
) -> Option<poly_expr::DefId> {
    match spread {
        poly_expr::RecordSpread::Head(def) | poly_expr::RecordSpread::Tail(def) => Some(*def),
        poly_expr::RecordSpread::None => None,
    }
}

fn same_effect_row_family(left: &Type, right: &Type) -> bool {
    let (
        Type::Con {
            path: left_path, ..
        },
        Type::Con {
            path: right_path, ..
        },
    ) = (left, right)
    else {
        return left == right;
    };
    effect_paths_same_family(left_path, right_path)
}

fn effect_paths_same_family(left: &[String], right: &[String]) -> bool {
    effect_path_contains_family(left, right) || effect_path_contains_family(right, left)
}

fn effect_path_contains_family(family: &[String], item: &[String]) -> bool {
    !family.is_empty() && item.starts_with(family)
}

fn effect_row_items(effect: &Type) -> &[Type] {
    match effect {
        Type::EffectRow(items) => items,
        _ => std::slice::from_ref(effect),
    }
}

fn effect_family_from_item(item: &Type) -> Option<EffectFamily> {
    let Type::Con { path, args } = item else {
        return None;
    };
    Some(EffectFamily {
        path: path.clone(),
        args: args.clone(),
    })
}

fn matching_effect_row_item(item: &Type, candidates: &[Type]) -> Option<Type> {
    candidates
        .iter()
        .find(|candidate| same_effect_row_family(item, candidate))
        .cloned()
}

fn refine_operation_type_from_handled_effect(
    ty: Type,
    operation_effect: &Type,
    handled_effect: &Type,
) -> Type {
    let mut replacements = Vec::new();
    for operation_item in effect_row_items(operation_effect) {
        for handled_item in effect_row_items(handled_effect) {
            collect_effect_arg_replacements(operation_item, handled_item, &mut replacements);
        }
    }
    replace_effect_arg_occurrences(ty, &replacements)
}

fn collect_effect_arg_replacements(
    operation_item: &Type,
    handled_item: &Type,
    replacements: &mut Vec<(Type, Type)>,
) {
    let (
        Type::Con {
            path: operation_path,
            args: operation_args,
        },
        Type::Con {
            path: handled_path,
            args: handled_args,
        },
    ) = (operation_item, handled_item)
    else {
        return;
    };
    if operation_path != handled_path || operation_args.len() != handled_args.len() {
        return;
    }
    replacements.extend(
        operation_args
            .iter()
            .cloned()
            .zip(handled_args.iter().cloned()),
    );
}

fn replace_effect_arg_occurrences(ty: Type, replacements: &[(Type, Type)]) -> Type {
    if let Some((_, replacement)) = replacements
        .iter()
        .find(|(needle, _)| type_replacement_key_matches(&ty, needle))
    {
        return replacement.clone();
    }
    match ty {
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(replace_effect_arg_occurrences(*arg, replacements)),
            arg_effect: Box::new(replace_effect_arg_occurrences(*arg_effect, replacements)),
            ret_effect: Box::new(replace_effect_arg_occurrences(*ret_effect, replacements)),
            ret: Box::new(replace_effect_arg_occurrences(*ret, replacements)),
        },
        Type::Thunk { effect, value } => Type::Thunk {
            effect: Box::new(replace_effect_arg_occurrences(*effect, replacements)),
            value: Box::new(replace_effect_arg_occurrences(*value, replacements)),
        },
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    optional: field.optional,
                    value: replace_effect_arg_occurrences(field.value, replacements),
                })
                .collect(),
        ),
        Type::PolyVariant(variants) => Type::PolyVariant(
            variants
                .into_iter()
                .map(|variant| TypeVariant {
                    name: variant.name,
                    payloads: variant
                        .payloads
                        .into_iter()
                        .map(|payload| replace_effect_arg_occurrences(payload, replacements))
                        .collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(|item| replace_effect_arg_occurrences(item, replacements))
                .collect(),
        ),
        Type::EffectRow(items) => Type::EffectRow(
            items
                .into_iter()
                .map(|item| replace_effect_arg_occurrences(item, replacements))
                .collect(),
        ),
        Type::Con { path, args } => Type::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| replace_effect_arg_occurrences(arg, replacements))
                .collect(),
        },
        Type::Union(left, right) => Type::Union(
            Box::new(replace_effect_arg_occurrences(*left, replacements)),
            Box::new(replace_effect_arg_occurrences(*right, replacements)),
        ),
        Type::Intersection(left, right) => Type::Intersection(
            Box::new(replace_effect_arg_occurrences(*left, replacements)),
            Box::new(replace_effect_arg_occurrences(*right, replacements)),
        ),
        Type::Stack { inner, weight } => Type::Stack {
            inner: Box::new(replace_effect_arg_occurrences(*inner, replacements)),
            weight,
        },
        Type::OpenVar(_) | Type::Any | Type::Never => ty,
    }
}

fn type_replacement_key_matches(ty: &Type, needle: &Type) -> bool {
    matches!(needle, Type::OpenVar(_)) && ty == needle
}

fn let_body(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
) -> Result<poly_expr::ExprId, SpecializeError> {
    match arena.defs.get(def) {
        Some(poly_expr::Def::Let {
            body: Some(body), ..
        }) => Ok(*body),
        Some(poly_expr::Def::Let { body: None, .. }) => Err(SpecializeError::MissingBody {
            def: convert_def(def),
        }),
        Some(other) => Err(SpecializeError::UnsupportedDefKind {
            def: convert_def(def),
            kind: def_kind(other),
        }),
        None => Err(SpecializeError::MissingDef {
            def: convert_def(def),
        }),
    }
}

fn operation_scheme_returns_never(arena: &poly_expr::Arena, def: poly_expr::DefId) -> bool {
    let Some(poly_expr::Def::Let {
        scheme: Some(scheme),
        ..
    }) = arena.defs.get(def)
    else {
        return false;
    };
    function_pos_return_is_never(&arena.typ, scheme.predicate)
}

fn function_pos_return_is_never(types: &poly::types::TypeArena, pos: poly::types::PosId) -> bool {
    let poly::types::Pos::Fun { ret, .. } = types.pos(pos) else {
        return false;
    };
    matches!(types.pos(*ret), poly::types::Pos::Bot)
}

fn collect_pattern_defs(
    arena: &poly_expr::Arena,
    pat: poly_expr::PatId,
    out: &mut Vec<poly_expr::DefId>,
) {
    match arena.pat(pat) {
        poly_expr::Pat::Wild | poly_expr::Pat::Lit(_) | poly_expr::Pat::Ref(_) => {}
        poly_expr::Pat::Var(def) => out.push(*def),
        poly_expr::Pat::As(inner, def) => {
            collect_pattern_defs(arena, *inner, out);
            out.push(*def);
        }
        poly_expr::Pat::Tuple(items) | poly_expr::Pat::PolyVariant(_, items) => {
            for item in items {
                collect_pattern_defs(arena, *item, out);
            }
        }
        poly_expr::Pat::Con(_, payloads) => {
            for payload in payloads {
                collect_pattern_defs(arena, *payload, out);
            }
        }
        poly_expr::Pat::Or(left, right) => {
            collect_pattern_defs(arena, *left, out);
            collect_pattern_defs(arena, *right, out);
        }
        poly_expr::Pat::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix.iter().chain(suffix) {
                collect_pattern_defs(arena, *item, out);
            }
            if let Some(spread) = spread {
                collect_pattern_defs(arena, *spread, out);
            }
        }
        poly_expr::Pat::Record { fields, spread } => {
            for field in fields {
                collect_pattern_defs(arena, field.pat, out);
            }
            if let Some(def) = record_spread_def(spread) {
                out.push(def);
            }
        }
    }
}

fn forced_computation_value_type(ty: Type) -> Type {
    match ty {
        Type::Thunk { value, .. } => *value,
        ty => ty,
    }
}

fn raw_expr_value_type(
    arena: &poly_expr::Arena,
    solved: &SolvedTask,
    expr: poly_expr::ExprId,
) -> Option<Type> {
    let actual = solved.actual_type_of(expr)?;
    match arena.expr(expr) {
        poly_expr::Expr::App(callee, _) if callee_is_constructor_spine(arena, *callee) => {
            Some(ComputationShape::from_runtime_type(actual).value)
        }
        poly_expr::Expr::App(callee, _) => {
            Some(raw_apply_value_type(solved, *callee).unwrap_or_else(|| actual.clone()))
        }
        poly_expr::Expr::Select(_, select) => Some(
            raw_select_value_type(arena, solved, expr, *select).unwrap_or_else(|| actual.clone()),
        ),
        poly_expr::Expr::RefSet(_, _)
        | poly_expr::Expr::Tuple(_)
        | poly_expr::Expr::Record { .. }
        | poly_expr::Expr::PolyVariant(_, _)
        | poly_expr::Expr::Case(_, _)
        | poly_expr::Expr::Catch(_, _)
        | poly_expr::Expr::Block(_, _) => Some(ComputationShape::from_runtime_type(actual).value),
        poly_expr::Expr::Lit(_)
        | poly_expr::Expr::PrimitiveOp(_)
        | poly_expr::Expr::Var(_)
        | poly_expr::Expr::Lambda(_, _) => Some(actual.clone()),
    }
}

fn callee_is_constructor_spine(arena: &poly_expr::Arena, expr: poly_expr::ExprId) -> bool {
    match arena.expr(expr) {
        poly_expr::Expr::Var(ref_id) => arena
            .ref_target(*ref_id)
            .is_some_and(|def| arena.constructors.contains_key(&def)),
        poly_expr::Expr::App(callee, _) => callee_is_constructor_spine(arena, *callee),
        _ => false,
    }
}

fn raw_apply_value_type(solved: &SolvedTask, callee: poly_expr::ExprId) -> Option<Type> {
    let callee_ty = solved
        .emitted_type_of(callee)
        .or_else(|| solved.actual_type_of(callee))?;
    let parts = function_computation_parts(callee_ty)?;
    Some(types::runtime_shape(parts.ret_effect, parts.ret))
}

fn raw_select_value_type(
    arena: &poly_expr::Arena,
    solved: &SolvedTask,
    expr: poly_expr::ExprId,
    select: poly_expr::SelectId,
) -> Option<Type> {
    match arena.select(select).resolution {
        Some(poly_expr::SelectResolution::RecordField) => solved
            .actual_type_of(expr)
            .map(|actual| ComputationShape::from_runtime_type(actual).value),
        Some(poly_expr::SelectResolution::Method { .. }) => solved
            .select_signature(expr)
            .and_then(function_computation_parts)
            .map(|parts| types::runtime_shape(parts.ret_effect, parts.ret)),
        Some(poly_expr::SelectResolution::TypeclassMethod { .. }) => solved
            .typeclass_resolution(expr)
            .map(|resolution| &resolution.signature)
            .and_then(function_computation_parts)
            .map(|parts| types::runtime_shape(parts.ret_effect, parts.ret)),
        None => solved.actual_type_of(expr).cloned(),
    }
}

fn raw_expr_is_computation(
    arena: &poly_expr::Arena,
    solved: &SolvedTask,
    expr: poly_expr::ExprId,
) -> bool {
    solved.is_raw_thunk_computation(expr)
        || matches!(arena.expr(expr), poly_expr::Expr::Catch(_, _))
}

fn lift_raw_expr_to_computation(actual: Option<&Type>, emitted: EmittedExpr) -> EmittedExpr {
    let Some(actual) = actual else {
        return emitted;
    };
    let target = ComputationShape::from_runtime_type(actual);
    let Some(current) = emitted.computation.clone() else {
        return emitted;
    };
    if equivalent_boundary_types(&current.value, &target.value) {
        return EmittedExpr {
            computation: Some(target),
            ..emitted
        };
    }
    if matches!(current.value, Type::Thunk { .. }) {
        return force_emitted_value_thunk(emitted, target);
    }
    coerce_emitted_value(emitted, &target.value, Some(target.effect))
}

fn force_emitted_expr_if_thunk(actual: Option<&Type>, emitted: EmittedExpr) -> Expr {
    let Some(actual @ Type::Thunk { .. }) = actual else {
        return emitted.expr;
    };
    let target = ComputationShape::from_runtime_type(actual);
    let Some(current) = emitted.computation.clone() else {
        return force_expr_if_thunk(actual, emitted.expr);
    };
    if equivalent_boundary_types(&current.value, &target.value) {
        return emitted.expr;
    }
    force_emitted_value_thunk(emitted, target).expr
}

fn force_expr_if_thunk(actual: &Type, expr: Expr) -> Expr {
    let Type::Thunk { value, .. } = actual else {
        return expr;
    };
    boundary_expr(actual, value, expr)
}

fn boundary_emitted_expr(actual: &Type, expected: &Type, emitted: EmittedExpr) -> EmittedExpr {
    if matches!(expected, Type::Any) {
        return emitted;
    }
    let Some(shape) = emitted.computation.clone() else {
        return EmittedExpr::pure(
            boundary_expr(actual, expected, emitted.expr),
            Some(expected.clone()),
        );
    };
    if let Type::Thunk { effect, value } = expected {
        if shape.effect.is_pure_effect() && equivalent_boundary_types(&shape.value, expected) {
            return emitted;
        }
        let body = ensure_emitted_value(emitted, actual, value);
        return make_thunk_from_computation(body, effect.as_ref().clone(), value.as_ref().clone());
    }
    ensure_emitted_value(emitted, actual, expected)
}

fn ensure_emitted_value(emitted: EmittedExpr, actual: &Type, expected: &Type) -> EmittedExpr {
    let Some(shape) = emitted.computation.clone() else {
        return EmittedExpr::pure(
            boundary_expr(actual, expected, emitted.expr),
            Some(expected.clone()),
        );
    };
    if equivalent_boundary_types(&shape.value, expected) {
        return EmittedExpr {
            computation: Some(ComputationShape {
                effect: shape.effect,
                value: expected.clone(),
            }),
            ..emitted
        };
    }
    if matches!(shape.value, Type::Thunk { .. }) {
        let target = forced_value_shape(actual, &shape, expected);
        let forced = force_emitted_value_thunk(emitted, target);
        let Some(forced_shape) = forced.computation.clone() else {
            return forced;
        };
        if equivalent_boundary_types(&forced_shape.value, expected) {
            return forced;
        }
        return coerce_emitted_value(forced, expected, None);
    }
    coerce_emitted_value(emitted, expected, None)
}

fn forced_value_shape(
    actual: &Type,
    current: &ComputationShape,
    expected: &Type,
) -> ComputationShape {
    let actual_shape = ComputationShape::from_runtime_type(actual);
    if equivalent_boundary_types(&actual_shape.value, expected) {
        return ComputationShape {
            value: expected.clone(),
            ..actual_shape
        };
    }
    let Type::Thunk { effect, .. } = &current.value else {
        return ComputationShape {
            effect: current.effect.clone(),
            value: expected.clone(),
        };
    };
    ComputationShape {
        effect: join_emitted_effects(current.effect.clone(), effect.as_ref().clone()),
        value: expected.clone(),
    }
}

fn force_emitted_value_thunk(emitted: EmittedExpr, target: ComputationShape) -> EmittedExpr {
    let Some(current) = emitted.computation.clone() else {
        return emitted;
    };
    let Type::Thunk { effect, value } = current.value else {
        return EmittedExpr {
            computation: Some(target),
            ..emitted
        };
    };
    let source = runtime_effective_thunk_type(*effect, *value);
    let target = runtime_computation_type(target);
    let expr = Expr::new(ExprKind::ForceThunk {
        source,
        target: target.clone(),
        thunk: Box::new(emitted.expr),
    });
    EmittedExpr {
        expr,
        computation: Some(ComputationShape {
            effect: target.effect,
            value: target.value,
        }),
    }
}

fn coerce_emitted_value(
    emitted: EmittedExpr,
    expected: &Type,
    effect: Option<Type>,
) -> EmittedExpr {
    let Some(shape) = emitted.computation.clone() else {
        return EmittedExpr::pure(emitted.expr, Some(expected.clone()));
    };
    if equivalent_boundary_types(&shape.value, expected) {
        return EmittedExpr {
            computation: Some(ComputationShape {
                effect: effect.unwrap_or(shape.effect),
                value: expected.clone(),
            }),
            ..emitted
        };
    }
    let expr = boundary_expr(&shape.value, expected, emitted.expr);
    EmittedExpr {
        expr,
        computation: Some(ComputationShape {
            effect: effect.unwrap_or(shape.effect),
            value: expected.clone(),
        }),
    }
}

fn make_thunk_from_computation(
    emitted: EmittedExpr,
    target_effect: Type,
    target_value: Type,
) -> EmittedExpr {
    let Some(source) = emitted.computation.clone() else {
        return emitted;
    };
    let source = runtime_computation_type(source);
    let target = runtime_effective_thunk_type(target_effect, target_value);
    let target_ty = Type::Thunk {
        effect: Box::new(target.effect.clone()),
        value: Box::new(target.value.clone()),
    };
    let expr = Expr::new(ExprKind::MakeThunk {
        source,
        target,
        body: Box::new(emitted.expr),
    });
    EmittedExpr::pure(expr, Some(target_ty))
}

fn runtime_computation_type(shape: ComputationShape) -> ComputationType {
    ComputationType {
        effect: close_resolved_runtime_surface(shape.effect, TypeSlotKind::Effect),
        value: close_resolved_runtime_surface(shape.value, TypeSlotKind::Value),
    }
}

fn runtime_effective_thunk_type(effect: Type, value: Type) -> EffectiveThunkType {
    EffectiveThunkType {
        effect: close_resolved_runtime_surface(effect, TypeSlotKind::Effect),
        value: close_resolved_runtime_surface(value, TypeSlotKind::Value),
    }
}

fn join_emitted_effects(left: Type, right: Type) -> Type {
    if left.is_pure_effect() {
        return right;
    }
    if right.is_pure_effect() {
        return left;
    }
    let mut items = effect_row_items(&left).to_vec();
    items.extend(effect_row_items(&right).iter().cloned());
    types::simplify_type(Type::EffectRow(items))
}

fn boundary_expr(actual: &Type, expected: &Type, expr: Expr) -> Expr {
    let actual = close_runtime_type_surface(
        erase_negative_only_open_vars(actual.clone()),
        TypeSlotKind::Value,
    );
    let expected = close_runtime_type_surface(
        erase_negative_only_open_vars(expected.clone()),
        TypeSlotKind::Value,
    );
    let actual = &actual;
    let expected = &expected;
    if let (
        Type::Thunk {
            effect: source_effect,
            value: source_value,
        },
        Type::Thunk {
            effect: target_effect,
            value: target_value,
        },
    ) = (actual, expected)
    {
        let forced = Expr::new(ExprKind::ForceThunk {
            source: EffectiveThunkType {
                effect: source_effect.as_ref().clone(),
                value: source_value.as_ref().clone(),
            },
            target: ComputationType {
                effect: source_effect.as_ref().clone(),
                value: source_value.as_ref().clone(),
            },
            thunk: Box::new(expr),
        });
        let body = if equivalent_boundary_types(source_value, target_value) {
            forced
        } else {
            boundary_expr(source_value, target_value, forced)
        };
        return Expr::new(ExprKind::MakeThunk {
            source: ComputationType {
                effect: target_effect.as_ref().clone(),
                value: target_value.as_ref().clone(),
            },
            target: EffectiveThunkType {
                effect: target_effect.as_ref().clone(),
                value: target_value.as_ref().clone(),
            },
            body: Box::new(body),
        });
    }
    if let Type::Thunk { effect, value } = expected
        && equivalent_boundary_types(actual, value)
    {
        return Expr::new(ExprKind::MakeThunk {
            source: ComputationType {
                effect: effect.as_ref().clone(),
                value: actual.clone(),
            },
            target: EffectiveThunkType {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            body: Box::new(expr),
        });
    }
    if let Type::Thunk { effect, value } = actual
        && equivalent_boundary_types(value, expected)
    {
        return Expr::new(ExprKind::ForceThunk {
            source: EffectiveThunkType {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            target: ComputationType {
                effect: effect.as_ref().clone(),
                value: expected.clone(),
            },
            thunk: Box::new(expr),
        });
    }
    if function_boundary_types(actual, expected) {
        return Expr::new(ExprKind::FunctionAdapter {
            source: actual.clone(),
            target: expected.clone(),
            function: Box::new(expr),
            hygiene: hygiene::function_adapter_hygiene(actual, expected),
        });
    }
    Expr::new(ExprKind::Coerce {
        source: actual.clone(),
        target: expected.clone(),
        expr: Box::new(expr),
    })
}

fn function_boundary_types(actual: &Type, expected: &Type) -> bool {
    matches!((actual, expected), (Type::Fun { .. }, Type::Fun { .. }))
}

fn wrap_stack_handler_marker(signature: &Type, body: Expr) -> Expr {
    let Some(path) = stack_handler_marker_path(signature) else {
        return body;
    };
    wrap_stack_handler_marker_body(path, body)
}

fn stack_handler_marker_path(signature: &Type) -> Option<Vec<String>> {
    let Type::Fun { arg, .. } = signature else {
        return None;
    };
    thunk_effect_marker_path(arg)
}

fn thunk_effect_marker_path(ty: &Type) -> Option<Vec<String>> {
    match ty {
        Type::Thunk { effect, .. } => effect_marker_path(effect),
        Type::Stack { inner, .. } => thunk_effect_marker_path(inner),
        _ => None,
    }
}

fn effect_marker_path(effect: &Type) -> Option<Vec<String>> {
    match effect {
        Type::EffectRow(items) => items.iter().find_map(effect_marker_path),
        Type::Con { path, .. } if !path.is_empty() => Some(path.clone()),
        Type::Stack { inner, .. } => effect_marker_path(inner),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            effect_marker_path(left).or_else(|| effect_marker_path(right))
        }
        _ => None,
    }
}

fn wrap_stack_handler_marker_body(path: Vec<String>, body: Expr) -> Expr {
    match body.kind {
        ExprKind::Lambda(param, lambda_body) => Expr::new(ExprKind::Lambda(
            param,
            Box::new(wrap_stack_handler_marker_body(path, *lambda_body)),
        )),
        ExprKind::Catch { body, arms } => Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::MarkerFrame { path, body })),
            arms,
        }),
        ExprKind::FunctionAdapter {
            source,
            target,
            function,
            hygiene,
        } => Expr::new(ExprKind::FunctionAdapter {
            source,
            target,
            function: Box::new(wrap_stack_handler_marker_body(path, *function)),
            hygiene,
        }),
        other => Expr::new(other),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn callback_type(first_ret_effect: Type, final_ret_effect: Type) -> Type {
        Type::Fun {
            arg: Box::new(Type::unit()),
            arg_effect: Box::new(Type::pure_effect()),
            ret_effect: Box::new(first_ret_effect),
            ret: Box::new(Type::Fun {
                arg: Box::new(int_type()),
                arg_effect: Box::new(Type::pure_effect()),
                ret_effect: Box::new(final_ret_effect),
                ret: Box::new(Type::unit()),
            }),
        }
    }

    #[test]
    fn same_path_lower_candidates_unify_invariant_arguments() {
        let arena = poly_expr::Arena::new();
        let mut graph = TypeGraph::new(&arena);
        let left_item = graph.fresh_value();
        let right_item = graph.fresh_value();
        let joined = graph.fresh_value();
        let left_box = con(&["box"], vec![left_item.clone()]);
        let right_box = con(&["box"], vec![right_item.clone()]);

        graph
            .constrain_subtype(
                Type::Union(Box::new(left_box), Box::new(right_box)),
                joined.clone(),
            )
            .unwrap();
        graph
            .constrain_subtype(int_type(), left_item.clone())
            .unwrap();
        graph.solve_constraints().unwrap();
        let solution = graph.solve_slots().unwrap();
        let mut resolver = TypeResolver::new(&graph, &solution);

        assert_eq!(resolver.resolve(&right_item).unwrap(), int_type());
        assert_eq!(
            resolver.resolve(&joined).unwrap(),
            con(&["box"], vec![int_type()])
        );
    }

    #[test]
    fn function_lower_candidates_do_not_unify_ret_effects_invariantly() {
        let arena = poly_expr::Arena::new();
        let mut graph = TypeGraph::new(&arena);
        let callback = graph.fresh_value();
        let effect = graph.fresh_effect();
        let handled = Type::EffectRow(vec![con(&["handled"], Vec::new())]);
        let pure_then_effectful = callback_type(Type::pure_effect(), handled.clone());
        let shared_effect = callback_type(effect.clone(), effect.clone());

        graph
            .constrain_subtype(handled.clone(), effect.clone())
            .unwrap();
        graph
            .constrain_subtype(pure_then_effectful, callback.clone())
            .unwrap();
        graph.constrain_subtype(shared_effect, callback).unwrap();
        graph.solve_constraints().unwrap();

        let solution = graph.solve_slots().unwrap();
        let mut resolver = TypeResolver::new(&graph, &solution);

        assert_eq!(resolver.resolve(&effect).unwrap(), handled);
    }

    #[test]
    fn effect_row_candidates_merge_same_family_arguments() {
        let arena = poly_expr::Arena::new();
        let mut graph = TypeGraph::new(&arena);
        let item = graph.fresh_value();
        let open_sub = con(&["effect", "sub"], vec![item]);
        let int_sub = con(&["effect", "sub"], vec![int_type()]);
        let nondet = con(&["effect", "nondet"], Vec::new());
        let open_row = Type::EffectRow(vec![open_sub, nondet.clone()]);
        let int_row = Type::EffectRow(vec![int_sub.clone(), nondet.clone()]);

        assert_eq!(
            join_type_candidates(&graph, open_row.clone(), int_row.clone()).unwrap(),
            Type::EffectRow(vec![int_sub.clone(), nondet.clone()])
        );
        assert_eq!(
            meet_type_candidates(&graph, open_row, int_row).unwrap(),
            Type::EffectRow(vec![int_sub, nondet])
        );
    }

    #[test]
    fn effect_row_candidate_merges_single_effect_item() {
        let arena = poly_expr::Arena::new();
        let graph = TypeGraph::new(&arena);
        let item = con(&["effect", "item"], vec![int_type()]);
        let row = Type::EffectRow(vec![item.clone()]);

        assert_eq!(
            join_type_candidates(&graph, row.clone(), item.clone()).unwrap(),
            row
        );
        assert_eq!(
            meet_type_candidates(&graph, item.clone(), Type::EffectRow(vec![item.clone()]))
                .unwrap(),
            Type::EffectRow(vec![item])
        );
    }

    #[test]
    fn effect_row_item_payload_candidates_keep_union_and_intersection() {
        let arena = poly_expr::Arena::new();
        let graph = TypeGraph::new(&arena);
        let list_int = list_type(int_type());
        let int_payload = con(&["state"], vec![int_type()]);
        let list_payload = con(&["state"], vec![list_int.clone()]);

        assert_eq!(
            merge_effect_row_item_candidate(
                &graph,
                int_payload.clone(),
                list_payload.clone(),
                CandidateMerge::Join,
            )
            .unwrap(),
            con(
                &["state"],
                vec![types::simplify_type(Type::Union(
                    Box::new(int_type()),
                    Box::new(list_int.clone()),
                ))],
            )
        );
        assert_eq!(
            merge_effect_row_item_candidate(
                &graph,
                int_payload,
                list_payload,
                CandidateMerge::Meet,
            )
            .unwrap(),
            con(
                &["state"],
                vec![types::simplify_type(Type::Intersection(
                    Box::new(int_type()),
                    Box::new(list_int),
                ))],
            )
        );
    }

    #[test]
    fn effect_row_lower_with_tail_refines_to_closed_upper() {
        let arena = poly_expr::Arena::new();
        let mut graph = TypeGraph::new(&arena);
        let tail = graph.fresh_effect();
        let next = con(&["loop", "next"], Vec::new());
        let redo = con(&["loop", "redo"], Vec::new());
        let local = con(&["local"], Vec::new());
        let lower = Type::EffectRow(vec![next.clone(), tail]);
        let upper = Type::EffectRow(vec![redo.clone(), next.clone(), local.clone()]);

        assert_eq!(
            refine_effect_lower_with_upper(&graph, &lower, &upper).unwrap(),
            Some(Type::EffectRow(vec![next, redo, local]))
        );
    }

    #[test]
    fn function_subtyping_compares_split_runtime_return_shapes() {
        let arena = poly_expr::Arena::new();
        let mut graph = TypeGraph::new(&arena);
        let effect = graph.fresh_effect();
        let effect_item = con(&["effect"], Vec::new());
        let effect_row = Type::EffectRow(vec![effect_item.clone()]);
        graph
            .constrain_subtype(effect_row.clone(), effect.clone())
            .unwrap();
        let actual = Type::Fun {
            arg: Box::new(Type::unit()),
            arg_effect: Box::new(Type::pure_effect()),
            ret_effect: Box::new(Type::pure_effect()),
            ret: Box::new(types::runtime_shape(effect.clone(), Type::unit())),
        };
        let expected = Type::Fun {
            arg: Box::new(Type::unit()),
            arg_effect: Box::new(Type::pure_effect()),
            ret_effect: Box::new(effect),
            ret: Box::new(Type::unit()),
        };

        graph.constrain_exact(actual, expected).unwrap();
        graph.solve_constraints().unwrap();

        let solution = graph.solve_slots().unwrap();
        assert!(solution.slots.iter().any(|slot| {
            matches!(slot, Some(Type::EffectRow(items)) if items == &vec![effect_item.clone()])
        }));
    }
}
