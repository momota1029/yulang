//! `mono` instance 内で erased expression に型を割り当てる作業状態。
//!
//! `poly` は式 node ごとの型を保持しない。ここでは instance/root ごとに主型と erased IR から
//! use-site の concrete 型を再構成し、mono IR へ写す段階が参照する plan だけを残す。

use std::collections::HashMap;

use mono::Type;
use poly::expr as poly_expr;

use crate::{SpecializeError, convert_def, def_kind, lit_type, types};

#[derive(Debug, Clone, Default)]
pub(crate) struct ExprTypePlan {
    types: HashMap<poly_expr::ExprId, Type>,
}

impl ExprTypePlan {
    pub(crate) fn type_of(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.types.get(&expr)
    }

    fn set_type(&mut self, expr: poly_expr::ExprId, ty: Type) -> Result<(), SpecializeError> {
        if let Some(existing) = self.types.get(&expr) {
            if existing == &ty {
                return Ok(());
            }
            return Err(SpecializeError::ConflictingExprType {
                expr: expr.0,
                existing: existing.clone(),
                incoming: ty,
            });
        }
        self.types.insert(expr, ty);
        Ok(())
    }
}

pub(crate) fn solve_expr(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
    expected: Option<&Type>,
) -> Result<ExprTypePlan, SpecializeError> {
    let mut solver = ExprTypeSolver {
        arena,
        plan: ExprTypePlan::default(),
    };
    solver.expr(expr, expected.cloned())?;
    Ok(solver.plan)
}

struct ExprTypeSolver<'a> {
    arena: &'a poly_expr::Arena,
    plan: ExprTypePlan,
}

impl<'a> ExprTypeSolver<'a> {
    fn expr(
        &mut self,
        expr: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        use poly_expr::Expr as PolyExpr;
        let inferred = match self.arena.expr(expr) {
            PolyExpr::Lit(lit) => Some(lit_type(lit)),
            PolyExpr::PrimitiveOp(_) => expected.clone(),
            PolyExpr::Var(ref_id) => self.var_type(*ref_id, expected.as_ref())?,
            PolyExpr::App(callee, arg) => self.apply_type(*callee, *arg, expected.as_ref())?,
            PolyExpr::RefSet(reference, value) => {
                self.expr(*reference, None)?;
                self.expr(*value, None)?;
                Some(Type::unit())
            }
            PolyExpr::Lambda(_, body) => self.lambda_type(*body, expected.as_ref())?,
            PolyExpr::Tuple(items) => self.tuple_type(items, expected.as_ref())?,
            PolyExpr::Record { fields, spread } => {
                for (_, value) in fields {
                    self.expr(*value, None)?;
                }
                self.record_spread(spread)?;
                expected.clone()
            }
            PolyExpr::PolyVariant(_, payloads) => {
                for payload in payloads {
                    self.expr(*payload, None)?;
                }
                expected.clone()
            }
            PolyExpr::Select(base, _) => {
                self.expr(*base, None)?;
                expected.clone()
            }
            PolyExpr::Case(scrutinee, arms) => {
                self.expr(*scrutinee, None)?;
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.expr(guard, Some(bool_type()))?;
                    }
                    self.expr(arm.body, expected.clone())?;
                }
                expected.clone()
            }
            PolyExpr::Catch(body, arms) => {
                self.expr(*body, expected.clone())?;
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.expr(guard, Some(bool_type()))?;
                    }
                    self.expr(arm.body, expected.clone())?;
                }
                expected.clone()
            }
            PolyExpr::Block(stmts, tail) => self.block_type(stmts, *tail, expected.as_ref())?,
        };
        let chosen = match (expected, inferred) {
            (Some(expected), Some(inferred)) if expected == inferred => Some(expected),
            (Some(expected), Some(inferred)) => {
                self.plan.set_type(expr, inferred.clone())?;
                Some(expected)
            }
            (Some(expected), None) => Some(expected),
            (None, inferred) => inferred,
        };
        if let Some(ty) = &chosen {
            self.plan.set_type(expr, ty.clone())?;
        }
        Ok(chosen)
    }

    fn apply_type(
        &mut self,
        callee: poly_expr::ExprId,
        arg: poly_expr::ExprId,
        expected: Option<&Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        let arg_hint = self.expr(arg, None)?;
        let callee_expected = self.callee_function_type(callee, arg_hint.as_ref(), expected)?;
        let callee_expected = callee_expected.or_else(|| {
            arg_hint
                .clone()
                .zip(expected.cloned())
                .map(|(arg, ret)| types::pure_function_type(arg, ret))
        });
        let (arg_expected, ret_hint) = match &callee_expected {
            Some(Type::Fun { arg, ret, .. }) => (Some(arg.as_ref()), Some(ret.as_ref())),
            _ => (None, None),
        };
        self.expr(callee, callee_expected.clone())?;
        if let Some(arg_expected) = arg_expected {
            self.expr(arg, Some(arg_expected.clone()))?;
        }
        Ok(expected.cloned().or_else(|| ret_hint.cloned()))
    }

    fn lambda_type(
        &mut self,
        body: poly_expr::ExprId,
        expected: Option<&Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        match expected {
            Some(Type::Fun { ret, .. }) => {
                self.expr(body, Some(ret.as_ref().clone()))?;
                Ok(expected.cloned())
            }
            Some(expected) => {
                self.expr(body, None)?;
                Ok(Some(expected.clone()))
            }
            None => {
                self.expr(body, None)?;
                Ok(None)
            }
        }
    }

    fn tuple_type(
        &mut self,
        items: &[poly_expr::ExprId],
        expected: Option<&Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        let expected_items = match expected {
            Some(Type::Tuple(expected_items)) if expected_items.len() == items.len() => {
                Some(expected_items.as_slice())
            }
            _ => None,
        };
        let mut item_types = Vec::with_capacity(items.len());
        for (index, item) in items.iter().enumerate() {
            let expected = expected_items.and_then(|items| items.get(index)).cloned();
            item_types.push(self.expr(*item, expected)?);
        }
        if let Some(expected) = expected {
            return Ok(Some(expected.clone()));
        }
        Ok(item_types
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .map(Type::Tuple))
    }

    fn block_type(
        &mut self,
        stmts: &[poly_expr::Stmt],
        tail: Option<poly_expr::ExprId>,
        expected: Option<&Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        for stmt in stmts {
            match stmt {
                poly_expr::Stmt::Let(_, _, value) | poly_expr::Stmt::Expr(value) => {
                    self.expr(*value, None)?;
                }
                poly_expr::Stmt::Module(_, body) => {
                    self.block_type(body, None, None)?;
                }
            }
        }
        match tail {
            Some(tail) => self.expr(tail, expected.cloned()),
            None => Ok(Some(Type::unit())),
        }
    }

    fn record_spread(
        &mut self,
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
    ) -> Result<(), SpecializeError> {
        match spread {
            poly_expr::RecordSpread::Head(expr) | poly_expr::RecordSpread::Tail(expr) => {
                self.expr(*expr, None)?;
            }
            poly_expr::RecordSpread::None => {}
        }
        Ok(())
    }

    fn var_type(
        &mut self,
        ref_id: poly_expr::RefId,
        expected: Option<&Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if let Some(expected) = expected {
            self.require_var_target(def)?;
            return Ok(Some(expected.clone()));
        }
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                ..
            }) => types::type_hint_for_scheme(self.arena, def, scheme),
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => Ok(None),
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

    fn require_var_target(&self, def: poly_expr::DefId) -> Result<(), SpecializeError> {
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(_), ..
            })
            | Some(poly_expr::Def::Arg)
            | Some(poly_expr::Def::Let { body: None, .. }) => Ok(()),
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

    fn callee_function_type(
        &mut self,
        callee: poly_expr::ExprId,
        arg: Option<&Type>,
        ret: Option<&Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some((def, scheme)) = self.callee_scheme(callee)? else {
            return Ok(None);
        };
        Ok(
            types::function_signature_for_scheme(self.arena, def, scheme, arg, ret)?
                .map(|sig| sig.ty),
        )
    }

    fn callee_scheme(
        &mut self,
        callee: poly_expr::ExprId,
    ) -> Result<Option<(poly_expr::DefId, &'a poly::types::Scheme)>, SpecializeError> {
        let poly_expr::Expr::Var(ref_id) = self.arena.expr(callee) else {
            return Ok(None);
        };
        let Some(def) = self.arena.ref_target(*ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                ..
            }) => Ok(Some((def, scheme))),
            Some(poly_expr::Def::Let { scheme: None, .. }) => Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            }),
            Some(poly_expr::Def::Arg) => Ok(None),
            Some(other) => Err(SpecializeError::UnsupportedDefKind {
                def: convert_def(def),
                kind: def_kind(other),
            }),
            None => Err(SpecializeError::MissingDef {
                def: convert_def(def),
            }),
        }
    }
}

fn bool_type() -> Type {
    Type::Con {
        path: vec!["bool".to_string()],
        args: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use mono::Type;

    use super::solve_expr;

    #[test]
    fn root_generic_call_gets_types_for_apply_callee_and_arg() {
        let lowering = lower_source("my id x = x\nid(1)\n");
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("root expression should solve");

        let poly::expr::Expr::App(callee, arg) = arena.expr(root) else {
            panic!("root should be an apply");
        };
        assert_eq!(mono::dump::dump_type(plan.type_of(root).unwrap()), "int");
        assert_eq!(
            mono::dump::dump_type(plan.type_of(*callee).unwrap()),
            "int -> int"
        );
        assert_eq!(plan.type_of(*arg), Some(&int_type()));
    }

    fn int_type() -> Type {
        Type::Con {
            path: vec!["int".to_string()],
            args: Vec::new(),
        }
    }

    fn lower_source(source: &str) -> infer::lowering::BodyLowering {
        let files = sources::load(vec![sources::SourceFile {
            module_path: sources::Path::default(),
            source: source.to_string(),
        }]);
        let output = infer::dump::dump_loaded_files(&files).expect("source should lower");
        assert!(
            output.lowering.errors.is_empty(),
            "body lowering errors: {:?}",
            output.lowering.errors
        );
        output.lowering
    }
}
