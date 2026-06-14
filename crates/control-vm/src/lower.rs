//! Lowering from the tree-shaped `mono` program into the control IR arena.

use std::fmt;

use crate::ir::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprId, Instance, InstanceId, Pat, Program, RecordField,
    RecordSpread, Root, SelectResolution, Stmt,
};

pub fn lower(program: &mono::Program) -> Result<Program, LowerError> {
    Lowerer::default().lower_program(program)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerError {
    MismatchedInstanceSlot {
        expected: InstanceId,
        actual: InstanceId,
    },
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchedInstanceSlot { expected, actual } => write!(
                f,
                "mismatched instance slot while lowering: expected m{}, found m{}",
                expected.0, actual.0
            ),
        }
    }
}

impl std::error::Error for LowerError {}

#[derive(Debug, Default)]
struct Lowerer {
    exprs: Vec<Expr>,
}

impl Lowerer {
    fn lower_program(mut self, program: &mono::Program) -> Result<Program, LowerError> {
        let roots = program
            .roots
            .iter()
            .map(|root| self.lower_root(root))
            .collect::<Result<Vec<_>, _>>()?;
        let instances = program
            .instances
            .iter()
            .enumerate()
            .map(|(index, instance)| self.lower_instance(index, instance))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Program {
            roots,
            instances,
            exprs: self.exprs,
        })
    }

    fn lower_root(&mut self, root: &mono::Root) -> Result<Root, LowerError> {
        match root {
            mono::Root::Instance(instance) => Ok(Root::Instance(convert_instance(*instance))),
            mono::Root::EvalInstance(instance) => {
                Ok(Root::EvalInstance(convert_instance(*instance)))
            }
            mono::Root::Expr(expr) => Ok(Root::Expr(self.lower_expr(expr)?)),
        }
    }

    fn lower_instance(
        &mut self,
        index: usize,
        instance: &mono::Instance,
    ) -> Result<Instance, LowerError> {
        let expected = InstanceId(index as u32);
        let actual = convert_instance(instance.id);
        if expected != actual {
            return Err(LowerError::MismatchedInstanceSlot { expected, actual });
        }
        Ok(Instance {
            id: actual,
            source: instance.source.clone(),
            signature: instance.signature.clone(),
            entry: self.lower_expr(&instance.body)?,
        })
    }

    fn lower_expr(&mut self, expr: &mono::Expr) -> Result<ExprId, LowerError> {
        use mono::ExprKind as MonoExpr;
        let lowered = match &expr.kind {
            MonoExpr::Lit(lit) => Expr::Lit(lit.clone()),
            MonoExpr::PrimitiveOp { op, context } => Expr::PrimitiveOp {
                op: *op,
                context: context.clone(),
            },
            MonoExpr::Constructor { def, arity } => Expr::Constructor {
                def: convert_def(*def),
                arity: *arity,
            },
            MonoExpr::EffectOp { path } => Expr::EffectOp { path: path.clone() },
            MonoExpr::Local(def) => Expr::Local(convert_def(*def)),
            MonoExpr::InstanceRef(instance) => Expr::InstanceRef(convert_instance(*instance)),
            MonoExpr::Coerce {
                source,
                target,
                expr,
            } => Expr::Coerce {
                source: source.clone(),
                target: target.clone(),
                expr: self.lower_expr(expr)?,
            },
            MonoExpr::MakeThunk {
                source,
                target,
                body,
            } => Expr::MakeThunk {
                source: source.clone(),
                target: target.clone(),
                body: self.lower_expr(body)?,
            },
            MonoExpr::ForceThunk {
                source,
                target,
                thunk,
            } => Expr::ForceThunk {
                source: source.clone(),
                target: target.clone(),
                thunk: self.lower_expr(thunk)?,
            },
            MonoExpr::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => Expr::FunctionAdapter {
                source: source.clone(),
                target: target.clone(),
                function: self.lower_expr(function)?,
                hygiene: hygiene.clone(),
            },
            MonoExpr::MarkerFrame { path, body } => Expr::MarkerFrame {
                path: path.clone(),
                body: self.lower_expr(body)?,
            },
            MonoExpr::Apply(callee, arg) => Expr::Apply {
                callee: self.lower_expr(callee)?,
                arg: self.lower_expr(arg)?,
            },
            MonoExpr::RefSet(reference, value) => Expr::RefSet {
                reference: self.lower_expr(reference)?,
                value: self.lower_expr(value)?,
            },
            MonoExpr::Lambda(param, body) => Expr::Lambda {
                param: lower_pat(param),
                body: self.lower_expr(body)?,
            },
            MonoExpr::Tuple(items) => Expr::Tuple(self.lower_exprs(items)?),
            MonoExpr::Record { fields, spread } => Expr::Record {
                fields: fields
                    .iter()
                    .map(|field| {
                        Ok(RecordField {
                            name: field.name.clone(),
                            value: self.lower_expr(&field.value)?,
                        })
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?,
                spread: self.lower_spread(spread)?,
            },
            MonoExpr::PolyVariant { tag, payloads } => Expr::PolyVariant {
                tag: tag.clone(),
                payloads: self.lower_exprs(payloads)?,
            },
            MonoExpr::Select {
                base,
                name,
                resolution,
            } => Expr::Select {
                base: self.lower_expr(base)?,
                name: name.clone(),
                resolution: resolution.as_ref().map(lower_select_resolution),
            },
            MonoExpr::Case { scrutinee, arms } => Expr::Case {
                scrutinee: self.lower_expr(scrutinee)?,
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CaseArm {
                            pat: lower_pat(&arm.pat),
                            guard: self.lower_optional_expr(arm.guard.as_ref())?,
                            body: self.lower_expr(&arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?,
            },
            MonoExpr::Catch { body, arms } => Expr::Catch {
                body: self.lower_expr(body)?,
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CatchArm {
                            operation_path: arm.operation_path.clone(),
                            pat: lower_pat(&arm.pat),
                            continuation: arm.continuation.as_ref().map(lower_pat),
                            guard: self.lower_optional_expr(arm.guard.as_ref())?,
                            body: self.lower_expr(&arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?,
            },
            MonoExpr::Block(block) => Expr::Block(self.lower_block(block)?),
        };
        let id = ExprId(self.exprs.len() as u32);
        self.exprs.push(lowered);
        Ok(id)
    }

    fn lower_exprs(&mut self, exprs: &[mono::Expr]) -> Result<Vec<ExprId>, LowerError> {
        exprs.iter().map(|expr| self.lower_expr(expr)).collect()
    }

    fn lower_optional_expr(
        &mut self,
        expr: Option<&mono::Expr>,
    ) -> Result<Option<ExprId>, LowerError> {
        expr.map(|expr| self.lower_expr(expr)).transpose()
    }

    fn lower_block(&mut self, block: &mono::Block) -> Result<Block, LowerError> {
        Ok(Block {
            stmts: block
                .stmts
                .iter()
                .map(|stmt| self.lower_stmt(stmt))
                .collect::<Result<Vec<_>, _>>()?,
            tail: self.lower_optional_expr(block.tail.as_deref())?,
        })
    }

    fn lower_stmt(&mut self, stmt: &mono::Stmt) -> Result<Stmt, LowerError> {
        match stmt {
            mono::Stmt::Let(vis, pat, value) => {
                Ok(Stmt::Let(*vis, lower_pat(pat), self.lower_expr(value)?))
            }
            mono::Stmt::Expr(expr) => Ok(Stmt::Expr(self.lower_expr(expr)?)),
            mono::Stmt::Module(def, stmts) => Ok(Stmt::Module(
                convert_def(*def),
                stmts
                    .iter()
                    .map(|stmt| self.lower_stmt(stmt))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
        }
    }

    fn lower_spread(
        &mut self,
        spread: &mono::RecordSpread<Box<mono::Expr>>,
    ) -> Result<RecordSpread<ExprId>, LowerError> {
        match spread {
            mono::RecordSpread::None => Ok(RecordSpread::None),
            mono::RecordSpread::Head(expr) => Ok(RecordSpread::Head(self.lower_expr(expr)?)),
            mono::RecordSpread::Tail(expr) => Ok(RecordSpread::Tail(self.lower_expr(expr)?)),
        }
    }
}

fn lower_pat(pat: &mono::Pat) -> Pat {
    match pat {
        mono::Pat::Wild => Pat::Wild,
        mono::Pat::Lit(lit) => Pat::Lit(lit.clone()),
        mono::Pat::Tuple(items) => Pat::Tuple(items.iter().map(lower_pat).collect()),
        mono::Pat::List {
            prefix,
            spread,
            suffix,
        } => Pat::List {
            prefix: prefix.iter().map(lower_pat).collect(),
            spread: spread.as_deref().map(lower_pat).map(Box::new),
            suffix: suffix.iter().map(lower_pat).collect(),
        },
        mono::Pat::Record { fields, spread } => Pat::Record {
            fields: fields
                .iter()
                .map(|(name, pat)| (name.clone(), lower_pat(pat)))
                .collect(),
            spread: lower_def_spread(spread),
        },
        mono::Pat::PolyVariant(tag, payloads) => {
            Pat::PolyVariant(tag.clone(), payloads.iter().map(lower_pat).collect())
        }
        mono::Pat::Con(def, payloads) => {
            Pat::Con(convert_def(*def), payloads.iter().map(lower_pat).collect())
        }
        mono::Pat::Ref(instance) => Pat::Ref(convert_instance(*instance)),
        mono::Pat::Var(def) => Pat::Var(convert_def(*def)),
        mono::Pat::Or(left, right) => {
            Pat::Or(Box::new(lower_pat(left)), Box::new(lower_pat(right)))
        }
        mono::Pat::As(pat, def) => Pat::As(Box::new(lower_pat(pat)), convert_def(*def)),
    }
}

fn lower_def_spread(spread: &mono::RecordSpread<mono::DefId>) -> RecordSpread<DefId> {
    match spread {
        mono::RecordSpread::None => RecordSpread::None,
        mono::RecordSpread::Head(def) => RecordSpread::Head(convert_def(*def)),
        mono::RecordSpread::Tail(def) => RecordSpread::Tail(convert_def(*def)),
    }
}

fn lower_select_resolution(resolution: &mono::SelectResolution) -> SelectResolution {
    match resolution {
        mono::SelectResolution::RecordField => SelectResolution::RecordField,
        mono::SelectResolution::Method { instance } => SelectResolution::Method {
            instance: convert_instance(*instance),
        },
        mono::SelectResolution::TypeclassMethod { member } => SelectResolution::TypeclassMethod {
            member: convert_def(*member),
        },
    }
}

fn convert_def(def: mono::DefId) -> DefId {
    DefId(def.0)
}

fn convert_instance(instance: mono::InstanceId) -> InstanceId {
    InstanceId(instance.0)
}
