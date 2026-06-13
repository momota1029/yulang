//! `poly::Arena` から `mono::Program` を作る単一化 crate。
//!
//! この crate は yulang2 系の後段入口であり、旧 typed IR や旧 monomorphize の evidence を読まない。
//! 主型と文脈型から monomorphize 用の signature を作り、到達した定義だけを `mono` instance 化する。

#![forbid(unsafe_code)]

mod types;

use std::collections::HashMap;
use std::fmt;

use mono::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprKind, Instance, InstanceId, InstanceSource, Lit,
    Pat, Program, RecordField, RecordSpread, Root, SelectResolution, Stmt, Type, Vis,
};
use poly::expr as poly_expr;

pub use mono;

#[derive(Debug, Clone, Default)]
pub struct Specializer {
    instances: Vec<Option<Instance>>,
    instance_by_key: HashMap<InstanceKey, InstanceId>,
}

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
            poly_expr::RuntimeRoot::Expr(expr) => Ok(Root::Expr(self.expr(arena, expr, None)?)),
            poly_expr::RuntimeRoot::ComputedDef(def) => {
                Ok(Root::Instance(self.ensure_def_instance(arena, def, None)?))
            }
        }
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

        let body = self.expr(arena, body, Some(&signature.ty))?;
        self.instances[id.0 as usize] = Some(Instance {
            id,
            source: InstanceSource::Def(convert_def(def)),
            signature,
            body,
        });
        Ok(id)
    }

    fn expr(
        &mut self,
        arena: &poly_expr::Arena,
        expr: poly_expr::ExprId,
        expected: Option<&Type>,
    ) -> Result<Expr, SpecializeError> {
        use poly_expr::Expr as PolyExpr;
        let kind = match arena.expr(expr) {
            PolyExpr::Lit(lit) => ExprKind::Lit(convert_lit(lit)),
            PolyExpr::PrimitiveOp(op) => ExprKind::PrimitiveOp(format!("{op:?}")),
            PolyExpr::Var(ref_id) => self.var(arena, *ref_id, expected)?,
            PolyExpr::App(callee, arg) => self.apply(arena, *callee, *arg, expected)?,
            PolyExpr::RefSet(reference, value) => ExprKind::RefSet(
                Box::new(self.expr(arena, *reference, None)?),
                Box::new(self.expr(arena, *value, None)?),
            ),
            PolyExpr::Lambda(param, body) => {
                let body_expected = match expected {
                    Some(Type::Fun { ret, .. }) => Some(ret.as_ref()),
                    _ => None,
                };
                ExprKind::Lambda(
                    self.pat(arena, *param)?,
                    Box::new(self.expr(arena, *body, body_expected)?),
                )
            }
            PolyExpr::Tuple(items) => ExprKind::Tuple(self.exprs(arena, items, None)?),
            PolyExpr::Record { fields, spread } => ExprKind::Record {
                fields: fields
                    .iter()
                    .map(|(name, value)| {
                        Ok(RecordField {
                            name: name.clone(),
                            value: self.expr(arena, *value, None)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                spread: self.expr_spread(arena, spread)?,
            },
            PolyExpr::PolyVariant(tag, payloads) => ExprKind::PolyVariant {
                tag: tag.clone(),
                payloads: self.exprs(arena, payloads, None)?,
            },
            PolyExpr::Select(base, select) => {
                let select = arena.select(*select);
                ExprKind::Select {
                    base: Box::new(self.expr(arena, *base, None)?),
                    name: select.name.clone(),
                    resolution: self.select_resolution(arena, select.resolution)?,
                }
            }
            PolyExpr::Case(scrutinee, arms) => ExprKind::Case {
                scrutinee: Box::new(self.expr(arena, *scrutinee, None)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CaseArm {
                            pat: self.pat(arena, arm.pat)?,
                            guard: self.optional_expr(arena, arm.guard)?,
                            body: self.expr(arena, arm.body, expected)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            },
            PolyExpr::Catch(body, arms) => ExprKind::Catch {
                body: Box::new(self.expr(arena, *body, expected)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CatchArm {
                            pat: self.pat(arena, arm.pat)?,
                            continuation: self.optional_pat(arena, arm.continuation)?,
                            guard: self.optional_expr(arena, arm.guard)?,
                            body: self.expr(arena, arm.body, expected)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            },
            PolyExpr::Block(stmts, tail) => ExprKind::Block(Block {
                stmts: self.stmts(arena, stmts)?,
                tail: self
                    .optional_expr_with_expected(arena, *tail, expected)?
                    .map(Box::new),
            }),
        };
        Ok(Expr::new(kind))
    }

    fn apply(
        &mut self,
        arena: &poly_expr::Arena,
        callee: poly_expr::ExprId,
        arg: poly_expr::ExprId,
        expected: Option<&Type>,
    ) -> Result<ExprKind, SpecializeError> {
        let arg_hint = self.expr_type_hint(arena, arg)?;
        let callee_expected =
            self.callee_function_type_hint(arena, callee, arg_hint.as_ref(), expected)?;
        let callee_expected = callee_expected.or_else(|| {
            arg_hint
                .clone()
                .zip(expected.cloned())
                .map(|(arg, ret)| types::pure_function_type(arg, ret))
        });
        Ok(ExprKind::Apply(
            Box::new(self.expr(arena, callee, callee_expected.as_ref())?),
            Box::new(self.expr(arena, arg, arg_hint.as_ref())?),
        ))
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
        match arena.defs.get(def) {
            Some(poly_expr::Def::Arg) => Ok(ExprKind::Local(convert_def(def))),
            Some(poly_expr::Def::Let { body: Some(_), .. }) => Ok(ExprKind::InstanceRef(
                self.ensure_def_instance(arena, def, expected)?,
            )),
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

    fn pat(
        &mut self,
        arena: &poly_expr::Arena,
        pat: poly_expr::PatId,
    ) -> Result<Pat, SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match arena.pat(pat) {
            PolyPat::Wild => Ok(Pat::Wild),
            PolyPat::Lit(lit) => Ok(Pat::Lit(convert_lit(lit))),
            PolyPat::Tuple(items) => Ok(Pat::Tuple(self.pats(arena, items)?)),
            PolyPat::List {
                prefix,
                spread,
                suffix,
            } => Ok(Pat::List {
                prefix: self.pats(arena, prefix)?,
                spread: self.optional_pat(arena, *spread)?.map(Box::new),
                suffix: self.pats(arena, suffix)?,
            }),
            PolyPat::Record { fields, spread } => Ok(Pat::Record {
                fields: fields
                    .iter()
                    .map(|(name, pat)| Ok((name.clone(), self.pat(arena, *pat)?)))
                    .collect::<Result<Vec<_>, _>>()?,
                spread: convert_def_spread(spread),
            }),
            PolyPat::PolyVariant(tag, payloads) => {
                Ok(Pat::PolyVariant(tag.clone(), self.pats(arena, payloads)?))
            }
            PolyPat::Con(ref_id, payloads) => {
                let instance = self.ref_instance(arena, *ref_id)?;
                Ok(Pat::Con(instance, self.pats(arena, payloads)?))
            }
            PolyPat::Ref(ref_id) => Ok(Pat::Ref(self.ref_instance(arena, *ref_id)?)),
            PolyPat::Var(def) => Ok(Pat::Var(convert_def(*def))),
            PolyPat::Or(left, right) => Ok(Pat::Or(
                Box::new(self.pat(arena, *left)?),
                Box::new(self.pat(arena, *right)?),
            )),
            PolyPat::As(pat, def) => {
                Ok(Pat::As(Box::new(self.pat(arena, *pat)?), convert_def(*def)))
            }
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
        resolution: Option<poly_expr::SelectResolution>,
    ) -> Result<Option<SelectResolution>, SpecializeError> {
        match resolution {
            None => Ok(None),
            Some(poly_expr::SelectResolution::RecordField) => {
                Ok(Some(SelectResolution::RecordField))
            }
            Some(poly_expr::SelectResolution::Method { def }) => {
                Ok(Some(SelectResolution::Method {
                    instance: self.ensure_def_instance(arena, def, None)?,
                }))
            }
            Some(poly_expr::SelectResolution::TypeclassMethod { member }) => {
                Ok(Some(SelectResolution::TypeclassMethod {
                    member: convert_def(member),
                }))
            }
        }
    }

    fn exprs(
        &mut self,
        arena: &poly_expr::Arena,
        exprs: &[poly_expr::ExprId],
        expected: Option<&Type>,
    ) -> Result<Vec<Expr>, SpecializeError> {
        exprs
            .iter()
            .map(|expr| self.expr(arena, *expr, expected))
            .collect()
    }

    fn pats(
        &mut self,
        arena: &poly_expr::Arena,
        pats: &[poly_expr::PatId],
    ) -> Result<Vec<Pat>, SpecializeError> {
        pats.iter().map(|pat| self.pat(arena, *pat)).collect()
    }

    fn optional_expr(
        &mut self,
        arena: &poly_expr::Arena,
        expr: Option<poly_expr::ExprId>,
    ) -> Result<Option<Expr>, SpecializeError> {
        self.optional_expr_with_expected(arena, expr, None)
    }

    fn optional_expr_with_expected(
        &mut self,
        arena: &poly_expr::Arena,
        expr: Option<poly_expr::ExprId>,
        expected: Option<&Type>,
    ) -> Result<Option<Expr>, SpecializeError> {
        expr.map(|expr| self.expr(arena, expr, expected))
            .transpose()
    }

    fn optional_pat(
        &mut self,
        arena: &poly_expr::Arena,
        pat: Option<poly_expr::PatId>,
    ) -> Result<Option<Pat>, SpecializeError> {
        pat.map(|pat| self.pat(arena, pat)).transpose()
    }

    fn stmts(
        &mut self,
        arena: &poly_expr::Arena,
        stmts: &[poly_expr::Stmt],
    ) -> Result<Vec<Stmt>, SpecializeError> {
        stmts
            .iter()
            .map(|stmt| match stmt {
                poly_expr::Stmt::Let(vis, pat, value) => Ok(Stmt::Let(
                    convert_vis(*vis),
                    self.pat(arena, *pat)?,
                    self.expr(arena, *value, None)?,
                )),
                poly_expr::Stmt::Expr(expr) => Ok(Stmt::Expr(self.expr(arena, *expr, None)?)),
                poly_expr::Stmt::Module(def, body) => {
                    Ok(Stmt::Module(convert_def(*def), self.stmts(arena, body)?))
                }
            })
            .collect()
    }

    fn expr_spread(
        &mut self,
        arena: &poly_expr::Arena,
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
    ) -> Result<RecordSpread<Box<Expr>>, SpecializeError> {
        match spread {
            poly_expr::RecordSpread::Head(expr) => {
                Ok(RecordSpread::Head(Box::new(self.expr(arena, *expr, None)?)))
            }
            poly_expr::RecordSpread::Tail(expr) => {
                Ok(RecordSpread::Tail(Box::new(self.expr(arena, *expr, None)?)))
            }
            poly_expr::RecordSpread::None => Ok(RecordSpread::None),
        }
    }

    fn expr_type_hint(
        &mut self,
        arena: &poly_expr::Arena,
        expr: poly_expr::ExprId,
    ) -> Result<Option<Type>, SpecializeError> {
        use poly_expr::Expr as PolyExpr;
        match arena.expr(expr) {
            PolyExpr::Lit(lit) => Ok(Some(lit_type(lit))),
            PolyExpr::Var(ref_id) => {
                let Some(def) = arena.ref_target(*ref_id) else {
                    return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
                };
                match arena.defs.get(def) {
                    Some(poly_expr::Def::Let {
                        scheme: Some(scheme),
                        ..
                    }) => types::type_hint_for_scheme(arena, def, scheme),
                    Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => {
                        Ok(None)
                    }
                    Some(poly_expr::Def::Let { scheme: None, .. }) => {
                        Err(SpecializeError::MissingScheme {
                            def: convert_def(def),
                        })
                    }
                    Some(other) => Err(SpecializeError::UnsupportedDefKind {
                        def: convert_def(def),
                        kind: def_kind(other),
                    }),
                    None => Err(SpecializeError::MissingDef {
                        def: convert_def(def),
                    }),
                }
            }
            PolyExpr::Tuple(items) => items
                .iter()
                .map(|item| self.expr_type_hint(arena, *item))
                .collect::<Result<Option<Vec<_>>, _>>()
                .map(|items| items.map(Type::Tuple)),
            PolyExpr::App(callee, arg) => {
                let arg_hint = self.expr_type_hint(arena, *arg)?;
                self.callee_return_type_hint(arena, *callee, arg_hint.as_ref())
            }
            _ => Ok(None),
        }
    }

    fn callee_function_type_hint(
        &mut self,
        arena: &poly_expr::Arena,
        callee: poly_expr::ExprId,
        arg: Option<&Type>,
        ret: Option<&Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some((def, scheme)) = self.callee_scheme(arena, callee)? else {
            return Ok(None);
        };
        Ok(types::function_signature_for_scheme(arena, def, scheme, arg, ret)?.map(|sig| sig.ty))
    }

    fn callee_return_type_hint(
        &mut self,
        arena: &poly_expr::Arena,
        callee: poly_expr::ExprId,
        arg: Option<&Type>,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some((def, scheme)) = self.callee_scheme(arena, callee)? else {
            return Ok(None);
        };
        types::function_return_hint_for_scheme(arena, def, scheme, arg)
    }

    fn callee_scheme<'a>(
        &mut self,
        arena: &'a poly_expr::Arena,
        callee: poly_expr::ExprId,
    ) -> Result<Option<(poly_expr::DefId, &'a poly::types::Scheme)>, SpecializeError> {
        let poly_expr::Expr::Var(ref_id) = arena.expr(callee) else {
            return Ok(None);
        };
        let Some(def) = arena.ref_target(*ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        match arena.defs.get(def) {
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstanceKey {
    def: poly_expr::DefId,
    ty: Type,
}

pub fn specialize(arena: &poly_expr::Arena) -> Result<Program, SpecializeError> {
    Specializer::new().specialize(arena)
}

pub fn specialize_roots(
    arena: &poly_expr::Arena,
    roots: impl IntoIterator<Item = poly_expr::DefId>,
) -> Result<Program, SpecializeError> {
    Specializer::new().specialize_roots(arena, roots)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecializeError {
    MissingDef {
        def: DefId,
    },
    MissingScheme {
        def: DefId,
    },
    MissingBody {
        def: DefId,
    },
    UnsupportedDefKind {
        def: DefId,
        kind: DefKind,
    },
    UnsupportedSchemeFeature {
        def: DefId,
        feature: SchemeFeature,
    },
    ConflictingTypeSubstitution {
        def: DefId,
        var: u32,
        existing: Type,
        incoming: Type,
    },
    UnresolvedRef {
        ref_id: u32,
    },
    InternalMissingInstance {
        instance: InstanceId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefKind {
    Module,
    Let,
    Arg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchemeFeature {
    RolePredicates,
    RecursiveBounds,
    StackQuantifiers,
}

impl fmt::Display for SpecializeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingDef { def } => write!(f, "missing def d{}", def.0),
            Self::MissingScheme { def } => write!(f, "missing scheme for d{}", def.0),
            Self::MissingBody { def } => write!(f, "missing body for d{}", def.0),
            Self::UnsupportedDefKind { def, kind } => {
                write!(f, "unsupported def kind for d{}: {kind:?}", def.0)
            }
            Self::UnsupportedSchemeFeature { def, feature } => {
                write!(f, "unsupported scheme feature for d{}: {feature:?}", def.0,)
            }
            Self::ConflictingTypeSubstitution {
                def,
                var,
                existing,
                incoming,
            } => {
                write!(
                    f,
                    "conflicting type substitution for d{} 't{}: {} vs {}",
                    def.0,
                    var,
                    mono::dump::dump_type(existing),
                    mono::dump::dump_type(incoming),
                )
            }
            Self::UnresolvedRef { ref_id } => write!(f, "unresolved ref r{ref_id}"),
            Self::InternalMissingInstance { instance } => {
                write!(f, "internal missing mono instance m{}", instance.0)
            }
        }
    }
}

impl std::error::Error for SpecializeError {}

fn convert_lit(lit: &poly_expr::Lit) -> Lit {
    match lit {
        poly_expr::Lit::Int(value) => Lit::Int(*value),
        poly_expr::Lit::BigInt(value) => Lit::BigInt(value.clone()),
        poly_expr::Lit::Float(value) => Lit::Float(*value),
        poly_expr::Lit::Str(value) => Lit::Str(value.clone()),
        poly_expr::Lit::Bool(value) => Lit::Bool(*value),
        poly_expr::Lit::Unit => Lit::Unit,
    }
}

fn lit_type(lit: &poly_expr::Lit) -> Type {
    let name = match lit {
        poly_expr::Lit::Int(_) | poly_expr::Lit::BigInt(_) => "int",
        poly_expr::Lit::Float(_) => "float",
        poly_expr::Lit::Str(_) => "str",
        poly_expr::Lit::Bool(_) => "bool",
        poly_expr::Lit::Unit => "unit",
    };
    Type::Con {
        path: vec![name.to_string()],
        args: Vec::new(),
    }
}

fn convert_vis(vis: poly_expr::Vis) -> Vis {
    match vis {
        poly_expr::Vis::Pub => Vis::Pub,
        poly_expr::Vis::Our => Vis::Our,
        poly_expr::Vis::My => Vis::My,
    }
}

fn convert_def(def: poly_expr::DefId) -> DefId {
    DefId(def.0)
}

fn convert_def_spread(spread: &poly_expr::RecordSpread<poly_expr::DefId>) -> RecordSpread<DefId> {
    match spread {
        poly_expr::RecordSpread::Head(def) => RecordSpread::Head(convert_def(*def)),
        poly_expr::RecordSpread::Tail(def) => RecordSpread::Tail(convert_def(*def)),
        poly_expr::RecordSpread::None => RecordSpread::None,
    }
}

fn def_kind(def: &poly_expr::Def) -> DefKind {
    match def {
        poly_expr::Def::Mod { .. } => DefKind::Module,
        poly_expr::Def::Let { .. } => DefKind::Let,
        poly_expr::Def::Arg => DefKind::Arg,
    }
}

#[cfg(test)]
mod tests {
    use super::{specialize, specialize_roots};
    use mono::{ExprKind, InstanceSource, Lit, Type};

    #[test]
    fn empty_arena_specializes_to_empty_program() {
        let arena = poly::expr::Arena::new();
        let program = specialize(&arena).expect("empty arena should specialize");

        assert!(program.roots.is_empty());
        assert!(program.instances.is_empty());
    }

    #[test]
    fn default_specialize_does_not_treat_arena_roots_as_runtime_demands() {
        let mut arena = poly::expr::Arena::new();
        let def = arena.defs.fresh();
        arena.defs.set(
            def,
            poly::expr::Def::Let {
                vis: poly::expr::Vis::My,
                scheme: None,
                body: None,
                children: Vec::new(),
            },
        );
        arena.roots.push(def);

        let program = specialize(&arena).expect("unused arena roots should not be specialized");

        assert!(program.roots.is_empty());
        assert!(program.instances.is_empty());
    }

    #[test]
    fn string_input_does_not_materialize_unused_generic_binding() {
        let lowering = lower_source("my id x = x\n");

        let program =
            specialize(&lowering.session.poly).expect("unused generic binding should be ignored");

        assert!(program.roots.is_empty());
        assert!(program.instances.is_empty());
    }

    #[test]
    fn string_input_materializes_explicit_monomorphic_root() {
        let lowering = lower_source("my one = 1\n");
        let arena = &lowering.session.poly;
        let root = arena.roots[0];

        let program = specialize_roots(arena, [root]).expect("monomorphic root should specialize");

        assert_eq!(
            program.roots,
            vec![mono::Root::Instance(mono::InstanceId(0))]
        );
        assert_eq!(program.instances.len(), 1);
        assert_eq!(
            program.instances[0].source,
            InstanceSource::Def(mono::DefId(root.0))
        );
        assert_eq!(
            program.instances[0].signature.ty,
            Type::Con {
                path: vec!["int".to_string()],
                args: Vec::new()
            }
        );
        assert_eq!(program.instances[0].body.kind, ExprKind::Lit(Lit::Int(1)));
    }

    #[test]
    fn string_input_materializes_reachable_monomorphic_refs() {
        let lowering = lower_source("my one = 1\nmy two = one\n");
        let arena = &lowering.session.poly;
        let two = arena.roots[1];

        let program =
            specialize_roots(arena, [two]).expect("reachable monomorphic ref should specialize");

        assert_eq!(
            program.roots,
            vec![mono::Root::Instance(mono::InstanceId(0))]
        );
        assert_eq!(program.instances.len(), 2);
        assert_eq!(
            program.instances[0].source,
            InstanceSource::Def(mono::DefId(two.0))
        );
        assert_eq!(
            program.instances[0].body.kind,
            ExprKind::InstanceRef(mono::InstanceId(1))
        );
        assert_eq!(program.instances[1].body.kind, ExprKind::Lit(Lit::Int(1)));
    }

    #[test]
    fn string_input_defaults_explicit_generic_root_without_context() {
        let lowering = lower_source("my id x = x\n");
        let arena = &lowering.session.poly;
        let root = arena.roots[0];

        let program =
            specialize_roots(arena, [root]).expect("generic root should get a default signature");

        assert_eq!(
            mono::dump::dump_type(&program.instances[0].signature.ty),
            "unit -> unit"
        );
    }

    #[test]
    fn string_input_specializes_generic_ref_from_apply_argument_and_result() {
        let lowering = lower_source("my id x = x\nmy one = 1\nmy call = id(one)\n");
        let arena = &lowering.session.poly;
        let call = arena.roots[2];

        let program = specialize_roots(arena, [call])
            .expect("generic callee should specialize from apply context");

        assert_eq!(
            program.roots,
            vec![mono::Root::Instance(mono::InstanceId(0))]
        );
        assert_eq!(program.instances.len(), 3);
        assert_eq!(
            mono::dump::dump_type(&program.instances[1].signature.ty),
            "int -> int"
        );
        assert_eq!(
            program.instances[0].body.kind,
            ExprKind::Apply(
                Box::new(mono::Expr::new(ExprKind::InstanceRef(mono::InstanceId(1)))),
                Box::new(mono::Expr::new(ExprKind::InstanceRef(mono::InstanceId(2))))
            )
        );
    }

    #[test]
    fn string_input_specializes_root_expr_generic_call() {
        let lowering = lower_source("my id x = x\nid(1)\n");
        let arena = &lowering.session.poly;

        let program = specialize(arena).expect("root expr should specialize generic callee");

        assert_eq!(program.roots.len(), 1);
        assert_eq!(
            program.roots[0],
            mono::Root::Expr(mono::Expr::new(ExprKind::Apply(
                Box::new(mono::Expr::new(ExprKind::InstanceRef(mono::InstanceId(0)))),
                Box::new(mono::Expr::new(ExprKind::Lit(Lit::Int(1))))
            )))
        );
        assert_eq!(program.instances.len(), 1);
        assert_eq!(
            mono::dump::dump_type(&program.instances[0].signature.ty),
            "int -> int"
        );
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
