use std::collections::HashMap;

use crate::ast::expr::{
    CatchArmKind, ExprKind, PatKind, RecordPatField, RecordPatSpread, RecordSpread, TypedBlock,
    TypedCatchArm, TypedExpr, TypedPat, TypedStmt,
};
use crate::ids::{DefId, NegId, PosId, TypeVar};
use crate::lower::LowerState;
use crate::symbols::Path;
use crate::types::{EffectAtom, Neg, Pos, RecordField};

pub(crate) fn transform_copied_principal_body(
    state: &mut LowerState,
    expr: &TypedExpr,
    def_subst: &HashMap<DefId, DefId>,
    tv_subst: &[(TypeVar, TypeVar)],
    source_path: &Path,
    dest_path: &Path,
    dest_args: &[(TypeVar, TypeVar)],
) -> TypedExpr {
    let mut types = CopiedTypeVars::new(state, tv_subst, source_path, dest_path, dest_args);
    transform_copied_principal_body_inner(&mut types, expr, def_subst)
}

fn transform_copied_principal_body_inner(
    types: &mut CopiedTypeVars<'_>,
    expr: &TypedExpr,
    def_subst: &HashMap<DefId, DefId>,
) -> TypedExpr {
    TypedExpr {
        tv: types.copy_tv(expr.tv),
        eff: types.copy_tv(expr.eff),
        kind: transform_copied_expr_kind(types, &expr.kind, def_subst),
    }
}

fn transform_copied_expr_kind(
    types: &mut CopiedTypeVars<'_>,
    kind: &ExprKind,
    def_subst: &HashMap<DefId, DefId>,
) -> ExprKind {
    match kind {
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(*op),
        ExprKind::Lit(lit) => ExprKind::Lit(lit.clone()),
        ExprKind::Var(def) => ExprKind::Var(def_subst.get(def).copied().unwrap_or(*def)),
        ExprKind::Ref(ref_id) => types
            .state
            .ctx
            .refs
            .get(*ref_id)
            .and_then(|def| def_subst.get(&def).copied())
            .map(ExprKind::Var)
            .unwrap_or(ExprKind::Ref(*ref_id)),
        ExprKind::App(callee, arg) => ExprKind::App(
            Box::new(transform_copied_principal_body_inner(
                types, callee, def_subst,
            )),
            Box::new(transform_copied_principal_body_inner(types, arg, def_subst)),
        ),
        ExprKind::RefSet { reference, value } => ExprKind::RefSet {
            reference: Box::new(transform_copied_principal_body_inner(
                types, reference, def_subst,
            )),
            value: Box::new(transform_copied_principal_body_inner(
                types, value, def_subst,
            )),
        },
        ExprKind::Lam(def, body) => ExprKind::Lam(
            *def,
            Box::new(transform_copied_principal_body_inner(
                types, body, def_subst,
            )),
        ),
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .iter()
                .map(|item| transform_copied_principal_body_inner(types, item, def_subst))
                .collect(),
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .iter()
                .map(|(name, value)| {
                    (
                        name.clone(),
                        transform_copied_principal_body_inner(types, value, def_subst),
                    )
                })
                .collect(),
            spread: spread.as_ref().map(|spread| match spread {
                RecordSpread::Head(expr) => RecordSpread::Head(Box::new(
                    transform_copied_principal_body_inner(types, expr, def_subst),
                )),
                RecordSpread::Tail(expr) => RecordSpread::Tail(Box::new(
                    transform_copied_principal_body_inner(types, expr, def_subst),
                )),
            }),
        },
        ExprKind::PolyVariant(tag, payloads) => ExprKind::PolyVariant(
            tag.clone(),
            payloads
                .iter()
                .map(|payload| transform_copied_principal_body_inner(types, payload, def_subst))
                .collect(),
        ),
        ExprKind::Select { recv, name } => ExprKind::Select {
            recv: Box::new(transform_copied_principal_body_inner(
                types, recv, def_subst,
            )),
            name: name.clone(),
        },
        ExprKind::Match(scrutinee, arms) => ExprKind::Match(
            Box::new(transform_copied_principal_body_inner(
                types, scrutinee, def_subst,
            )),
            arms.iter()
                .map(|arm| crate::ast::expr::TypedMatchArm {
                    pat: transform_copied_pat(&arm.pat, types, def_subst),
                    guard: arm.guard.as_ref().map(|guard| {
                        transform_copied_principal_body_inner(types, guard, def_subst)
                    }),
                    body: transform_copied_principal_body_inner(types, &arm.body, def_subst),
                })
                .collect(),
        ),
        ExprKind::Catch(body, arms) => ExprKind::Catch(
            Box::new(transform_copied_principal_body_inner(
                types, body, def_subst,
            )),
            arms.iter()
                .map(|arm| TypedCatchArm {
                    tv: types.copy_tv(arm.tv),
                    guard: arm.guard.as_ref().map(|guard| {
                        transform_copied_principal_body_inner(types, guard, def_subst)
                    }),
                    kind: match &arm.kind {
                        CatchArmKind::Value(pat, body) => CatchArmKind::Value(
                            transform_copied_pat(pat, types, def_subst),
                            transform_copied_principal_body_inner(types, body, def_subst),
                        ),
                        CatchArmKind::Effect {
                            op_path,
                            pat,
                            k,
                            body,
                        } => CatchArmKind::Effect {
                            op_path: replace_copied_effect_path(
                                op_path,
                                types.source_path,
                                types.dest_path,
                            ),
                            pat: transform_copied_pat(pat, types, def_subst),
                            k: *k,
                            body: transform_copied_principal_body_inner(types, body, def_subst),
                        },
                    },
                })
                .collect(),
        ),
        ExprKind::Block(block) => ExprKind::Block(transform_copied_block(block, types, def_subst)),
        ExprKind::Coerce {
            actual_tv,
            expected_tv,
            expr,
        } => ExprKind::Coerce {
            actual_tv: types.copy_tv(*actual_tv),
            expected_tv: types.copy_tv(*expected_tv),
            expr: Box::new(transform_copied_principal_body_inner(
                types, expr, def_subst,
            )),
        },
        ExprKind::PackForall(var, expr) => ExprKind::PackForall(
            types.copy_tv(*var),
            Box::new(transform_copied_principal_body_inner(
                types, expr, def_subst,
            )),
        ),
    }
}

fn transform_copied_block(
    block: &TypedBlock,
    types: &mut CopiedTypeVars<'_>,
    def_subst: &HashMap<DefId, DefId>,
) -> TypedBlock {
    TypedBlock {
        tv: types.copy_tv(block.tv),
        eff: types.copy_tv(block.eff),
        stmts: block
            .stmts
            .iter()
            .map(|stmt| match stmt {
                TypedStmt::Let(pat, value) => TypedStmt::Let(
                    transform_copied_pat(pat, types, def_subst),
                    transform_copied_principal_body_inner(types, value, def_subst),
                ),
                TypedStmt::Expr(expr) => TypedStmt::Expr(transform_copied_principal_body_inner(
                    types, expr, def_subst,
                )),
                TypedStmt::Module(def, body) => TypedStmt::Module(
                    def_subst.get(def).copied().unwrap_or(*def),
                    transform_copied_block(body, types, def_subst),
                ),
            })
            .collect(),
        tail: block.tail.as_ref().map(|tail| {
            Box::new(transform_copied_principal_body_inner(
                types, tail, def_subst,
            ))
        }),
    }
}

fn transform_copied_pat(
    pat: &TypedPat,
    types: &mut CopiedTypeVars<'_>,
    def_subst: &HashMap<DefId, DefId>,
) -> TypedPat {
    TypedPat {
        tv: types.copy_tv(pat.tv),
        kind: match &pat.kind {
            PatKind::Wild => PatKind::Wild,
            PatKind::Lit(lit) => PatKind::Lit(lit.clone()),
            PatKind::Tuple(items) => PatKind::Tuple(
                items
                    .iter()
                    .map(|item| transform_copied_pat(item, types, def_subst))
                    .collect(),
            ),
            PatKind::List {
                prefix,
                spread,
                suffix,
            } => PatKind::List {
                prefix: prefix
                    .iter()
                    .map(|item| transform_copied_pat(item, types, def_subst))
                    .collect(),
                spread: spread
                    .as_ref()
                    .map(|spread| Box::new(transform_copied_pat(spread, types, def_subst))),
                suffix: suffix
                    .iter()
                    .map(|item| transform_copied_pat(item, types, def_subst))
                    .collect(),
            },
            PatKind::Record { spread, fields } => PatKind::Record {
                spread: spread.as_ref().map(|spread| match spread {
                    RecordPatSpread::Head(pat) => {
                        RecordPatSpread::Head(Box::new(transform_copied_pat(pat, types, def_subst)))
                    }
                    RecordPatSpread::Tail(pat) => {
                        RecordPatSpread::Tail(Box::new(transform_copied_pat(pat, types, def_subst)))
                    }
                }),
                fields: fields
                    .iter()
                    .map(|field| RecordPatField {
                        name: field.name.clone(),
                        pat: transform_copied_pat(&field.pat, types, def_subst),
                        default: field.default.as_ref().map(|default| {
                            transform_copied_principal_body_inner(types, default, def_subst)
                        }),
                    })
                    .collect(),
            },
            PatKind::PolyVariant(tag, items) => PatKind::PolyVariant(
                tag.clone(),
                items
                    .iter()
                    .map(|item| transform_copied_pat(item, types, def_subst))
                    .collect(),
            ),
            PatKind::Con(ref_id, payload) => PatKind::Con(
                *ref_id,
                payload
                    .as_ref()
                    .map(|payload| Box::new(transform_copied_pat(payload, types, def_subst))),
            ),
            PatKind::UnresolvedName(name) => PatKind::UnresolvedName(name.clone()),
            PatKind::Or(lhs, rhs) => PatKind::Or(
                Box::new(transform_copied_pat(lhs, types, def_subst)),
                Box::new(transform_copied_pat(rhs, types, def_subst)),
            ),
            PatKind::As(pattern, def) => PatKind::As(
                Box::new(transform_copied_pat(pattern, types, def_subst)),
                *def,
            ),
        },
    }
}

fn replace_copied_effect_path(path: &Path, source_path: &Path, dest_path: &Path) -> Path {
    if path.segments.starts_with(&source_path.segments) {
        let mut segments = dest_path.segments.clone();
        segments.extend_from_slice(&path.segments[source_path.segments.len()..]);
        Path { segments }
    } else {
        path.clone()
    }
}

struct CopiedTypeVars<'a> {
    state: &'a mut LowerState,
    fixed: HashMap<TypeVar, TypeVar>,
    copied: HashMap<TypeVar, TypeVar>,
    source_path: &'a Path,
    dest_path: &'a Path,
    dest_args: &'a [(TypeVar, TypeVar)],
}

impl<'a> CopiedTypeVars<'a> {
    fn new(
        state: &'a mut LowerState,
        fixed: &[(TypeVar, TypeVar)],
        source_path: &'a Path,
        dest_path: &'a Path,
        dest_args: &'a [(TypeVar, TypeVar)],
    ) -> Self {
        Self {
            state,
            fixed: fixed.iter().copied().collect(),
            copied: HashMap::new(),
            source_path,
            dest_path,
            dest_args,
        }
    }

    fn copy_tv(&mut self, tv: TypeVar) -> TypeVar {
        if let Some(mapped) = self.fixed.get(&tv).copied() {
            return mapped;
        }
        if let Some(mapped) = self.copied.get(&tv).copied() {
            return mapped;
        }

        let level = self.state.infer.level_of(tv);
        let mapped = match self.state.infer.origin_of(tv) {
            Some(origin) => self.state.fresh_tv_at_origin(level, origin),
            None => self.state.fresh_tv_at(level),
        };
        self.copied.insert(tv, mapped);

        let lowers = self.state.infer.lowers_of(tv);
        for lower in lowers {
            let lower = self.copy_pos(lower);
            self.state.infer.add_lower(mapped, lower);
        }

        let uppers = self.state.infer.uppers_of(tv);
        for upper in uppers {
            let upper = self.copy_neg(upper);
            self.state.infer.add_upper(mapped, upper);
        }

        if self.state.infer.is_through(tv) {
            self.state.infer.mark_through(mapped);
        }

        mapped
    }

    fn copy_pos_id(&mut self, id: PosId) -> PosId {
        let pos = self.state.infer.arena.get_pos(id);
        let pos = self.copy_pos(pos);
        self.state.infer.alloc_pos(pos)
    }

    fn copy_neg_id(&mut self, id: NegId) -> NegId {
        let neg = self.state.infer.arena.get_neg(id);
        let neg = self.copy_neg(neg);
        self.state.infer.alloc_neg(neg)
    }

    fn copy_pos(&mut self, pos: Pos) -> Pos {
        match pos {
            Pos::Bot => Pos::Bot,
            Pos::Var(tv) => Pos::Var(self.copy_tv(tv)),
            Pos::Atom(atom) => Pos::Atom(self.copy_effect_atom(atom)),
            Pos::Forall(vars, body) => Pos::Forall(
                vars.into_iter().map(|var| self.copy_tv(var)).collect(),
                self.copy_pos_id(body),
            ),
            Pos::Con(path, args) => Pos::Con(
                replace_copied_effect_path(&path, self.source_path, self.dest_path),
                args.into_iter()
                    .map(|(pos, neg)| (self.copy_pos_id(pos), self.copy_neg_id(neg)))
                    .collect(),
            ),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Pos::Fun {
                arg: self.copy_neg_id(arg),
                arg_eff: self.copy_neg_id(arg_eff),
                ret_eff: self.copy_pos_id(ret_eff),
                ret: self.copy_pos_id(ret),
            },
            Pos::Record(fields) => Pos::Record(
                fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.copy_pos_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.copy_pos_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
                tail: self.copy_pos_id(tail),
            },
            Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
                tail: self.copy_pos_id(tail),
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.copy_pos_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
            },
            Pos::PolyVariant(items) => Pos::PolyVariant(
                items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.copy_pos_id(payload))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Pos::Tuple(items) => Pos::Tuple(
                items
                    .into_iter()
                    .map(|item| self.copy_pos_id(item))
                    .collect(),
            ),
            Pos::Row(items, tail) => Pos::Row(
                items
                    .into_iter()
                    .map(|item| self.copy_pos_id(item))
                    .collect(),
                self.copy_pos_id(tail),
            ),
            Pos::Union(lhs, rhs) => Pos::Union(self.copy_pos_id(lhs), self.copy_pos_id(rhs)),
            Pos::Raw(tv) => Pos::Raw(self.copy_tv(tv)),
        }
    }

    fn copy_neg(&mut self, neg: Neg) -> Neg {
        match neg {
            Neg::Top => Neg::Top,
            Neg::Var(tv) => Neg::Var(self.copy_tv(tv)),
            Neg::Atom(atom) => Neg::Atom(self.copy_effect_atom(atom)),
            Neg::Forall(vars, body) => Neg::Forall(
                vars.into_iter().map(|var| self.copy_tv(var)).collect(),
                self.copy_neg_id(body),
            ),
            Neg::Con(path, args) => Neg::Con(
                replace_copied_effect_path(&path, self.source_path, self.dest_path),
                args.into_iter()
                    .map(|(pos, neg)| (self.copy_pos_id(pos), self.copy_neg_id(neg)))
                    .collect(),
            ),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neg::Fun {
                arg: self.copy_pos_id(arg),
                arg_eff: self.copy_pos_id(arg_eff),
                ret_eff: self.copy_neg_id(ret_eff),
                ret: self.copy_neg_id(ret),
            },
            Neg::Record(fields) => Neg::Record(
                fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.copy_neg_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Neg::PolyVariant(items) => Neg::PolyVariant(
                items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.copy_neg_id(payload))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Neg::Tuple(items) => Neg::Tuple(
                items
                    .into_iter()
                    .map(|item| self.copy_neg_id(item))
                    .collect(),
            ),
            Neg::Row(items, tail) => Neg::Row(
                items
                    .into_iter()
                    .map(|item| self.copy_neg_id(item))
                    .collect(),
                self.copy_neg_id(tail),
            ),
            Neg::Intersection(lhs, rhs) => {
                Neg::Intersection(self.copy_neg_id(lhs), self.copy_neg_id(rhs))
            }
        }
    }

    fn copy_effect_atom(&mut self, atom: EffectAtom) -> EffectAtom {
        if atom.path == *self.source_path {
            return EffectAtom {
                path: self.dest_path.clone(),
                args: self.dest_args.to_vec(),
            };
        }
        EffectAtom {
            path: replace_copied_effect_path(&atom.path, self.source_path, self.dest_path),
            args: atom
                .args
                .into_iter()
                .map(|(pos, neg)| (self.copy_tv(pos), self.copy_tv(neg)))
                .collect(),
        }
    }
}
