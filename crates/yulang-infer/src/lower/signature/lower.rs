use std::collections::HashMap;

use rowan::TextRange;

use crate::diagnostic::{TypeOrigin, TypeOriginKind};
use crate::ids::{NegId, PosId, TypeVar};
use crate::lower::LowerState;
use crate::lower::builtin_types::builtin_source_type_path;
use crate::symbols::{Name, Path};
use crate::types::RecordField;
use crate::types::{Neg, Pos};

use super::{LoweredFunctionSigShape, SigRow, SigType, SigVar};

pub fn lower_pure_sig_pos_id(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
) -> PosId {
    match sig {
        SigType::Fun {
            arg, ret_eff, ret, ..
        } => {
            let arg = lower_pure_sig_neg_id(state, arg, vars);
            let ret_eff = if let Some(row) = ret_eff.as_ref() {
                lower_sig_row_pos_id(state, row, vars)
            } else {
                state.infer.arena.empty_pos_row
            };
            let ret = lower_pure_sig_pos_id(state, ret, vars);
            state.infer.alloc_pos(Pos::Fun {
                arg,
                arg_eff: state.infer.arena.empty_neg_row,
                ret_eff,
                ret,
            })
        }
        SigType::Prim { path, span } => {
            if let Some(var) = scoped_sig_prim_var(path, *span, vars) {
                state.infer.alloc_pos(Pos::Var(sig_var(state, vars, &var)))
            } else if is_never_sig_path(path) {
                state.infer.alloc_pos(Pos::Bot)
            } else {
                state
                    .infer
                    .alloc_pos(Pos::Con(canonical_sig_type_path(state, path), vec![]))
            }
        }
        SigType::Apply { path, args, .. } => {
            let args = args
                .iter()
                .map(|arg| {
                    (
                        lower_pure_sig_pos_id(state, arg, vars),
                        lower_pure_sig_neg_id(state, arg, vars),
                    )
                })
                .collect();
            state
                .infer
                .alloc_pos(Pos::Con(canonical_sig_type_path(state, path), args))
        }
        SigType::Record { fields, .. } => {
            let fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: lower_pure_sig_pos_id(state, &field.ty, vars),
                    optional: field.optional,
                })
                .collect();
            state.infer.alloc_pos(Pos::Record(fields))
        }
        SigType::Tuple { items, .. } => {
            let items = items
                .iter()
                .map(|item| lower_pure_sig_pos_id(state, item, vars))
                .collect();
            state.infer.alloc_pos(Pos::Tuple(items))
        }
        SigType::RecordTailSpread { fields, tail, .. } => {
            let fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: lower_pure_sig_pos_id(state, &field.ty, vars),
                    optional: field.optional,
                })
                .collect();
            let tail = lower_pure_sig_pos_id(state, tail, vars);
            state
                .infer
                .alloc_pos(Pos::RecordTailSpread { fields, tail })
        }
        SigType::RecordHeadSpread { tail, fields, .. } => {
            let tail = lower_pure_sig_pos_id(state, tail, vars);
            let fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: lower_pure_sig_pos_id(state, &field.ty, vars),
                    optional: field.optional,
                })
                .collect();
            state
                .infer
                .alloc_pos(Pos::RecordHeadSpread { tail, fields })
        }
        SigType::Var(var) => state.infer.alloc_pos(Pos::Var(sig_var(state, vars, var))),
        SigType::Unit { .. } => state.infer.alloc_pos(prim_type("unit")),
    }
}

pub fn lower_pure_sig_neg_id(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
) -> NegId {
    match sig {
        SigType::Fun {
            arg, ret_eff, ret, ..
        } => {
            let arg = lower_pure_sig_pos_id(state, arg, vars);
            let ret_eff = if let Some(row) = ret_eff.as_ref() {
                lower_sig_row_neg_id(state, row, vars)
            } else {
                state.infer.arena.empty_neg_row
            };
            let ret = lower_pure_sig_neg_id(state, ret, vars);
            state.infer.alloc_neg(Neg::Fun {
                arg,
                arg_eff: state.infer.arena.empty_pos_row,
                ret_eff,
                ret,
            })
        }
        SigType::Prim { path, span } => {
            if let Some(var) = scoped_sig_prim_var(path, *span, vars) {
                state.infer.alloc_neg(Neg::Var(sig_var(state, vars, &var)))
            } else if is_never_sig_path(path) {
                state.infer.alloc_neg(Neg::Top)
            } else {
                state
                    .infer
                    .alloc_neg(Neg::Con(canonical_sig_type_path(state, path), vec![]))
            }
        }
        SigType::Apply { path, args, .. } => {
            let args = args
                .iter()
                .map(|arg| {
                    (
                        lower_pure_sig_pos_id(state, arg, vars),
                        lower_pure_sig_neg_id(state, arg, vars),
                    )
                })
                .collect();
            state
                .infer
                .alloc_neg(Neg::Con(canonical_sig_type_path(state, path), args))
        }
        SigType::Record { fields, .. } => {
            let fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: lower_pure_sig_neg_id(state, &field.ty, vars),
                    optional: field.optional,
                })
                .collect();
            state.infer.alloc_neg(Neg::Record(fields))
        }
        SigType::Tuple { items, .. } => {
            let items = items
                .iter()
                .map(|item| lower_pure_sig_neg_id(state, item, vars))
                .collect();
            state.infer.alloc_neg(Neg::Tuple(items))
        }
        SigType::RecordTailSpread { .. } | SigType::RecordHeadSpread { .. } => {
            panic!("record spread types are only supported in positive positions")
        }
        SigType::Var(var) => state.infer.alloc_neg(Neg::Var(sig_var(state, vars, var))),
        SigType::Unit { .. } => state.infer.alloc_neg(neg_prim_type("unit")),
    }
}

pub fn lower_sig_pos_id(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
    effect_path: Path,
    act_arg_tvs: &[TypeVar],
) -> PosId {
    let ty = lower_sig_type(state, sig, vars, effect_path, act_arg_tvs);
    state.infer.alloc_pos(ty)
}

pub fn lower_sig_neg_id(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
    act_arg_tvs: &[TypeVar],
) -> NegId {
    let ty = lower_sig_neg_type(state, sig, vars, act_arg_tvs);
    state.infer.alloc_neg(ty)
}

pub fn lower_pure_sig_type(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
) -> Pos {
    let id = lower_pure_sig_pos_id(state, sig, vars);
    state.infer.arena.get_pos(id).clone()
}

pub fn lower_pure_sig_neg_type(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
) -> Neg {
    let id = lower_pure_sig_neg_id(state, sig, vars);
    state.infer.arena.get_neg(id).clone()
}

pub fn lower_function_sig_shape(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
) -> Option<LoweredFunctionSigShape> {
    let SigType::Fun {
        arg, ret_eff, ret, ..
    } = sig
    else {
        return None;
    };

    let arg_pos = lower_pure_sig_pos_id(state, arg, vars);
    let arg_neg = lower_pure_sig_neg_id(state, arg, vars);
    let ret_pos = lower_pure_sig_pos_id(state, ret, vars);
    let ret_neg = lower_pure_sig_neg_id(state, ret, vars);
    let (ret_eff_pos, ret_eff_neg, effect_hint) =
        lower_function_sig_ret_eff(state, ret_eff.as_ref(), vars);

    Some(LoweredFunctionSigShape {
        arg_pos,
        arg_neg,
        ret_pos,
        ret_neg,
        ret_eff_pos,
        ret_eff_neg,
        effect_hint,
    })
}

fn lower_sig_type(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
    effect_path: Path,
    act_arg_tvs: &[TypeVar],
) -> Pos {
    match sig {
        SigType::Fun {
            arg, ret_eff, ret, ..
        } => {
            let ret_is_fun = matches!(ret.as_ref(), SigType::Fun { .. });
            let ret_ty = lower_sig_type(state, ret, vars, effect_path.clone(), act_arg_tvs);
            let ret_eff = if let Some(row) = ret_eff {
                lower_sig_row_pos(state, row, vars)
            } else if ret_is_fun {
                state.pos_row(vec![], Pos::Bot)
            } else {
                state.pos_row(
                    vec![Pos::Atom(crate::types::EffectAtom {
                        path: effect_path,
                        args: act_arg_tvs.iter().map(|tv| (*tv, *tv)).collect(),
                    })],
                    Pos::Bot,
                )
            };
            let arg = lower_sig_neg_type(state, arg, vars, act_arg_tvs);
            let arg_eff = state.neg_row(vec![], Neg::Top);
            state.pos_fun(arg, arg_eff, ret_eff, ret_ty)
        }
        SigType::Prim { path, .. } => {
            if is_never_sig_path(path) {
                Pos::Bot
            } else {
                state.pos_con(canonical_sig_type_path(state, path), vec![])
            }
        }
        SigType::Apply { path, args, .. } => {
            let args = args
                .iter()
                .map(|arg| {
                    let pos =
                        lower_sig_type(state, arg, vars, Path { segments: vec![] }, act_arg_tvs);
                    let neg = lower_sig_neg_type(state, arg, vars, act_arg_tvs);
                    (pos, neg)
                })
                .collect();
            state.pos_con(canonical_sig_type_path(state, path), args)
        }
        SigType::Record { fields, .. } => {
            let fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: lower_sig_type(
                        state,
                        &field.ty,
                        vars,
                        Path { segments: vec![] },
                        act_arg_tvs,
                    ),
                    optional: field.optional,
                })
                .collect();
            state.pos_record(fields)
        }
        SigType::Tuple { items, .. } => {
            let items = items
                .iter()
                .map(|item| {
                    lower_sig_type(state, item, vars, Path { segments: vec![] }, act_arg_tvs)
                })
                .collect();
            state.pos_tuple(items)
        }
        SigType::RecordTailSpread { fields, tail, .. } => {
            let fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: lower_sig_type(
                        state,
                        &field.ty,
                        vars,
                        Path { segments: vec![] },
                        act_arg_tvs,
                    ),
                    optional: field.optional,
                })
                .collect();
            let tail = lower_sig_type(state, tail, vars, Path { segments: vec![] }, act_arg_tvs);
            state.pos_record_tail_spread(fields, tail)
        }
        SigType::RecordHeadSpread { tail, fields, .. } => {
            let tail = lower_sig_type(state, tail, vars, Path { segments: vec![] }, act_arg_tvs);
            let fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: lower_sig_type(
                        state,
                        &field.ty,
                        vars,
                        Path { segments: vec![] },
                        act_arg_tvs,
                    ),
                    optional: field.optional,
                })
                .collect();
            state.pos_record_head_spread(tail, fields)
        }
        SigType::Var(var) => Pos::Var(sig_var(state, vars, var)),
        SigType::Unit { .. } => prim_type("unit"),
    }
}

fn lower_sig_neg_type(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
    act_arg_tvs: &[TypeVar],
) -> Neg {
    match sig {
        SigType::Fun {
            arg, ret_eff, ret, ..
        } => {
            let arg = lower_sig_type(state, arg, vars, Path { segments: vec![] }, act_arg_tvs);
            let arg_eff = state.pos_row(vec![], Pos::Bot);
            let ret_eff = ret_eff
                .as_ref()
                .map(|row| lower_sig_row_neg(state, row, vars))
                .unwrap_or_else(|| {
                    state
                        .infer
                        .arena
                        .get_neg(state.infer.arena.empty_neg_row)
                        .clone()
                });
            let ret = lower_sig_neg_type(state, ret, vars, act_arg_tvs);
            state.neg_fun(arg, arg_eff, ret_eff, ret)
        }
        SigType::Prim { path, .. } => {
            if is_never_sig_path(path) {
                Neg::Top
            } else {
                state.neg_con(canonical_sig_type_path(state, path), vec![])
            }
        }
        SigType::Apply { path, args, .. } => {
            let args = args
                .iter()
                .map(|arg| {
                    let pos =
                        lower_sig_type(state, arg, vars, Path { segments: vec![] }, act_arg_tvs);
                    let neg = lower_sig_neg_type(state, arg, vars, act_arg_tvs);
                    (pos, neg)
                })
                .collect();
            state.neg_con(canonical_sig_type_path(state, path), args)
        }
        SigType::Record { fields, .. } => {
            let fields = fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: lower_sig_neg_type(state, &field.ty, vars, act_arg_tvs),
                    optional: field.optional,
                })
                .collect();
            state.neg_record(fields)
        }
        SigType::Tuple { items, .. } => {
            let item_negs = items
                .iter()
                .map(|item| lower_sig_neg_type(state, item, vars, act_arg_tvs))
                .collect::<Vec<_>>();
            let items = item_negs
                .into_iter()
                .map(|item| state.infer.alloc_neg(item))
                .collect();
            Neg::Tuple(items)
        }
        SigType::RecordTailSpread { .. } | SigType::RecordHeadSpread { .. } => {
            panic!("record spread types are only supported in positive positions")
        }
        SigType::Var(var) => Neg::Var(sig_var(state, vars, var)),
        SigType::Unit { .. } => neg_prim_type("unit"),
    }
}

fn lower_sig_row_pos(
    state: &mut LowerState,
    row: &SigRow,
    vars: &mut HashMap<String, TypeVar>,
) -> Pos {
    let items = row
        .items
        .iter()
        .filter_map(|item| lower_sig_effect_atom(state, item, vars).map(Pos::Atom))
        .collect::<Vec<_>>();
    let tail = row
        .tail
        .as_ref()
        .map(|var| {
            let tv = sig_var(state, vars, var);
            state.infer.mark_through(tv);
            Pos::Var(tv)
        })
        .unwrap_or(Pos::Bot);
    state.pos_row(items, tail)
}

fn lower_sig_row_pos_id(
    state: &mut LowerState,
    row: &SigRow,
    vars: &mut HashMap<String, TypeVar>,
) -> PosId {
    let row = lower_sig_row_pos(state, row, vars);
    state.infer.alloc_pos(row)
}

fn lower_sig_row_neg(
    state: &mut LowerState,
    row: &SigRow,
    vars: &mut HashMap<String, TypeVar>,
) -> Neg {
    let items = row
        .items
        .iter()
        .filter_map(|item| lower_sig_effect_atom(state, item, vars).map(Neg::Atom))
        .collect::<Vec<_>>();
    let tail = row
        .tail
        .as_ref()
        .map(|var| {
            let tv = sig_var(state, vars, var);
            state.infer.mark_through(tv);
            Neg::Var(tv)
        })
        .unwrap_or_else(|| {
            state
                .infer
                .arena
                .get_neg(state.infer.arena.empty_neg_row)
                .clone()
        });
    state.neg_row(items, tail)
}

fn lower_sig_row_neg_id(
    state: &mut LowerState,
    row: &SigRow,
    vars: &mut HashMap<String, TypeVar>,
) -> NegId {
    let row = lower_sig_row_neg(state, row, vars);
    state.infer.alloc_neg(row)
}

fn lower_sig_effect_atom(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
) -> Option<crate::types::EffectAtom> {
    match sig {
        SigType::Prim { path, .. } => Some(crate::types::EffectAtom {
            path: canonical_sig_type_path(state, path),
            args: vec![],
        }),
        SigType::Apply { path, args, .. } => Some(crate::types::EffectAtom {
            path: canonical_sig_type_path(state, path),
            args: args
                .iter()
                .map(|arg| lower_sig_effect_arg(state, arg, vars))
                .collect(),
        }),
        _ => None,
    }
}

pub fn lower_sig_effect_arg(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
) -> (TypeVar, TypeVar) {
    if let SigType::Var(var) = sig {
        let tv = sig_var(state, vars, var);
        return (tv, tv);
    }
    let pos_tv = fresh_sig_annotation_tv(state, sig.span(), "effect argument");
    let neg_tv = fresh_sig_annotation_tv(state, sig.span(), "effect argument");
    let pos = lower_pure_sig_type(state, sig, vars);
    let neg = lower_pure_sig_neg_type(state, sig, vars);
    state.infer.constrain(pos, Neg::Var(pos_tv));
    state.infer.constrain(Pos::Var(neg_tv), neg);
    (pos_tv, neg_tv)
}

pub(super) fn scoped_sig_prim_var(
    path: &Path,
    span: TextRange,
    vars: &HashMap<String, TypeVar>,
) -> Option<SigVar> {
    if path.segments.len() != 1 {
        return None;
    }
    let name = path.segments[0].0.clone();
    vars.contains_key(&name).then_some(SigVar { name, span })
}

pub(super) fn canonical_sig_type_path(state: &LowerState, path: &Path) -> Path {
    state.ctx.canonical_current_type_path(path)
}

pub(super) fn sig_var(
    state: &LowerState,
    vars: &mut HashMap<String, TypeVar>,
    var: &SigVar,
) -> TypeVar {
    let key = sig_var_key(var);
    if let Some(tv) = vars.get(&key) {
        return *tv;
    }
    let tv = state.fresh_tv_with_origin(TypeOrigin {
        span: Some(var.span),
        kind: TypeOriginKind::Annotation,
        label: Some(format!("'{}", var.name)),
    });
    vars.insert(key, tv);
    tv
}

fn lower_function_sig_ret_eff(
    state: &mut LowerState,
    ret_eff: Option<&SigRow>,
    vars: &mut HashMap<String, TypeVar>,
) -> (PosId, NegId, bool) {
    let Some(row) = ret_eff else {
        return (
            state.infer.arena.empty_pos_row,
            state.infer.arena.empty_neg_row,
            false,
        );
    };

    if row.items.is_empty() {
        if let Some(tail) = &row.tail {
            let tv = sig_var(state, vars, tail);
            return (
                state.infer.alloc_pos(Pos::Var(tv)),
                state.infer.alloc_neg(Neg::Var(tv)),
                false,
            );
        }
        return (
            state.infer.arena.empty_pos_row,
            state.infer.arena.empty_neg_row,
            false,
        );
    }

    let tail_tv = if let Some(tail) = &row.tail {
        let tv = sig_var(state, vars, tail);
        state.infer.mark_through(tv);
        tv
    } else {
        let tv = fresh_sig_annotation_tv(state, row.items[0].span(), "function latent effect");
        state.infer.mark_through(tv);
        tv
    };
    let pos_items = row
        .items
        .iter()
        .filter_map(|item| lower_sig_effect_atom(state, item, vars).map(Pos::Atom))
        .collect::<Vec<_>>();
    let neg_items = row
        .items
        .iter()
        .filter_map(|item| lower_sig_effect_atom(state, item, vars).map(Neg::Atom))
        .collect::<Vec<_>>();
    (
        state
            .infer
            .alloc_pos(state.pos_row(pos_items, Pos::Var(tail_tv))),
        state
            .infer
            .alloc_neg(state.neg_row(neg_items, Neg::Var(tail_tv))),
        false,
    )
}

fn sig_var_key(var: &SigVar) -> String {
    if var.name == "_" {
        format!(
            "_@{}:{}",
            u32::from(var.span.start()),
            u32::from(var.span.end())
        )
    } else {
        var.name.clone()
    }
}

fn fresh_sig_annotation_tv(
    state: &LowerState,
    span: TextRange,
    label: impl Into<String>,
) -> TypeVar {
    state.fresh_tv_with_origin(TypeOrigin {
        span: Some(span),
        kind: TypeOriginKind::Annotation,
        label: Some(label.into()),
    })
}

fn prim_type(name: &str) -> Pos {
    if name == "never" {
        return Pos::Bot;
    }
    Pos::Con(builtin_source_type_path(name), vec![])
}

fn neg_prim_type(name: &str) -> Neg {
    if name == "never" {
        return Neg::Top;
    }
    Neg::Con(builtin_source_type_path(name), vec![])
}

fn is_never_sig_path(path: &Path) -> bool {
    matches!(path.segments.as_slice(), [Name(name)] if name == "never")
}
