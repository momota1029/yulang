use std::collections::{HashMap, HashSet};

use crate::ids::{TypeVar, fresh_type_var};
use crate::simplify::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRecordSpread, CompactRow,
    CompactType, CompactTypeScheme, CompactVariant,
};
use crate::symbols::{Name, Path};
use crate::types::RecordField;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(TypeVar),
    Prim(Path),
    Con(Path, Vec<CompactBounds>),
    Fun {
        arg: Box<Type>,
        arg_eff: Box<Type>,
        ret_eff: Box<Type>,
        ret: Box<Type>,
    },
    Record(Vec<RecordField<Type>>),
    RecordTailSpread {
        fields: Vec<RecordField<Type>>,
        tail: Box<Type>,
    },
    RecordHeadSpread {
        tail: Box<Type>,
        fields: Vec<RecordField<Type>>,
    },
    Variant(Vec<(Name, Vec<Type>)>),
    Tuple(Vec<Type>),
    Row(Vec<Type>, Box<Type>),
    Union(Vec<Type>),
    Inter(Vec<Type>),
    Rec(TypeVar, Box<Type>),
    Bot,
    Top,
}

pub fn compact_scheme_to_type(scheme: &CompactTypeScheme) -> Type {
    let mut ctx = CompactToTypeCtx::new(scheme);
    let root = normalize_render_bounds(scheme.cty.clone());
    if let Some(fun) = coalesce_root_fun(&mut ctx, &root, true) {
        return simplify_root_type(fun);
    }
    simplify_type(ctx.coalesce_type(&root.lower, true))
}

pub fn compact_side_to_type(
    rec_vars: &std::collections::HashMap<TypeVar, CompactBounds>,
    ty: &CompactType,
    positive: bool,
) -> Type {
    let scheme = CompactTypeScheme {
        cty: CompactBounds::default(),
        rec_vars: rec_vars.clone(),
    };
    let mut ctx = CompactToTypeCtx::new(&scheme);
    simplify_type(ctx.coalesce_type(ty, positive))
}

pub fn format_type(ty: &Type) -> String {
    let mut namer = VarNamer::default();
    format_type_inner(ty, &mut namer, false)
}

pub fn format_coalesced_scheme(scheme: &CompactTypeScheme) -> String {
    format_type(&compact_scheme_to_type(scheme))
}

#[derive(Default)]
struct VarNamer {
    names: HashMap<u32, String>,
    next: usize,
}

impl VarNamer {
    fn name(&mut self, raw: u32) -> String {
        const GREEK: &[&str] = &[
            "α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ", "λ", "μ", "ν", "ξ", "ο", "π", "ρ",
            "σ", "τ", "υ", "φ", "χ", "ψ", "ω",
        ];

        if let Some(name) = self.names.get(&raw) {
            return name.clone();
        }

        let name = if self.next < GREEK.len() {
            GREEK[self.next].to_string()
        } else {
            format!("t{}", self.next)
        };
        self.next += 1;
        self.names.insert(raw, name.clone());
        name
    }
}

struct CompactToTypeCtx<'a> {
    scheme: &'a CompactTypeScheme,
    in_process_vars: HashMap<(TypeVar, bool), TypeVar>,
    recursive_var_hits: HashSet<(TypeVar, bool)>,
    in_process_types: HashMap<(String, bool), TypeVar>,
    recursive_type_hits: HashSet<(String, bool)>,
}

impl<'a> CompactToTypeCtx<'a> {
    fn new(scheme: &'a CompactTypeScheme) -> Self {
        Self {
            scheme,
            in_process_vars: HashMap::new(),
            recursive_var_hits: HashSet::new(),
            in_process_types: HashMap::new(),
            recursive_type_hits: HashSet::new(),
        }
    }

    fn coalesce_var(&mut self, tv: TypeVar, positive: bool) -> Type {
        let key = (tv, positive);
        if let Some(rec_tv) = self.in_process_vars.get(&key) {
            self.recursive_var_hits.insert(key);
            return Type::Var(*rec_tv);
        }

        let Some(bounds) = self.scheme.rec_vars.get(&tv) else {
            return Type::Var(tv);
        };

        let rec_tv = fresh_type_var();
        self.in_process_vars.insert(key, rec_tv);
        let body = if positive {
            self.coalesce_type(&bounds.lower, true)
        } else {
            self.coalesce_type(&bounds.upper, false)
        };
        self.in_process_vars.remove(&key);

        if self.recursive_var_hits.remove(&key) {
            Type::Rec(rec_tv, Box::new(body))
        } else {
            body
        }
    }

    fn coalesce_type(&mut self, ty: &CompactType, positive: bool) -> Type {
        if should_hash_cons_type(ty) {
            let key = (compact_type_key(ty), positive);
            if let Some(rec_tv) = self.in_process_types.get(&key) {
                self.recursive_type_hits.insert(key.clone());
                return Type::Var(*rec_tv);
            }

            let rec_tv = fresh_type_var();
            self.in_process_types.insert(key.clone(), rec_tv);
            let body = self.coalesce_type_body(ty, positive);
            self.in_process_types.remove(&key);

            if self.recursive_type_hits.remove(&key) {
                return Type::Rec(rec_tv, Box::new(body));
            }
            return body;
        }

        self.coalesce_type_body(ty, positive)
    }

    fn coalesce_type_body(&mut self, ty: &CompactType, positive: bool) -> Type {
        let mut parts = Vec::new();

        let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
        vars.sort_by_key(|tv| tv.0);
        parts.extend(vars.into_iter().map(|tv| self.coalesce_var(tv, positive)));

        let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
        prims.sort_by(|a, b| path_string(a).cmp(&path_string(b)));
        parts.extend(prims.into_iter().map(Type::Prim));

        let mut cons = ty.cons.clone();
        cons.sort_by(|a, b| path_string(&a.path).cmp(&path_string(&b.path)));
        parts.extend(cons.into_iter().map(|con| Type::Con(con.path, con.args)));

        parts.extend(ty.funs.iter().map(|fun| self.coalesce_fun(fun, positive)));
        parts.extend(ty.records.iter().map(|record| {
            Type::Record(
                record
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.coalesce_type(&field.value, positive),
                        optional: field.optional,
                    })
                    .collect(),
            )
        }));
        parts.extend(ty.record_spreads.iter().map(|spread| {
            let fields = spread
                .fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: self.coalesce_type(&field.value, positive),
                    optional: field.optional,
                })
                .collect();
            let tail = Box::new(self.coalesce_type(&spread.tail, positive));
            if spread.tail_wins {
                Type::RecordTailSpread { fields, tail }
            } else {
                Type::RecordHeadSpread { tail, fields }
            }
        }));
        parts.extend(ty.variants.iter().map(|variant| {
            Type::Variant(
                variant
                    .items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.coalesce_type(payload, positive))
                                .collect(),
                        )
                    })
                    .collect(),
            )
        }));
        parts.extend(ty.tuples.iter().map(|tuple| {
            Type::Tuple(
                tuple
                    .iter()
                    .map(|item| self.coalesce_type(item, positive))
                    .collect(),
            )
        }));
        parts.extend(ty.rows.iter().map(|row| {
            Type::Row(
                row.items
                    .iter()
                    .map(|item| self.coalesce_type(item, positive))
                    .collect(),
                Box::new(self.coalesce_type(&row.tail, positive)),
            )
        }));

        combine_types(parts, positive)
    }
}

impl CompactToTypeCtx<'_> {
    fn coalesce_fun(&mut self, fun: &CompactFun, positive: bool) -> Type {
        Type::Fun {
            arg: Box::new(self.coalesce_type(&fun.arg, !positive)),
            arg_eff: Box::new(self.coalesce_fun_effect_field(&fun.arg_eff, !positive)),
            ret_eff: Box::new(self.coalesce_fun_effect_field(&fun.ret_eff, positive)),
            ret: Box::new(self.coalesce_type(&fun.ret, positive)),
        }
    }

    fn coalesce_fun_effect_field(&mut self, ty: &CompactType, positive: bool) -> Type {
        if is_empty_compact(ty) || is_explicit_empty_row_compact(ty) {
            Type::Bot
        } else {
            self.coalesce_type(ty, positive)
        }
    }
}

fn coalesce_root_fun(
    ctx: &mut CompactToTypeCtx<'_>,
    bounds: &CompactBounds,
    normalize_fields: bool,
) -> Option<Type> {
    let [lower_fun] = bounds.lower.funs.as_slice() else {
        return None;
    };
    let [upper_fun] = bounds.upper.funs.as_slice() else {
        return None;
    };
    if !root_non_fun_parts_empty(&bounds.lower) || !root_non_fun_parts_empty(&bounds.upper) {
        return None;
    }

    if !normalize_fields {
        let arg = common_compact_type(&lower_fun.arg, &upper_fun.arg)
            .filter(|ty| !is_empty_compact(ty))
            .unwrap_or_else(|| lower_fun.arg.clone());
        let rendered_arg = if is_var_only_compact(&arg) {
            Type::Var(*arg.vars.iter().next().unwrap())
        } else {
            ctx.coalesce_type(&arg, false)
        };

        return Some(Type::Fun {
            arg: Box::new(rendered_arg),
            arg_eff: Box::new(ctx.coalesce_type(&lower_fun.arg_eff, false)),
            ret_eff: Box::new(ctx.coalesce_type(&lower_fun.ret_eff, true)),
            ret: Box::new(ctx.coalesce_type(&lower_fun.ret, true)),
        });
    }

    Some(Type::Fun {
        arg: Box::new(coalesce_root_fun_field(
            ctx,
            &lower_fun.arg,
            &upper_fun.arg,
            false,
        )),
        arg_eff: Box::new(coalesce_root_fun_field(
            ctx,
            &lower_fun.arg_eff,
            &upper_fun.arg_eff,
            false,
        )),
        ret_eff: Box::new(coalesce_root_fun_effect_field(
            ctx,
            &lower_fun.ret_eff,
            &upper_fun.ret_eff,
            true,
        )),
        ret: Box::new(coalesce_root_fun_field(
            ctx,
            &lower_fun.ret,
            &upper_fun.ret,
            true,
        )),
    })
}

fn coalesce_root_fun_effect_field(
    ctx: &mut CompactToTypeCtx<'_>,
    lower: &CompactType,
    upper: &CompactType,
    positive: bool,
) -> Type {
    let bounds = normalize_render_bounds(CompactBounds {
        self_var: None,
        lower: lower.clone(),
        upper: upper.clone(),
    });
    if let Some(fun) = coalesce_root_fun(ctx, &bounds, true) {
        return simplify_type(fun);
    }

    let ty = if positive
        && (is_empty_compact(&bounds.lower) || is_explicit_empty_row_compact(&bounds.lower))
    {
        bounds.upper
    } else if positive {
        bounds.lower
    } else {
        common_compact_type(&bounds.lower, &bounds.upper)
            .filter(|ty| !is_empty_compact(ty))
            .unwrap_or(bounds.lower)
    };

    if is_empty_compact(&ty) || is_explicit_empty_row_compact(&ty) {
        Type::Bot
    } else if is_var_only_compact(&ty) {
        Type::Var(*ty.vars.iter().next().unwrap())
    } else {
        ctx.coalesce_type(&ty, positive)
    }
}

fn coalesce_root_fun_field(
    ctx: &mut CompactToTypeCtx<'_>,
    lower: &CompactType,
    upper: &CompactType,
    positive: bool,
) -> Type {
    let bounds = normalize_render_bounds(CompactBounds {
        self_var: None,
        lower: lower.clone(),
        upper: upper.clone(),
    });
    if let Some(fun) = coalesce_root_fun(ctx, &bounds, true) {
        return simplify_type(fun);
    }

    let ty = if positive {
        bounds.lower
    } else {
        common_compact_type(&bounds.lower, &bounds.upper)
            .filter(|ty| !is_empty_compact(ty))
            .unwrap_or(bounds.lower)
    };

    if is_var_only_compact(&ty) {
        Type::Var(*ty.vars.iter().next().unwrap())
    } else {
        ctx.coalesce_type(&ty, positive)
    }
}

fn simplify_type(ty: Type) -> Type {
    match ty {
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Type::Fun {
            arg: Box::new(simplify_type(*arg)),
            arg_eff: Box::new(simplify_type(*arg_eff)),
            ret_eff: Box::new(simplify_type(*ret_eff)),
            ret: Box::new(simplify_type(*ret)),
        },
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: simplify_type(field.value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::RecordTailSpread { fields, tail } => Type::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: simplify_type(field.value),
                    optional: field.optional,
                })
                .collect(),
            tail: Box::new(simplify_type(*tail)),
        },
        Type::RecordHeadSpread { tail, fields } => Type::RecordHeadSpread {
            tail: Box::new(simplify_type(*tail)),
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: simplify_type(field.value),
                    optional: field.optional,
                })
                .collect(),
        },
        Type::Variant(items) => Type::Variant(
            items
                .into_iter()
                .map(|(name, payloads)| (name, payloads.into_iter().map(simplify_type).collect()))
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(items.into_iter().map(simplify_type).collect()),
        Type::Row(items, tail) => {
            let mut items = items
                .into_iter()
                .map(simplify_type)
                .filter(|item| !is_empty_row(item))
                .collect::<Vec<_>>();
            let mut deduped = Vec::new();
            for item in items.drain(..) {
                if !deduped.contains(&item) {
                    deduped.push(item);
                }
            }
            Type::Row(deduped, Box::new(simplify_type(*tail)))
        }
        Type::Union(items) => {
            let mut out = Vec::new();
            for item in items.into_iter().map(simplify_type) {
                match item {
                    Type::Union(nested) => out.extend(nested),
                    other if !is_empty_row(&other) => out.push(other),
                    _ => {}
                }
            }
            combine_types(out, true)
        }
        Type::Inter(items) => {
            let mut out = Vec::new();
            for item in items.into_iter().map(simplify_type) {
                match item {
                    Type::Inter(nested) => out.extend(nested),
                    other => out.push(other),
                }
            }
            combine_types(out, false)
        }
        Type::Rec(tv, body) => {
            let body = simplify_type(*body);
            if body == Type::Var(tv) {
                Type::Var(tv)
            } else {
                Type::Rec(tv, Box::new(body))
            }
        }
        other => other,
    }
}

fn simplify_root_type(ty: Type) -> Type {
    let ty = simplify_type(ty);
    normalize_root_curried_fun_effect_chain(ty)
}

fn normalize_root_curried_fun_effect_chain(ty: Type) -> Type {
    let Some((mut chain, tail)) = collect_root_fun_chain(ty.clone()) else {
        return ty;
    };

    clear_prefix_latent_effects_before_effectful_arg(&mut chain);

    let latent = common_non_empty_root_ret_effect(&chain);
    if let Some(effect) = latent {
        let last = chain.len().saturating_sub(1);
        for (idx, (_, _, ret_eff)) in chain.iter_mut().enumerate() {
            *ret_eff = Box::new(if idx == last {
                effect.clone()
            } else {
                empty_fun_effect_placeholder()
            });
        }
    }

    rebuild_root_fun_chain(chain, tail)
}

fn clear_prefix_latent_effects_before_effectful_arg(chain: &mut [RootFunLink]) {
    let Some(first_effectful_arg) = chain
        .iter()
        .position(|(_, arg_eff, _)| !is_empty_fun_effect(arg_eff))
    else {
        return;
    };
    for (_, _, ret_eff) in &mut chain[..first_effectful_arg] {
        *ret_eff = Box::new(empty_fun_effect_placeholder());
    }
}

fn is_empty_fun_effect(ty: &Type) -> bool {
    matches!(ty, Type::Bot)
        || is_empty_row(ty)
        || matches!(ty, Type::Row(items, tail) if items.is_empty() && matches!(tail.as_ref(), Type::Top))
}

fn empty_fun_effect_placeholder() -> Type {
    Type::Row(vec![], Box::new(Type::Bot))
}

fn collect_root_fun_chain(mut ty: Type) -> Option<(Vec<RootFunLink>, Type)> {
    let mut chain = Vec::new();

    loop {
        match ty {
            Type::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                chain.push((arg, arg_eff, ret_eff));
                ty = *ret;
            }
            tail => {
                if chain.is_empty() {
                    return None;
                }
                return Some((chain, tail));
            }
        }
    }
}

fn common_non_empty_root_ret_effect(chain: &[RootFunLink]) -> Option<Type> {
    let mut effects = chain.iter().filter_map(|(_, _, ret_eff)| {
        if is_empty_fun_effect(ret_eff) {
            None
        } else {
            Some((**ret_eff).clone())
        }
    });
    let first = effects.next()?;
    if effects.all(|eff| eff == first) {
        Some(first)
    } else {
        None
    }
}

fn rebuild_root_fun_chain(mut chain: Vec<RootFunLink>, tail: Type) -> Type {
    let mut out = tail;
    while let Some((arg, arg_eff, ret_eff)) = chain.pop() {
        out = Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret: Box::new(out),
        };
    }
    out
}

type RootFunLink = (Box<Type>, Box<Type>, Box<Type>);

fn combine_types(parts: Vec<Type>, positive: bool) -> Type {
    let mut flat = Vec::new();
    for part in parts {
        let items = match part {
            Type::Union(items) if positive => items,
            Type::Inter(items) if !positive => items,
            Type::Bot if positive => continue,
            Type::Top if !positive => continue,
            other => vec![other],
        };
        for item in items {
            match item {
                Type::Bot if positive => {}
                Type::Top if !positive => {}
                other if !flat.contains(&other) => flat.push(other),
                _ => {}
            }
        }
    }

    if positive && flat.iter().any(is_float_like_type) {
        flat.retain(|item| !is_int_like_type(item));
    }

    match flat.len() {
        0 => {
            if positive {
                Type::Bot
            } else {
                Type::Top
            }
        }
        1 => flat.into_iter().next().unwrap(),
        _ => {
            if positive {
                Type::Union(flat)
            } else {
                Type::Inter(flat)
            }
        }
    }
}

fn is_float_like_type(ty: &Type) -> bool {
    match ty {
        Type::Prim(path) => path.segments.last().map(|name| name.0.as_str()) == Some("float"),
        Type::Con(path, args) => {
            args.is_empty() && path.segments.last().map(|name| name.0.as_str()) == Some("float")
        }
        _ => false,
    }
}

fn is_int_like_type(ty: &Type) -> bool {
    match ty {
        Type::Prim(path) => path.segments.last().map(|name| name.0.as_str()) == Some("int"),
        Type::Con(path, args) => {
            args.is_empty() && path.segments.last().map(|name| name.0.as_str()) == Some("int")
        }
        _ => false,
    }
}

fn format_type_inner(ty: &Type, namer: &mut VarNamer, needs_paren: bool) -> String {
    match ty {
        Type::Var(tv) => namer.name(tv.0),
        Type::Prim(path) => path_string(path),
        Type::Con(path, args) => {
            let name = path_string(path);
            if args.is_empty() {
                return name;
            }
            let args = args
                .iter()
                .map(|arg| format_compact_bounds(arg, namer))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name}<{args}>")
        }
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            let arg = format_type_inner(arg, namer, true);
            let ret = format_type_inner(ret, namer, false);
            let arg_eff = format_row_inline(arg_eff, namer);
            let ret_eff = format_ret_row_inline(ret_eff, namer);
            let rendered = match (arg_eff, ret_eff) {
                (None, None) => format!("{arg} -> {ret}"),
                (Some(ae), None) => format!("{arg} [{ae}] -> {ret}"),
                (None, Some(re)) => format!("{arg} -> [{re}] {ret}"),
                (Some(ae), Some(re)) => format!("{arg} [{ae}] -> [{re}] {ret}"),
            };
            if needs_paren {
                format!("({rendered})")
            } else {
                rendered
            }
        }
        Type::Record(fields) => {
            let fields = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}{}: {}",
                        field.name.0,
                        if field.optional { "?" } else { "" },
                        format_type_inner(&field.value, namer, false)
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{{fields}}}")
        }
        Type::RecordTailSpread { fields, tail } => {
            let mut items = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}{}: {}",
                        field.name.0,
                        if field.optional { "?" } else { "" },
                        format_type_inner(&field.value, namer, false)
                    )
                })
                .collect::<Vec<_>>();
            items.push(format!("..{}", format_type_inner(tail, namer, false)));
            format!("{{{}}}", items.join(", "))
        }
        Type::RecordHeadSpread { tail, fields } => {
            let mut items = vec![format!("..{}", format_type_inner(tail, namer, false))];
            items.extend(fields.iter().map(|field| {
                format!(
                    "{}{}: {}",
                    field.name.0,
                    if field.optional { "?" } else { "" },
                    format_type_inner(&field.value, namer, false)
                )
            }));
            format!("{{{}}}", items.join(", "))
        }
        Type::Variant(items) => {
            let items = items
                .iter()
                .map(|(name, payloads)| {
                    if payloads.is_empty() {
                        name.0.clone()
                    } else {
                        format!(
                            "{} {}",
                            name.0,
                            payloads
                                .iter()
                                .map(|payload| format_type_inner(payload, namer, true))
                                .collect::<Vec<_>>()
                                .join(" ")
                        )
                    }
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!(":[{items}]")
        }
        Type::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| format_type_inner(item, namer, false))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        Type::Row(items, tail) => {
            let items = items
                .iter()
                .map(|item| format_type_inner(item, namer, false))
                .collect::<Vec<_>>();
            if matches!(tail.as_ref(), Type::Bot) {
                format!("[{};]", items.join(", "))
            } else {
                let tail = format_type_inner(tail, namer, false);
                if items.is_empty() {
                    format!("[; {tail}]")
                } else {
                    format!("[{}; {tail}]", items.join(", "))
                }
            }
        }
        Type::Union(items) => {
            let joined = items
                .iter()
                .map(|item| format_type_inner(item, namer, true))
                .collect::<Vec<_>>()
                .join(" | ");
            if needs_paren {
                format!("({joined})")
            } else {
                joined
            }
        }
        Type::Inter(items) => {
            let joined = items
                .iter()
                .map(|item| format_type_inner(item, namer, true))
                .collect::<Vec<_>>()
                .join(" & ");
            if needs_paren {
                format!("({joined})")
            } else {
                joined
            }
        }
        Type::Rec(tv, body) => {
            let name = namer.name(tv.0);
            let body = format_type_inner(body, namer, false);
            format!("rec {{{name} = {body}}}. {name}")
        }
        Type::Bot => "⊥".to_string(),
        Type::Top => "⊤".to_string(),
    }
}

fn format_row_inline(ty: &Type, namer: &mut VarNamer) -> Option<String> {
    match ty {
        Type::Bot | Type::Top => None,
        Type::Union(items) => {
            let mut parts = items
                .iter()
                .filter_map(|item| format_row_inline(item, namer))
                .collect::<Vec<_>>();
            parts.sort();
            parts.dedup();
            if parts.is_empty() {
                None
            } else {
                Some(parts.join(", "))
            }
        }
        Type::Row(items, tail) => {
            let items = items
                .iter()
                .map(|item| format_type_inner(item, namer, false))
                .collect::<Vec<_>>();
            match tail.as_ref() {
                Type::Bot | Type::Top => {
                    if items.is_empty() {
                        None
                    } else {
                        Some(items.join(", "))
                    }
                }
                _ => {
                    let tail = format_row_inline(tail, namer)
                        .unwrap_or_else(|| format_type_inner(tail, namer, false));
                    if items.is_empty() {
                        Some(tail)
                    } else {
                        Some(format!("{}; {tail}", items.join(", ")))
                    }
                }
            }
        }
        _ => Some(format_type_inner(ty, namer, false)),
    }
}

fn format_ret_row_inline(ty: &Type, namer: &mut VarNamer) -> Option<String> {
    match ty {
        Type::Top => Some("⊤".to_string()),
        Type::Row(items, tail) if matches!(tail.as_ref(), Type::Top) => {
            let items = items
                .iter()
                .map(|item| format_type_inner(item, namer, false))
                .collect::<Vec<_>>();
            if items.is_empty() {
                Some("⊤".to_string())
            } else {
                Some(format!("{}; ⊤", items.join(", ")))
            }
        }
        _ => format_row_inline(ty, namer),
    }
}

fn format_compact_bounds(bounds: &CompactBounds, namer: &mut VarNamer) -> String {
    if let Some(rendered) = format_compact_bounds_with_center(bounds, namer) {
        return rendered;
    }
    let lower_empty = is_empty_compact(&bounds.lower);
    let upper_empty = is_empty_compact(&bounds.upper);
    match (lower_empty, upper_empty) {
        (true, true) => bounds
            .self_var
            .map(|tv| namer.name(tv.0))
            .unwrap_or_else(|| "_".to_string()),
        (false, true) => format_compact_type(&bounds.lower, namer, false),
        (true, false) => format!("_ <: {}", format_compact_type(&bounds.upper, namer, false)),
        (false, false) => {
            if let (Some(lower_vars), Some(upper_vars)) = (
                compact_var_set(&bounds.lower),
                compact_var_set(&bounds.upper),
            ) {
                if lower_vars.is_subset(&upper_vars) {
                    return format_compact_type(&bounds.lower, namer, false);
                }
            }
            let lower = format_compact_type(&bounds.lower, namer, false);
            let upper = format_compact_type(&bounds.upper, namer, false);
            if lower == upper {
                lower
            } else {
                format!("{lower} <: {upper}")
            }
        }
    }
}

fn format_compact_bounds_with_center(
    bounds: &CompactBounds,
    namer: &mut VarNamer,
) -> Option<String> {
    let shared = shared_center_vars(bounds);
    if shared.is_empty() {
        return None;
    }
    let mut lower = bounds.lower.clone();
    let mut upper = bounds.upper.clone();
    for tv in &shared {
        lower.vars.remove(tv);
        upper.vars.remove(tv);
    }

    let lower_empty = is_empty_compact(&lower);
    let upper_empty = is_empty_compact(&upper);
    let center = format_shared_center_vars(&shared, namer);

    if !lower_empty && !upper_empty && lower == upper && has_non_var_shape(&lower) {
        return Some(format_compact_type(&lower, namer, false));
    }

    match (lower_empty, upper_empty) {
        (true, true) => Some(center),
        (false, true) => Some(format!(
            "{} | {center}",
            format_compact_type(&lower, namer, false)
        )),
        (true, false) => Some(format!(
            "{center} & {}",
            format_compact_type_with_join(&upper, namer, false, " & ")
        )),
        (false, false) => Some(format!(
            "{} | {center} & {}",
            format_compact_type(&lower, namer, false),
            format_compact_type_with_join(&upper, namer, false, " & ")
        )),
    }
}

fn shared_center_vars(bounds: &CompactBounds) -> Vec<TypeVar> {
    let mut shared = bounds
        .lower
        .vars
        .intersection(&bounds.upper.vars)
        .copied()
        .collect::<Vec<_>>();
    shared.sort_by_key(|tv| tv.0);
    shared
}

fn format_shared_center_vars(shared: &[TypeVar], namer: &mut VarNamer) -> String {
    shared
        .iter()
        .map(|tv| namer.name(tv.0))
        .collect::<Vec<_>>()
        .join(" | ")
}

fn format_compact_type(ty: &CompactType, namer: &mut VarNamer, needs_paren: bool) -> String {
    format_compact_type_with_join(ty, namer, needs_paren, " | ")
}

fn format_compact_type_with_join(
    ty: &CompactType,
    namer: &mut VarNamer,
    needs_paren: bool,
    join: &str,
) -> String {
    let mut parts = Vec::new();

    let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    parts.extend(vars.into_iter().map(|tv| namer.name(tv.0)));

    let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
    prims.sort_by(|a, b| path_string(a).cmp(&path_string(b)));
    parts.extend(prims.into_iter().map(|path| path_string(&path)));

    let mut cons = ty.cons.clone();
    cons.sort_by(|a, b| path_string(&a.path).cmp(&path_string(&b.path)));
    parts.extend(cons.into_iter().map(|con| format_compact_con(&con, namer)));

    parts.extend(ty.funs.iter().map(|fun| format_compact_fun(fun, namer)));
    parts.extend(
        ty.records
            .iter()
            .map(|record| format_compact_record(record, namer)),
    );
    parts.extend(
        ty.record_spreads
            .iter()
            .map(|spread| format_compact_record_spread(spread, namer)),
    );
    parts.extend(
        ty.variants
            .iter()
            .map(|variant| format_compact_variant(variant, namer)),
    );
    parts.extend(ty.tuples.iter().map(|tuple| {
        let items = tuple
            .iter()
            .map(|item| format_compact_type(item, namer, false))
            .collect::<Vec<_>>();
        format!("({})", items.join(", "))
    }));
    parts.extend(ty.rows.iter().map(|row| format_compact_row(row, namer)));

    if parts.is_empty() {
        return "_".to_string();
    }
    if parts.len() == 1 {
        return parts.remove(0);
    }
    let joined = parts.join(join);
    if needs_paren {
        format!("({joined})")
    } else {
        joined
    }
}

fn format_compact_con(con: &CompactCon, namer: &mut VarNamer) -> String {
    let name = path_string(&con.path);
    if con.args.is_empty() {
        return name;
    }
    let args = con
        .args
        .iter()
        .map(|arg| format_compact_bounds(arg, namer))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{name}<{args}>")
}

fn format_compact_fun(fun: &CompactFun, namer: &mut VarNamer) -> String {
    let arg = format_compact_type(&fun.arg, namer, true);
    let ret = format_compact_type(&fun.ret, namer, false);
    let arg_eff = format_compact_row_inline(&fun.arg_eff, namer);
    let ret_eff = format_compact_row_inline(&fun.ret_eff, namer);
    match (arg_eff, ret_eff) {
        (None, None) => format!("{arg} -> {ret}"),
        (Some(ae), None) => format!("{arg} [{ae}] -> {ret}"),
        (None, Some(re)) => format!("{arg} -> [{re}] {ret}"),
        (Some(ae), Some(re)) => format!("{arg} [{ae}] -> [{re}] {ret}"),
    }
}

fn format_compact_record(record: &CompactRecord, namer: &mut VarNamer) -> String {
    let fields = record
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}{}: {}",
                field.name.0,
                if field.optional { "?" } else { "" },
                format_compact_type(&field.value, namer, false)
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{{{fields}}}")
}

fn format_compact_record_spread(spread: &CompactRecordSpread, namer: &mut VarNamer) -> String {
    let fields = spread
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}{}: {}",
                field.name.0,
                if field.optional { "?" } else { "" },
                format_compact_type(&field.value, namer, false)
            )
        })
        .collect::<Vec<_>>();
    let tail = format_compact_type(&spread.tail, namer, false);
    if spread.tail_wins {
        let mut items = fields;
        items.push(format!("..{tail}"));
        format!("{{{}}}", items.join(", "))
    } else {
        let mut items = vec![format!("..{tail}")];
        items.extend(fields);
        format!("{{{}}}", items.join(", "))
    }
}

fn format_compact_variant(variant: &CompactVariant, namer: &mut VarNamer) -> String {
    let items = variant
        .items
        .iter()
        .map(|(name, payloads)| {
            if payloads.is_empty() {
                name.0.clone()
            } else {
                format!(
                    "{} {}",
                    name.0,
                    payloads
                        .iter()
                        .map(|payload| format_compact_type(payload, namer, true))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(":[{items}]")
}

fn format_compact_row(row: &CompactRow, namer: &mut VarNamer) -> String {
    let items = row
        .items
        .iter()
        .map(|item| format_compact_type(item, namer, false))
        .collect::<Vec<_>>();
    if is_empty_compact(&row.tail) {
        format!("[{};]", items.join(", "))
    } else {
        let tail = format_compact_type(&row.tail, namer, false);
        if items.is_empty() {
            format!("[; {tail}]")
        } else {
            format!("[{}; {tail}]", items.join(", "))
        }
    }
}

fn format_compact_row_inline(ty: &CompactType, namer: &mut VarNamer) -> Option<String> {
    match ty.rows.as_slice() {
        [] if is_empty_compact(ty) => None,
        [row]
            if ty.vars.is_empty()
                && ty.prims.is_empty()
                && ty.cons.is_empty()
                && ty.funs.is_empty()
                && ty.records.is_empty()
                && ty.variants.is_empty()
                && ty.tuples.is_empty() =>
        {
            let items = row
                .items
                .iter()
                .map(|item| format_compact_type(item, namer, false))
                .collect::<Vec<_>>();
            if is_empty_compact(&row.tail) {
                if items.is_empty() {
                    None
                } else {
                    Some(items.join(", "))
                }
            } else {
                let tail = format_compact_type(&row.tail, namer, false);
                if items.is_empty() {
                    Some(tail)
                } else {
                    Some(format!("{}; {tail}", items.join(", ")))
                }
            }
        }
        _ => Some(format_compact_type(ty, namer, false)),
    }
}

fn normalize_render_bounds(mut bounds: CompactBounds) -> CompactBounds {
    render_absorb_upper_vars_from_row_lower(&mut bounds);
    bounds
}

fn render_absorb_upper_vars_from_row_lower(bounds: &mut CompactBounds) {
    let Some(upper) = compact_var_set(&bounds.upper) else {
        return;
    };
    if upper.is_empty()
        || bounds.lower.rows.is_empty()
        || !bounds.lower.prims.is_empty()
        || !bounds.lower.cons.is_empty()
        || !bounds.lower.funs.is_empty()
        || !bounds.lower.records.is_empty()
        || !bounds.lower.record_spreads.is_empty()
        || !bounds.lower.variants.is_empty()
        || !bounds.lower.tuples.is_empty()
        || !upper.is_subset(&bounds.lower.vars)
    {
        return;
    }
    for tv in upper {
        if bounds.self_var == Some(tv) {
            continue;
        }
        bounds.lower.vars.remove(&tv);
        bounds.upper.vars.remove(&tv);
    }
}

fn compact_var_set(ty: &CompactType) -> Option<HashSet<TypeVar>> {
    (ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty())
    .then(|| ty.vars.clone())
}

fn should_hash_cons_type(ty: &CompactType) -> bool {
    !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
}

fn compact_type_key(ty: &CompactType) -> String {
    let mut vars = ty.vars.iter().map(|tv| tv.0).collect::<Vec<_>>();
    vars.sort_unstable();
    let mut prims = ty.prims.iter().map(path_string).collect::<Vec<_>>();
    prims.sort();
    let mut cons = ty.cons.iter().map(compact_con_key).collect::<Vec<_>>();
    cons.sort();
    let mut funs = ty.funs.iter().map(compact_fun_key).collect::<Vec<_>>();
    funs.sort();
    let mut records = ty
        .records
        .iter()
        .map(compact_record_key)
        .collect::<Vec<_>>();
    records.sort();
    let mut record_spreads = ty
        .record_spreads
        .iter()
        .map(compact_record_spread_key)
        .collect::<Vec<_>>();
    record_spreads.sort();
    let mut variants = ty
        .variants
        .iter()
        .map(compact_variant_key)
        .collect::<Vec<_>>();
    variants.sort();
    let mut tuples = ty
        .tuples
        .iter()
        .map(|tuple| compact_tuple_key(tuple))
        .collect::<Vec<_>>();
    tuples.sort();
    let mut rows = ty.rows.iter().map(compact_row_key).collect::<Vec<_>>();
    rows.sort();
    format!(
        "T[v={vars:?};p={prims:?};c={cons:?};f={funs:?};r={records:?};rs={record_spreads:?};vnt={variants:?};t={tuples:?};rw={rows:?}]"
    )
}

fn compact_bounds_key(bounds: &CompactBounds) -> String {
    format!(
        "B[{}<:{}]",
        compact_type_key(&bounds.lower),
        compact_type_key(&bounds.upper)
    )
}

fn compact_con_key(con: &CompactCon) -> String {
    let args = con.args.iter().map(compact_bounds_key).collect::<Vec<_>>();
    format!("{}<{args:?}>", path_string(&con.path))
}

fn compact_fun_key(fun: &CompactFun) -> String {
    format!(
        "({}->{}/{})",
        compact_type_key(&fun.arg),
        compact_type_key(&fun.arg_eff),
        compact_type_key(&fun.ret_eff),
    ) + &format!("->{}", compact_type_key(&fun.ret))
}

fn compact_record_key(record: &CompactRecord) -> String {
    let mut fields = record
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}{}:{}",
                field.name.0,
                if field.optional { "?" } else { "" },
                compact_type_key(&field.value)
            )
        })
        .collect::<Vec<_>>();
    fields.sort();
    format!("{{{}}}", fields.join(","))
}

fn compact_record_spread_key(spread: &CompactRecordSpread) -> String {
    let mut fields = spread
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}{}:{}",
                field.name.0,
                if field.optional { "?" } else { "" },
                compact_type_key(&field.value)
            )
        })
        .collect::<Vec<_>>();
    fields.sort();
    let tail = compact_type_key(&spread.tail);
    if spread.tail_wins {
        fields.push(format!("..{tail}"));
    } else {
        fields.insert(0, format!("..{tail}"));
    }
    format!("{{{}}}", fields.join(","))
}

fn compact_variant_key(variant: &CompactVariant) -> String {
    let mut items = variant
        .items
        .iter()
        .map(|(name, payloads)| {
            let payloads = payloads.iter().map(compact_type_key).collect::<Vec<_>>();
            format!("{}({})", name.0, payloads.join(","))
        })
        .collect::<Vec<_>>();
    items.sort();
    format!("[{}]", items.join("|"))
}

fn compact_tuple_key(tuple: &[CompactType]) -> String {
    let items = tuple.iter().map(compact_type_key).collect::<Vec<_>>();
    format!("({})", items.join(","))
}

fn compact_row_key(row: &CompactRow) -> String {
    let mut items = row.items.iter().map(compact_type_key).collect::<Vec<_>>();
    items.sort();
    format!("[{};{}]", items.join(","), compact_type_key(&row.tail))
}

fn root_non_fun_parts_empty(ty: &CompactType) -> bool {
    ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn common_compact_type(lhs: &CompactType, rhs: &CompactType) -> Option<CompactType> {
    Some(CompactType {
        vars: lhs.vars.intersection(&rhs.vars).copied().collect(),
        prims: lhs.prims.intersection(&rhs.prims).cloned().collect(),
        cons: lhs
            .cons
            .iter()
            .filter(|item| rhs.cons.contains(item))
            .cloned()
            .collect(),
        funs: lhs
            .funs
            .iter()
            .filter(|item| rhs.funs.contains(item))
            .cloned()
            .collect(),
        records: lhs
            .records
            .iter()
            .filter(|item| rhs.records.contains(item))
            .cloned()
            .collect(),
        record_spreads: lhs
            .record_spreads
            .iter()
            .filter(|item| rhs.record_spreads.contains(item))
            .cloned()
            .collect(),
        variants: lhs
            .variants
            .iter()
            .filter(|item| rhs.variants.contains(item))
            .cloned()
            .collect(),
        tuples: lhs
            .tuples
            .iter()
            .filter(|item| rhs.tuples.contains(item))
            .cloned()
            .collect(),
        rows: lhs
            .rows
            .iter()
            .filter(|item| rhs.rows.contains(item))
            .cloned()
            .collect(),
    })
}

fn is_empty_compact(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn has_non_var_shape(ty: &CompactType) -> bool {
    !ty.prims.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
}

fn is_explicit_empty_row_compact(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && matches!(
            ty.rows.as_slice(),
            [CompactRow { items, tail }] if items.is_empty() && is_empty_compact(tail)
        )
}

fn is_var_only_compact(ty: &CompactType) -> bool {
    ty.vars.len() == 1
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn is_empty_row(ty: &Type) -> bool {
    matches!(ty, Type::Row(items, tail) if items.is_empty() && matches!(tail.as_ref(), Type::Bot))
}

fn path_string(path: &Path) -> String {
    path.segments
        .iter()
        .map(|name| display_name_segment(name.0.as_str()))
        .collect::<Vec<_>>()
        .join("::")
}

fn display_name_segment(name: &str) -> &str {
    name
}
