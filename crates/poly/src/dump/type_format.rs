//! `poly::types` を surface 構文に近い短い表記へ落とす formatter。
//!
//! 型 dump は parser が読む形へなるべく寄せる。ただし `Pos` / `Neg` / `Neu` には
//! polarity や sandwich bound のような内部情報もあるため、完全に surface syntax へ
//! 潰しきれない node は短い internal marker を残す。

use rustc_hash::FxHashMap;

use crate::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicate, Scheme, SubtractId, TypeArena,
    TypeVar,
};

/// scheme を `list 'a` や `'a [io; 'e] -> ['e] 'a` のような短い構文風表記で返す。
pub fn format_scheme(arena: &TypeArena, scheme: &Scheme) -> String {
    let mut namer = TypeVarNamer::new();
    namer.seed(&scheme.quantifiers);
    TypeFormatter::new(arena, namer).format_scheme(scheme)
}

/// 正側型を短い構文風表記で返す。
pub fn format_pos(arena: &TypeArena, id: PosId) -> String {
    TypeFormatter::new(arena, TypeVarNamer::new()).pos(id, Context::Free)
}

/// 負側型を短い構文風表記で返す。
pub fn format_neg(arena: &TypeArena, id: NegId) -> String {
    TypeFormatter::new(arena, TypeVarNamer::new()).neg(id, Context::Free)
}

/// 中立型を短い構文風表記で返す。
pub fn format_neu(arena: &TypeArena, id: NeuId) -> String {
    TypeFormatter::new(arena, TypeVarNamer::new()).neu(id, Context::Free)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Arrow,
    Union,
    Intersection,
    Apply,
    Atom,
}

#[derive(Debug, Clone, Copy)]
enum Context {
    Free,
    FunctionArg,
    MlArg,
}

impl Context {
    fn needs_paren(self, rendered: Rendered) -> bool {
        match self {
            Context::Free => false,
            Context::FunctionArg => rendered.prec <= Prec::Intersection,
            Context::MlArg => rendered.prec < Prec::Atom,
        }
    }
}

#[derive(Debug, Clone)]
struct Rendered {
    text: String,
    prec: Prec,
    // 表示全体を外側の括弧で守らないと top-level に空白が出るか。
    // constructor の子にこれがある場合だけ、ML 適用ではなく C call 表記に切り替える。
    has_bare_space: bool,
}

impl Rendered {
    fn atom(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            prec: Prec::Atom,
            has_bare_space: false,
        }
    }

    fn apply_ml(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            prec: Prec::Apply,
            has_bare_space: true,
        }
    }

    fn apply_c(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            prec: Prec::Atom,
            has_bare_space: false,
        }
    }

    fn union(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            prec: Prec::Union,
            has_bare_space: true,
        }
    }

    fn intersection(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            prec: Prec::Intersection,
            has_bare_space: true,
        }
    }

    fn arrow(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            prec: Prec::Arrow,
            has_bare_space: true,
        }
    }

    fn in_context(self, context: Context) -> String {
        if context.needs_paren(self.clone()) {
            format!("({})", self.text)
        } else {
            self.text
        }
    }
}

struct TypeFormatter<'a> {
    arena: &'a TypeArena,
    namer: TypeVarNamer,
}

impl<'a> TypeFormatter<'a> {
    fn new(arena: &'a TypeArena, namer: TypeVarNamer) -> Self {
        Self { arena, namer }
    }

    fn format_scheme(mut self, scheme: &Scheme) -> String {
        let mut body = self.pos(scheme.predicate, Context::Free);
        if !scheme.role_predicates.is_empty() {
            let predicates = scheme
                .role_predicates
                .iter()
                .map(|predicate| self.role_predicate(predicate))
                .collect::<Vec<_>>()
                .join(", ");
            body = format!("{predicates} => {body}");
        }
        if !scheme.subtracts.is_empty() {
            let facts = scheme
                .subtracts
                .iter()
                .map(|(var, subtract)| self.subtract_fact(*var, *subtract))
                .collect::<Vec<_>>()
                .join(", ");
            body.push_str(" where ");
            body.push_str(&facts);
        }
        body
    }

    fn role_predicate(&mut self, predicate: &RolePredicate) -> String {
        let mut args = predicate
            .inputs
            .iter()
            .map(|arg| self.neu(*arg, Context::Free))
            .collect::<Vec<_>>();
        args.extend(predicate.associated.iter().map(|associated| {
            format!(
                "{} = {}",
                associated.name,
                self.neu(associated.value, Context::Free)
            )
        }));
        format!("{}({})", path_name(&predicate.role), args.join(", "))
    }

    fn pos(&mut self, id: PosId, context: Context) -> String {
        self.render_pos(id).in_context(context)
    }

    fn neg(&mut self, id: NegId, context: Context) -> String {
        self.render_neg(id).in_context(context)
    }

    fn neu(&mut self, id: NeuId, context: Context) -> String {
        self.render_neu(id).in_context(context)
    }

    fn render_pos(&mut self, id: PosId) -> Rendered {
        match self.arena.pos(id) {
            Pos::Bot => Rendered::atom("never"),
            Pos::Var(var) => Rendered::atom(self.namer.name(*var)),
            Pos::Con(path, args) => self.render_con(path, args),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.render_pos_fun(*arg, *arg_eff, *ret_eff, *ret),
            Pos::Record(fields) => {
                Rendered::atom(self.record(fields, |this, id| this.pos(id, Context::Free)))
            }
            Pos::RecordTailSpread { fields, tail } => {
                Rendered::atom(self.record_spread_tail(fields, *tail))
            }
            Pos::RecordHeadSpread { tail, fields } => {
                Rendered::atom(self.record_spread_head(*tail, fields))
            }
            Pos::PolyVariant(items) => {
                Rendered::atom(self.variant(items, |this, id| this.pos(id, Context::MlArg)))
            }
            Pos::Tuple(items) => {
                Rendered::atom(self.tuple(items, |this, id| this.pos(id, Context::Free)))
            }
            Pos::Row(items) => Rendered::atom(format!("'{}", self.pos_row_items(items))),
            Pos::NonSubtract(pos, subtract) => Rendered::atom(format!(
                "non-subtract({}, {})",
                self.pos(*pos, Context::Free),
                self.subtract_id(*subtract)
            )),
            Pos::Union(left, right) => {
                let parts = self.flatten_pos_union(*left, *right);
                Rendered::union(parts.join(" | "))
            }
        }
    }

    fn render_neg(&mut self, id: NegId) -> Rendered {
        match self.arena.neg(id) {
            Neg::Top => Rendered::atom("any"),
            Neg::Bot => Rendered::atom("never"),
            Neg::Var(var) => Rendered::atom(self.namer.name(*var)),
            Neg::Con(path, args) => self.render_con(path, args),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.render_neg_fun(*arg, *arg_eff, *ret_eff, *ret),
            Neg::Record(fields) => {
                Rendered::atom(self.record(fields, |this, id| this.neg(id, Context::Free)))
            }
            Neg::PolyVariant(items) => {
                Rendered::atom(self.variant(items, |this, id| this.neg(id, Context::MlArg)))
            }
            Neg::Tuple(items) => {
                Rendered::atom(self.tuple(items, |this, id| this.neg(id, Context::Free)))
            }
            Neg::Row(items, tail) => Rendered::atom(format!("'{}", self.neg_row(items, *tail))),
            Neg::Intersection(left, right) => {
                let parts = self.flatten_neg_intersection(*left, *right);
                Rendered::intersection(parts.join(" & "))
            }
        }
    }

    fn render_neu(&mut self, id: NeuId) -> Rendered {
        match self.arena.neu(id) {
            Neu::Bounds(lower, var, upper) if self.is_plain_bounds(*lower, *var, *upper) => {
                Rendered::atom(self.namer.name(*var))
            }
            Neu::Bounds(lower, var, upper) => Rendered::atom(format!(
                "bounds({}, {}, {})",
                self.pos(*lower, Context::Free),
                self.namer.name(*var),
                self.neg(*upper, Context::Free)
            )),
            Neu::Con(path, args) => self.render_con(path, args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.render_neu_fun(*arg, *arg_eff, *ret_eff, *ret),
            Neu::Record(fields) => {
                Rendered::atom(self.record(fields, |this, id| this.neu(id, Context::Free)))
            }
            Neu::PolyVariant(items) => {
                Rendered::atom(self.variant(items, |this, id| this.neu(id, Context::MlArg)))
            }
            Neu::Tuple(items) => {
                Rendered::atom(self.tuple(items, |this, id| this.neu(id, Context::Free)))
            }
        }
    }

    fn render_con(&mut self, path: &[String], args: &[NeuId]) -> Rendered {
        let name = path_name(path);
        if args.is_empty() {
            return Rendered::atom(name);
        }

        let args = args
            .iter()
            .map(|arg| self.render_neu(*arg))
            .collect::<Vec<_>>();
        if args.iter().any(|arg| arg.has_bare_space) {
            let args = args
                .into_iter()
                .map(|arg| arg.text)
                .collect::<Vec<_>>()
                .join(", ");
            Rendered::apply_c(format!("{name}({args})"))
        } else {
            let mut parts = Vec::with_capacity(args.len() + 1);
            parts.push(name);
            parts.extend(args.into_iter().map(|arg| arg.in_context(Context::MlArg)));
            Rendered::apply_ml(parts.join(" "))
        }
    }

    fn render_pos_fun(
        &mut self,
        arg: NegId,
        arg_eff: NegId,
        ret_eff: PosId,
        ret: PosId,
    ) -> Rendered {
        let arg = self.neg(arg, Context::FunctionArg);
        let arg_eff = self.neg_row_inline(arg_eff);
        let ret_eff = self.pos_row_inline(ret_eff);
        let ret = self.pos(ret, Context::Free);
        Rendered::arrow(fun_text(arg, arg_eff, ret_eff, ret))
    }

    fn render_neg_fun(
        &mut self,
        arg: PosId,
        arg_eff: PosId,
        ret_eff: NegId,
        ret: NegId,
    ) -> Rendered {
        let arg = self.pos(arg, Context::FunctionArg);
        let arg_eff = self.pos_row_inline(arg_eff);
        let ret_eff = self.neg_row_inline(ret_eff);
        let ret = self.neg(ret, Context::Free);
        Rendered::arrow(fun_text(arg, arg_eff, ret_eff, ret))
    }

    fn render_neu_fun(
        &mut self,
        arg: NeuId,
        arg_eff: NeuId,
        ret_eff: NeuId,
        ret: NeuId,
    ) -> Rendered {
        let arg = self.neu(arg, Context::FunctionArg);
        let arg_eff = Some(self.neu(arg_eff, Context::Free));
        let ret_eff = Some(self.neu(ret_eff, Context::Free));
        let ret = self.neu(ret, Context::Free);
        Rendered::arrow(fun_text(arg, arg_eff, ret_eff, ret))
    }

    fn record<Id: Copy>(
        &mut self,
        fields: &[RecordField<Id>],
        mut format: impl FnMut(&mut Self, Id) -> String,
    ) -> String {
        let fields = fields
            .iter()
            .map(|field| self.record_field(field, &mut format))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{{{fields}}}")
    }

    fn record_field<Id: Copy>(
        &mut self,
        field: &RecordField<Id>,
        format: &mut impl FnMut(&mut Self, Id) -> String,
    ) -> String {
        format!(
            "{}{}: {}",
            surface_name(&field.name),
            if field.optional { "?" } else { "" },
            format(self, field.value)
        )
    }

    fn record_spread_tail(&mut self, fields: &[RecordField<PosId>], tail: PosId) -> String {
        let mut items = fields
            .iter()
            .map(|field| self.record_field(field, &mut |this, id| this.pos(id, Context::Free)))
            .collect::<Vec<_>>();
        items.push(format!("..{}", self.pos(tail, Context::Free)));
        format!("{{{}}}", items.join(", "))
    }

    fn record_spread_head(&mut self, tail: PosId, fields: &[RecordField<PosId>]) -> String {
        let mut items = vec![format!("..{}", self.pos(tail, Context::Free))];
        items.extend(
            fields
                .iter()
                .map(|field| self.record_field(field, &mut |this, id| this.pos(id, Context::Free))),
        );
        format!("{{{}}}", items.join(", "))
    }

    fn variant<Id: Copy>(
        &mut self,
        items: &[(String, Vec<Id>)],
        mut format: impl FnMut(&mut Self, Id) -> String,
    ) -> String {
        let items = items
            .iter()
            .map(|(name, payloads)| {
                if payloads.is_empty() {
                    surface_name(name)
                } else {
                    let payloads = payloads
                        .iter()
                        .map(|payload| format(self, *payload))
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("{} {payloads}", surface_name(name))
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!(":{{{items}}}")
    }

    fn tuple<Id: Copy>(
        &mut self,
        items: &[Id],
        mut format: impl FnMut(&mut Self, Id) -> String,
    ) -> String {
        match items {
            [] => "()".to_string(),
            [only] => format!("({},)", format(self, *only)),
            _ => {
                let items = items
                    .iter()
                    .map(|item| format(self, *item))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({items})")
            }
        }
    }

    fn neg_row_inline(&mut self, id: NegId) -> Option<String> {
        match self.arena.neg(id) {
            Neg::Top => None,
            Neg::Bot => None,
            Neg::Row(items, tail) => self.neg_row_inline_items(items, *tail),
            Neg::Intersection(left, right) => {
                let mut parts = Vec::new();
                if let Some(left) = self.neg_row_inline(*left) {
                    parts.push(left);
                }
                if let Some(right) = self.neg_row_inline(*right) {
                    parts.push(right);
                }
                (!parts.is_empty()).then(|| parts.join(" & "))
            }
            _ => Some(self.neg(id, Context::Free)),
        }
    }

    fn neg_row_inline_items(&mut self, items: &[NegId], tail: NegId) -> Option<String> {
        let items = items
            .iter()
            .map(|item| self.neg(*item, Context::Free))
            .collect::<Vec<_>>();
        match self.arena.neg(tail) {
            Neg::Top if items.is_empty() => None,
            Neg::Top => Some(items.join(", ")),
            _ => {
                let tail = self
                    .neg_row_inline(tail)
                    .unwrap_or_else(|| self.neg(tail, Context::Free));
                if items.is_empty() {
                    Some(tail)
                } else {
                    Some(format!("{}; {tail}", items.join(", ")))
                }
            }
        }
    }

    fn neg_row(&mut self, items: &[NegId], tail: NegId) -> String {
        self.neg_row_inline_items(items, tail)
            .map(|items| format!("[{items}]"))
            .unwrap_or_else(|| "[]".to_string())
    }

    fn pos_row_inline(&mut self, id: PosId) -> Option<String> {
        let parts = self.collect_pos_row_parts(id);
        if parts.is_empty() {
            return None;
        }
        let mut items = Vec::new();
        let mut tails = Vec::new();
        for part in parts {
            match part {
                PosRowPart::Item(item) => items.push(item),
                PosRowPart::Tail(tail) => tails.push(tail),
            }
        }
        items.extend(tails);
        Some(items.join(", "))
    }

    fn pos_row_items(&mut self, items: &[PosId]) -> String {
        let items = items
            .iter()
            .flat_map(|item| self.collect_pos_row_parts(*item))
            .map(|part| match part {
                PosRowPart::Item(item) | PosRowPart::Tail(item) => item,
            })
            .collect::<Vec<_>>();
        if items.is_empty() {
            "[]".to_string()
        } else {
            format!("[{}]", items.join(", "))
        }
    }

    fn collect_pos_row_parts(&mut self, id: PosId) -> Vec<PosRowPart> {
        match self.arena.pos(id) {
            Pos::Bot => Vec::new(),
            Pos::Row(items) => {
                let mut parts = Vec::new();
                for item in items.clone() {
                    parts.extend(self.collect_pos_row_parts(item));
                }
                parts
            }
            Pos::Union(left, right) => {
                let mut parts = self.collect_pos_row_parts(*left);
                parts.extend(self.collect_pos_row_parts(*right));
                parts
            }
            Pos::Var(var) => vec![PosRowPart::Tail(self.namer.name(*var))],
            _ => vec![PosRowPart::Item(self.pos(id, Context::Free))],
        }
    }

    fn flatten_pos_union(&mut self, left: PosId, right: PosId) -> Vec<String> {
        let mut parts = Vec::new();
        self.push_pos_union(left, &mut parts);
        self.push_pos_union(right, &mut parts);
        parts
    }

    fn push_pos_union(&mut self, id: PosId, out: &mut Vec<String>) {
        match self.arena.pos(id) {
            Pos::Union(left, right) => {
                self.push_pos_union(*left, out);
                self.push_pos_union(*right, out);
            }
            _ => out.push(self.pos(id, Context::FunctionArg)),
        }
    }

    fn flatten_neg_intersection(&mut self, left: NegId, right: NegId) -> Vec<String> {
        let mut parts = Vec::new();
        self.push_neg_intersection(left, &mut parts);
        self.push_neg_intersection(right, &mut parts);
        parts
    }

    fn push_neg_intersection(&mut self, id: NegId, out: &mut Vec<String>) {
        match self.arena.neg(id) {
            Neg::Intersection(left, right) => {
                self.push_neg_intersection(*left, out);
                self.push_neg_intersection(*right, out);
            }
            _ => out.push(self.neg(id, Context::FunctionArg)),
        }
    }

    fn is_plain_bounds(&self, lower: PosId, var: TypeVar, upper: NegId) -> bool {
        matches!(self.arena.pos(lower), Pos::Bot) && matches!(self.arena.neg(upper), Neg::Top)
            || matches!(self.arena.pos(lower), Pos::Var(lower_var) if *lower_var == var)
                && matches!(self.arena.neg(upper), Neg::Var(upper_var) if *upper_var == var)
    }

    fn subtract_fact(&mut self, var: TypeVar, subtract: SubtractId) -> String {
        format!(
            "subtract({}, {})",
            self.namer.name(var),
            self.subtract_id(subtract)
        )
    }

    fn subtract_id(&self, subtract: SubtractId) -> String {
        format!("#{}", subtract.0)
    }
}

enum PosRowPart {
    Item(String),
    Tail(String),
}

#[derive(Debug, Clone)]
struct TypeVarNamer {
    names: FxHashMap<TypeVar, String>,
    next: usize,
}

impl TypeVarNamer {
    fn new() -> Self {
        Self {
            names: FxHashMap::default(),
            next: 0,
        }
    }

    fn seed(&mut self, vars: &[TypeVar]) {
        for var in vars {
            self.name(*var);
        }
    }

    fn name(&mut self, var: TypeVar) -> String {
        if let Some(name) = self.names.get(&var) {
            return name.clone();
        }
        let name = format!("'{}", letter_name(self.next));
        self.next += 1;
        self.names.insert(var, name.clone());
        name
    }
}

fn fun_text(arg: String, arg_eff: Option<String>, ret_eff: Option<String>, ret: String) -> String {
    match (arg_eff, ret_eff) {
        (None, None) => format!("{arg} -> {ret}"),
        (Some(arg_eff), None) => format!("{arg} [{arg_eff}] -> {ret}"),
        (None, Some(ret_eff)) => format!("{arg} -> [{ret_eff}] {ret}"),
        (Some(arg_eff), Some(ret_eff)) => format!("{arg} [{arg_eff}] -> [{ret_eff}] {ret}"),
    }
}

fn path_name(path: &[String]) -> String {
    path.iter()
        .map(|segment| surface_name(segment))
        .collect::<Vec<_>>()
        .join("::")
}

fn surface_name(name: &str) -> String {
    if is_plain_name(name) {
        name.to_string()
    } else {
        format!("{name:?}")
    }
}

fn is_plain_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn letter_name(mut index: usize) -> String {
    let mut chars = Vec::new();
    loop {
        chars.push((b'a' + (index % 26) as u8) as char);
        index /= 26;
        if index == 0 {
            break;
        }
        index -= 1;
    }
    chars.iter().rev().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_surface_like_function_with_rows_and_ml_application() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let b = TypeVar(1);

        let pos_a = arena.alloc_pos(Pos::Var(a));
        let neg_a = arena.alloc_neg(Neg::Var(a));
        let neu_a = arena.alloc_neu(Neu::Bounds(pos_a, a, neg_a));
        let ret = arena.alloc_pos(Pos::Con(vec!["list".into()], vec![neu_a]));
        let ret_eff = arena.alloc_pos(Pos::Var(b));
        let nondet = arena.alloc_neg(Neg::Con(vec!["nondet".into()], Vec::new()));
        let tail = arena.alloc_neg(Neg::Var(b));
        let arg_eff = arena.alloc_neg(Neg::Row(vec![nondet], tail));
        let arg = arena.alloc_neg(Neg::Var(a));
        let predicate = arena.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        let scheme = Scheme {
            quantifiers: vec![a, b],
            role_predicates: Vec::new(),
            predicate,
            subtracts: Vec::new(),
        };

        assert_eq!(
            format_scheme(&arena, &scheme),
            "'a [nondet; 'b] -> ['b] list 'a"
        );
    }

    #[test]
    fn formats_never_and_any_names() {
        let mut arena = TypeArena::new();
        let never = arena.alloc_pos(Pos::Bot);
        let any = arena.alloc_neg(Neg::Top);
        let neg_never = arena.alloc_neg(Neg::Bot);

        assert_eq!(format_pos(&arena, never), "never");
        assert_eq!(format_neg(&arena, any), "any");
        assert_eq!(format_neg(&arena, neg_never), "never");
    }

    #[test]
    fn omits_negative_bottom_function_argument_effect() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let b = TypeVar(1);
        let arg = arena.alloc_neg(Neg::Var(a));
        let arg_eff = arena.alloc_neg(Neg::Bot);
        let ret_eff = arena.alloc_pos(Pos::Var(b));
        let ret = arena.alloc_pos(Pos::Var(a));
        let predicate = arena.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        let scheme = Scheme {
            quantifiers: vec![a, b],
            role_predicates: Vec::new(),
            predicate,
            subtracts: Vec::new(),
        };

        assert_eq!(format_scheme(&arena, &scheme), "'a -> ['b] 'a");
    }

    #[test]
    fn omits_bottom_function_return_effect() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let arg = arena.alloc_neg(Neg::Var(a));
        let arg_eff = arena.alloc_neg(Neg::Bot);
        let ret_eff = arena.alloc_pos(Pos::Bot);
        let ret = arena.alloc_pos(Pos::Var(a));
        let predicate = arena.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        let scheme = Scheme {
            quantifiers: vec![a],
            role_predicates: Vec::new(),
            predicate,
            subtracts: Vec::new(),
        };

        assert_eq!(format_scheme(&arena, &scheme), "'a -> 'a");
    }

    #[test]
    fn formats_standalone_effect_row_with_apostrophe() {
        let mut arena = TypeArena::new();
        let e = TypeVar(0);
        let item = arena.alloc_neg(Neg::Con(vec!["nondet".into()], Vec::new()));
        let tail = arena.alloc_neg(Neg::Var(e));
        let row = arena.alloc_neg(Neg::Row(vec![item], tail));

        assert_eq!(format_neg(&arena, row), "'[nondet; 'a]");
    }

    #[test]
    fn formats_positive_effect_row_items_without_tail_separator() {
        let mut arena = TypeArena::new();
        let e = TypeVar(0);
        let nondet = arena.alloc_pos(Pos::Con(vec!["nondet".into()], Vec::new()));
        let tail = arena.alloc_pos(Pos::Var(e));
        let row = arena.alloc_pos(Pos::Row(vec![nondet, tail]));

        assert_eq!(format_pos(&arena, row), "'[nondet, 'a]");
    }

    #[test]
    fn uses_c_call_when_type_argument_has_bare_space() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let pos_a = arena.alloc_pos(Pos::Var(a));
        let neg_a = arena.alloc_neg(Neg::Var(a));
        let neu_a = arena.alloc_neu(Neu::Bounds(pos_a, a, neg_a));
        let list_a = arena.alloc_neu(Neu::Con(vec!["list".into()], vec![neu_a]));
        let outer = arena.alloc_pos(Pos::Con(vec!["box".into()], vec![list_a]));

        assert_eq!(format_pos(&arena, outer), "box(list 'a)");
    }

    #[test]
    fn uses_c_call_for_nested_same_constructor_application() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let pos_a = arena.alloc_pos(Pos::Var(a));
        let neg_a = arena.alloc_neg(Neg::Var(a));
        let neu_a = arena.alloc_neu(Neu::Bounds(pos_a, a, neg_a));
        let inner = arena.alloc_neu(Neu::Con(vec!["list".into()], vec![neu_a]));
        let outer = arena.alloc_pos(Pos::Con(vec!["list".into()], vec![inner]));

        assert_eq!(format_pos(&arena, outer), "list(list 'a)");
    }

    #[test]
    fn formats_scheme_subtract_facts_when_present() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let predicate = arena.alloc_pos(Pos::Var(a));
        let scheme = Scheme {
            quantifiers: vec![a],
            role_predicates: Vec::new(),
            predicate,
            subtracts: vec![(a, SubtractId(2))],
        };

        assert_eq!(format_scheme(&arena, &scheme), "'a where subtract('a, #2)");
    }

    #[test]
    fn formats_role_predicates_before_scheme_body() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let b = TypeVar(1);
        let c = TypeVar(2);
        let neu_a = plain_neu(&mut arena, a);
        let neu_b = plain_neu(&mut arena, b);
        let neu_c = plain_neu(&mut arena, c);
        let predicate = arena.alloc_pos(Pos::Var(c));
        let scheme = Scheme {
            quantifiers: vec![a, b, c],
            role_predicates: vec![RolePredicate {
                role: vec!["Mul".into()],
                inputs: vec![neu_a, neu_b],
                associated: vec![crate::types::RoleAssociatedType {
                    name: "out".into(),
                    value: neu_c,
                }],
            }],
            predicate,
            subtracts: Vec::new(),
        };

        assert_eq!(
            format_scheme(&arena, &scheme),
            "Mul('a, 'b, out = 'c) => 'c"
        );
    }

    fn plain_neu(arena: &mut TypeArena, var: TypeVar) -> NeuId {
        let pos = arena.alloc_pos(Pos::Var(var));
        let neg = arena.alloc_neg(Neg::Var(var));
        arena.alloc_neu(Neu::Bounds(pos, var, neg))
    }
}
