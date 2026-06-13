//! `poly::types` を surface 構文に近い短い表記へ落とす formatter。
//!
//! 型 dump は parser が読む形へなるべく寄せる。ただし `Pos` / `Neg` / `Neu` には
//! polarity や sandwich bound のような内部情報もあるため、完全に surface syntax へ
//! 潰しきれない node は短い internal marker を残す。

use rustc_hash::FxHashMap;

use crate::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicate, RolePredicateArg, Scheme,
    StackWeight, SubtractId, Subtractability, TypeArena, TypeVar,
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
    fn needs_paren(self, rendered: &Rendered) -> bool {
        match self {
            Context::Free => false,
            Context::FunctionArg => rendered.prec <= Prec::Intersection,
            Context::MlArg => rendered.prec < Prec::Atom,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum NeuPolarity {
    Neutral,
    Positive,
    Negative,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
        self.into_context(context).text
    }

    fn into_context(self, context: Context) -> Rendered {
        if context.needs_paren(&self) {
            Rendered::atom(format!("({})", self.text))
        } else {
            self
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
        let mut predicates = Vec::new();
        predicates.extend(
            scheme
                .role_predicates
                .iter()
                .map(|predicate| self.role_predicate(predicate)),
        );
        if !predicates.is_empty() {
            let facts = predicates.join(", ");
            body.push_str(" where ");
            body.push_str(&facts);
        }
        body
    }

    fn role_predicate(&mut self, predicate: &RolePredicate) -> String {
        let role = path_name(&predicate.role);
        let mut inputs = predicate
            .inputs
            .iter()
            .map(|arg| self.render_role_predicate_arg(*arg))
            .collect::<Vec<_>>();
        let associated = predicate
            .associated
            .iter()
            .map(|associated| {
                format!(
                    "{} = {}",
                    associated.name,
                    self.neu(associated.value, Context::Free)
                )
            })
            .collect::<Vec<_>>();

        if inputs.is_empty() {
            return self.role_call(role, inputs, associated);
        }

        if inputs[0].has_bare_space {
            return self.role_call(role, inputs, associated);
        }

        let subject = inputs.remove(0).in_context(Context::FunctionArg);
        let role = self.role_call(role, inputs, associated);
        format!("{subject}: {role}")
    }

    fn render_role_predicate_arg(&mut self, arg: RolePredicateArg) -> Rendered {
        match arg {
            RolePredicateArg::Covariant(pos) => self.render_pos(pos),
            RolePredicateArg::Contravariant(neg) => self.render_neg(neg),
            RolePredicateArg::Invariant(neu) => self.render_neu(neu),
        }
    }

    fn role_call(&mut self, role: String, args: Vec<Rendered>, associated: Vec<String>) -> String {
        if args.is_empty() && associated.is_empty() {
            return role;
        }

        if associated.is_empty() && !args.iter().any(|arg| arg.has_bare_space) {
            let mut parts = vec![role];
            parts.extend(args.into_iter().map(|arg| arg.in_context(Context::MlArg)));
            return parts.join(" ");
        }

        let mut parts = args.into_iter().map(|arg| arg.text).collect::<Vec<_>>();
        parts.extend(associated);
        format!("{}({})", role, parts.join(", "))
    }

    fn subtractability_head(&mut self, path: &[String], args: &[NeuId]) -> String {
        let rendered = self.render_subtractability_con(path, args);
        if rendered.has_bare_space {
            format!("[{}]", rendered.in_context(Context::Free))
        } else {
            rendered.in_context(Context::Free)
        }
    }

    fn render_subtractability_con(&mut self, path: &[String], args: &[NeuId]) -> Rendered {
        let name = subtractability_path_name(path);
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
            Pos::Con(path, args) => self.render_con(path, args, NeuPolarity::Positive),
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
            Pos::Stack { inner, weight } => {
                if is_hidden_quantifier_stack(weight) {
                    return self.render_pos(*inner);
                }
                let inner = self.pos(*inner, Context::Free);
                Rendered::apply_c(format!("stack({inner}, {})", self.stack_weight(weight)))
            }
            Pos::NonSubtract(pos, subtract) => {
                let inner = self.render_pos(*pos);
                let inner = if inner.prec == Prec::Atom && !inner.has_bare_space {
                    inner.text
                } else {
                    format!("({})", inner.text)
                };
                Rendered::atom(format!("{}{}", inner, self.subtract_id(*subtract)))
            }
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
            Neg::Con(path, args) => self.render_con(path, args, NeuPolarity::Negative),
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
            Neg::Stack { inner, weight } => {
                if is_hidden_quantifier_stack(weight) {
                    return self.render_neg(*inner);
                }
                let inner = self.neg(*inner, Context::Free);
                Rendered::apply_c(format!("stack({inner}, {})", self.stack_weight(weight)))
            }
            Neg::Intersection(left, right) => {
                let parts = self.flatten_neg_intersection(*left, *right);
                Rendered::intersection(parts.join(" & "))
            }
        }
    }

    fn render_neu(&mut self, id: NeuId) -> Rendered {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                let center = self.bounds_center(*lower, *upper);
                if let Some(var) = center {
                    if self.is_plain_bounds(*lower, var, *upper) {
                        return Rendered::atom(self.namer.name(var));
                    }
                    if let Some(rendered) =
                        self.render_directional_bounds(*lower, var, *upper, NeuPolarity::Neutral)
                    {
                        return rendered;
                    }
                    return self.render_bounds(*lower, var, *upper);
                }
                self.render_centerless_bounds(*lower, *upper)
            }
            Neu::Con(path, args) => self.render_con(path, args, NeuPolarity::Neutral),
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

    fn render_neu_with_polarity(&mut self, id: NeuId, polarity: NeuPolarity) -> Rendered {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                let center = self.bounds_center(*lower, *upper);
                if let Some(var) = center {
                    if self.is_plain_bounds(*lower, var, *upper) {
                        return Rendered::atom(self.namer.name(var));
                    }
                    if let Some(rendered) =
                        self.render_directional_bounds(*lower, var, *upper, polarity)
                    {
                        return rendered;
                    }
                    return self.render_bounds(*lower, var, *upper);
                }
                self.render_centerless_bounds(*lower, *upper)
            }
            Neu::Con(path, args) => self.render_con(path, args, polarity),
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

    fn render_con(&mut self, path: &[String], args: &[NeuId], polarity: NeuPolarity) -> Rendered {
        if args.is_empty() && matches!(path, [name] if name == "unit") {
            return Rendered::atom("()");
        }
        let name = path_name(path);
        if args.is_empty() {
            return Rendered::atom(name);
        }

        let args = args
            .iter()
            .map(|arg| self.render_neu_with_polarity(*arg, polarity))
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
        self.render_neg_row_inline(id).map(|rendered| rendered.text)
    }

    fn render_neg_row_inline(&mut self, id: NegId) -> Option<Rendered> {
        match self.arena.neg(id) {
            Neg::Top => None,
            Neg::Bot => None,
            Neg::Row(items, tail) => self.render_neg_row_inline_items(items, *tail),
            Neg::Intersection(left, right) => {
                let mut parts = Vec::new();
                if let Some(left) = self.render_neg_row_intersection_part(*left) {
                    parts.push(left);
                }
                if let Some(right) = self.render_neg_row_intersection_part(*right) {
                    parts.push(right);
                }
                (!parts.is_empty()).then(|| Rendered::intersection(parts.join(" & ")))
            }
            _ => Some(self.render_neg(id)),
        }
    }

    fn render_neg_row_intersection_part(&mut self, id: NegId) -> Option<String> {
        let rendered = match self.arena.neg(id) {
            Neg::Intersection(left, right) => {
                let mut parts = Vec::new();
                if let Some(left) = self.render_neg_row_intersection_part(*left) {
                    parts.push(left);
                }
                if let Some(right) = self.render_neg_row_intersection_part(*right) {
                    parts.push(right);
                }
                (!parts.is_empty()).then(|| Rendered::intersection(parts.join(" & ")))?
            }
            Neg::Row(items, tail) => self.render_neg_row_inline_items(items, *tail)?,
            _ => self.render_neg_row_inline(id)?,
        };
        if rendered.has_bare_space {
            Some(format!("[{}]", rendered.text))
        } else {
            Some(rendered.text)
        }
    }

    fn render_neg_row_inline_items(&mut self, items: &[NegId], tail: NegId) -> Option<Rendered> {
        let items = items
            .iter()
            .map(|item| self.render_neg(*item))
            .collect::<Vec<_>>();
        let item_has_bare_space = items.iter().any(|item| item.has_bare_space);
        let item_texts = items
            .into_iter()
            .map(|item| item.in_context(Context::Free))
            .collect::<Vec<_>>();
        match self.arena.neg(tail) {
            Neg::Top if item_texts.is_empty() => None,
            Neg::Top => {
                let text = item_texts.join(", ");
                Some(Rendered {
                    text,
                    prec: Prec::Atom,
                    has_bare_space: item_has_bare_space || item_texts.len() > 1,
                })
            }
            _ => {
                let tail = self
                    .render_neg_row_inline(tail)
                    .unwrap_or_else(|| self.render_neg(tail));
                if item_texts.is_empty() {
                    Some(tail)
                } else {
                    Some(Rendered {
                        text: format!("{}; {}", item_texts.join(", "), tail.text),
                        prec: Prec::Atom,
                        has_bare_space: true,
                    })
                }
            }
        }
    }

    fn neg_row(&mut self, items: &[NegId], tail: NegId) -> String {
        self.render_neg_row_inline_items(items, tail)
            .map(|items| format!("[{}]", items.text))
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

    /// 不変な変数の仕様記法。共変部と反変部の2つ組を、共有変数を1つ選んで
    /// `lower|α&upper` と書く（spec/2026-06-02-role-system.md）。
    /// var 自身が両端の top-level union / intersection に現れる場合は重複して書かない。
    fn render_bounds(&mut self, lower: PosId, var: TypeVar, upper: NegId) -> Rendered {
        let mut lower_parts = Vec::new();
        self.bounds_lower_parts(lower, var, &mut lower_parts);
        let mut upper_parts = Vec::new();
        self.bounds_upper_parts(upper, var, &mut upper_parts);

        if lower_parts.len() == 1 && lower_parts == upper_parts {
            return lower_parts.remove(0);
        }

        let mut text = if lower_parts.is_empty() {
            self.namer.name(var)
        } else {
            format!(
                "{} | {}",
                join_rendered_text(&lower_parts, " | "),
                self.namer.name(var)
            )
        };
        if !upper_parts.is_empty() {
            text.push_str(" & ");
            text.push_str(&join_rendered_text(&upper_parts, " & "));
        }
        if !lower_parts.is_empty() {
            Rendered::union(text)
        } else if !upper_parts.is_empty() {
            Rendered::intersection(text)
        } else {
            Rendered::atom(text)
        }
    }

    fn render_centerless_bounds(&mut self, lower: PosId, upper: NegId) -> Rendered {
        let mut lower_parts = Vec::new();
        self.bounds_lower_parts_without_center(lower, &mut lower_parts);
        let mut upper_parts = Vec::new();
        self.bounds_upper_parts_without_center(upper, &mut upper_parts);

        if lower_parts.len() == 1 && lower_parts == upper_parts {
            return lower_parts.remove(0);
        }
        if upper_parts.is_empty() {
            return Rendered::union(join_rendered_text(&lower_parts, " | "));
        }
        if lower_parts.is_empty() {
            return Rendered::intersection(join_rendered_text(&upper_parts, " & "));
        }
        Rendered {
            text: format!(
                "{} <: {}",
                join_rendered_text(&lower_parts, " | "),
                join_rendered_text(&upper_parts, " & ")
            ),
            prec: Prec::Atom,
            has_bare_space: true,
        }
    }

    fn bounds_center(&self, lower: PosId, upper: NegId) -> Option<TypeVar> {
        let mut lower_vars = Vec::new();
        self.bounds_lower_top_vars(lower, &mut lower_vars);
        lower_vars.sort_by_key(|var| var.0);
        lower_vars.dedup();
        let mut upper_vars = Vec::new();
        self.bounds_upper_top_vars(upper, &mut upper_vars);
        upper_vars.sort_by_key(|var| var.0);
        upper_vars.dedup();
        let common = lower_vars
            .into_iter()
            .filter(|var| upper_vars.contains(var))
            .collect::<Vec<_>>();
        (common.len() == 1).then(|| common[0])
    }

    fn bounds_lower_top_vars(&self, id: PosId, out: &mut Vec<TypeVar>) {
        match self.arena.pos(id) {
            Pos::Var(var) => out.push(*var),
            Pos::Stack { inner, weight } if is_hidden_quantifier_stack(weight) => {
                self.bounds_lower_top_vars(*inner, out);
            }
            Pos::Union(left, right) => {
                self.bounds_lower_top_vars(*left, out);
                self.bounds_lower_top_vars(*right, out);
            }
            _ => {}
        }
    }

    fn bounds_upper_top_vars(&self, id: NegId, out: &mut Vec<TypeVar>) {
        match self.arena.neg(id) {
            Neg::Var(var) => out.push(*var),
            Neg::Stack { inner, weight } if is_hidden_quantifier_stack(weight) => {
                self.bounds_upper_top_vars(*inner, out);
            }
            Neg::Intersection(left, right) => {
                self.bounds_upper_top_vars(*left, out);
                self.bounds_upper_top_vars(*right, out);
            }
            _ => {}
        }
    }

    fn bounds_lower_parts(&mut self, id: PosId, var: TypeVar, out: &mut Vec<Rendered>) {
        if self.pos_is_plain_bounds_var(id, var) {
            return;
        }
        match self.arena.pos(id) {
            Pos::Union(left, right) => {
                let (left, right) = (*left, *right);
                self.bounds_lower_parts(left, var, out);
                self.bounds_lower_parts(right, var, out);
            }
            Pos::Bot => {}
            _ => out.push(self.render_pos(id).into_context(Context::FunctionArg)),
        }
    }

    fn bounds_upper_parts(&mut self, id: NegId, var: TypeVar, out: &mut Vec<Rendered>) {
        if self.neg_is_plain_bounds_var(id, var) {
            return;
        }
        match self.arena.neg(id) {
            Neg::Intersection(left, right) => {
                let (left, right) = (*left, *right);
                self.bounds_upper_parts(left, var, out);
                self.bounds_upper_parts(right, var, out);
            }
            Neg::Top => {}
            _ => out.push(self.render_neg(id).into_context(Context::FunctionArg)),
        }
    }

    fn bounds_lower_parts_without_center(&mut self, id: PosId, out: &mut Vec<Rendered>) {
        match self.arena.pos(id) {
            Pos::Union(left, right) => {
                let (left, right) = (*left, *right);
                self.bounds_lower_parts_without_center(left, out);
                self.bounds_lower_parts_without_center(right, out);
            }
            Pos::Bot => {}
            _ => out.push(self.render_pos(id).into_context(Context::FunctionArg)),
        }
    }

    fn bounds_upper_parts_without_center(&mut self, id: NegId, out: &mut Vec<Rendered>) {
        match self.arena.neg(id) {
            Neg::Intersection(left, right) => {
                let (left, right) = (*left, *right);
                self.bounds_upper_parts_without_center(left, out);
                self.bounds_upper_parts_without_center(right, out);
            }
            Neg::Top => {}
            _ => out.push(self.render_neg(id).into_context(Context::FunctionArg)),
        }
    }

    fn is_plain_bounds(&self, lower: PosId, var: TypeVar, upper: NegId) -> bool {
        matches!(self.arena.pos(lower), Pos::Bot) && matches!(self.arena.neg(upper), Neg::Top)
            || self.pos_is_plain_bounds_var(lower, var) && self.neg_is_plain_bounds_var(upper, var)
    }

    fn pos_is_plain_bounds_var(&self, id: PosId, var: TypeVar) -> bool {
        match self.arena.pos(id) {
            Pos::Var(found) => *found == var,
            Pos::Stack { inner, weight } if is_hidden_quantifier_stack(weight) => {
                self.pos_is_plain_bounds_var(*inner, var)
            }
            _ => false,
        }
    }

    fn neg_is_plain_bounds_var(&self, id: NegId, var: TypeVar) -> bool {
        match self.arena.neg(id) {
            Neg::Var(found) => *found == var,
            Neg::Stack { inner, weight } if is_hidden_quantifier_stack(weight) => {
                self.neg_is_plain_bounds_var(*inner, var)
            }
            _ => false,
        }
    }

    fn render_directional_bounds(
        &mut self,
        lower: PosId,
        var: TypeVar,
        upper: NegId,
        polarity: NeuPolarity,
    ) -> Option<Rendered> {
        match polarity {
            NeuPolarity::Negative
                if matches!(self.arena.pos(lower), Pos::Var(lower_var) if *lower_var == var)
                    && neg_contains_var(self.arena, upper, var)
                    && !matches!(self.arena.neg(upper), Neg::Var(upper_var) if *upper_var == var) =>
            {
                Some(self.render_neg(upper))
            }
            NeuPolarity::Positive
                if matches!(self.arena.neg(upper), Neg::Var(upper_var) if *upper_var == var)
                    && pos_contains_var(self.arena, lower, var)
                    && !matches!(self.arena.pos(lower), Pos::Var(lower_var) if *lower_var == var) =>
            {
                Some(self.render_pos(lower))
            }
            NeuPolarity::Neutral | NeuPolarity::Positive | NeuPolarity::Negative => None,
        }
    }

    fn subtract_id(&self, subtract: SubtractId) -> String {
        format!("#{}", subtract.0)
    }

    fn stack_weight(&mut self, weight: &StackWeight) -> String {
        if weight.is_empty() {
            return "@0".to_string();
        }
        let entries = weight
            .entries()
            .iter()
            .map(|entry| {
                let floor = entry
                    .floor
                    .iter()
                    .map(|subtractability| self.stack_subtractability(subtractability))
                    .collect::<Vec<_>>()
                    .join(", ");
                let stack = entry
                    .stack
                    .iter()
                    .map(|subtractability| self.stack_subtractability(subtractability))
                    .collect::<Vec<_>>()
                    .join(", ");
                if entry.floor.is_empty() {
                    format!("#{} -> pop({})[{}]", entry.id.0, entry.pops, stack)
                } else {
                    format!(
                        "#{} -> floor[{}] pop({})[{}]",
                        entry.id.0, floor, entry.pops, stack
                    )
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("{{ {entries} }}")
    }

    fn stack_subtractability(&mut self, subtractability: &Subtractability) -> String {
        match subtractability {
            Subtractability::Empty => "Empty".to_string(),
            Subtractability::All => "All".to_string(),
            Subtractability::Set(path, args) => self.subtractability_head(path, args),
            Subtractability::SetMany(families) => families
                .iter()
                .map(|(path, args)| self.subtractability_head(path, args))
                .collect::<Vec<_>>()
                .join(", "),
            Subtractability::AllExcept(path, args) => {
                format!("AllExcept({})", self.subtractability_head(path, args))
            }
            Subtractability::AllExceptMany(families) => {
                let heads = families
                    .iter()
                    .map(|(path, args)| self.subtractability_head(path, args))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("AllExcept({heads})")
            }
        }
    }
}

fn pos_contains_var(arena: &TypeArena, id: PosId, expected: TypeVar) -> bool {
    match arena.pos(id) {
        Pos::Var(var) => *var == expected,
        Pos::Fun { ret_eff, ret, .. } => {
            pos_contains_var(arena, *ret_eff, expected) || pos_contains_var(arena, *ret, expected)
        }
        Pos::Record(fields) => fields
            .iter()
            .any(|field| pos_contains_var(arena, field.value, expected)),
        Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { tail, fields } => {
            pos_contains_var(arena, *tail, expected)
                || fields
                    .iter()
                    .any(|field| pos_contains_var(arena, field.value, expected))
        }
        Pos::PolyVariant(items) => items
            .iter()
            .flat_map(|(_, payloads)| payloads)
            .any(|payload| pos_contains_var(arena, *payload, expected)),
        Pos::Tuple(items) | Pos::Row(items) => items
            .iter()
            .any(|item| pos_contains_var(arena, *item, expected)),
        Pos::Stack { inner, .. } => pos_contains_var(arena, *inner, expected),
        Pos::NonSubtract(pos, _) => pos_contains_var(arena, *pos, expected),
        Pos::Union(left, right) => {
            pos_contains_var(arena, *left, expected) || pos_contains_var(arena, *right, expected)
        }
        Pos::Bot | Pos::Con(_, _) => false,
    }
}

fn join_rendered_text(parts: &[Rendered], separator: &str) -> String {
    parts
        .iter()
        .map(|part| part.text.as_str())
        .collect::<Vec<_>>()
        .join(separator)
}

fn neg_contains_var(arena: &TypeArena, id: NegId, expected: TypeVar) -> bool {
    match arena.neg(id) {
        Neg::Var(var) => *var == expected,
        Neg::Fun { arg, arg_eff, .. } => {
            pos_contains_var(arena, *arg, expected) || pos_contains_var(arena, *arg_eff, expected)
        }
        Neg::Record(fields) => fields
            .iter()
            .any(|field| neg_contains_var(arena, field.value, expected)),
        Neg::PolyVariant(items) => items
            .iter()
            .flat_map(|(_, payloads)| payloads)
            .any(|payload| neg_contains_var(arena, *payload, expected)),
        Neg::Tuple(items) => items
            .iter()
            .any(|item| neg_contains_var(arena, *item, expected)),
        Neg::Row(items, tail) => {
            items
                .iter()
                .any(|item| neg_contains_var(arena, *item, expected))
                || neg_contains_var(arena, *tail, expected)
        }
        Neg::Stack { inner, .. } => neg_contains_var(arena, *inner, expected),
        Neg::Intersection(left, right) => {
            neg_contains_var(arena, *left, expected) || neg_contains_var(arena, *right, expected)
        }
        Neg::Top | Neg::Bot | Neg::Con(_, _) => false,
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

fn is_hidden_quantifier_stack(weight: &StackWeight) -> bool {
    !weight.entries().is_empty()
        && weight
            .entries()
            .iter()
            .all(|entry| entry.stack.is_empty() && entry.pops == u32::MAX)
}

fn path_name(path: &[String]) -> String {
    path.iter()
        .map(|segment| surface_name(segment))
        .collect::<Vec<_>>()
        .join("::")
}

fn subtractability_path_name(path: &[String]) -> String {
    path.iter()
        .map(|segment| subtractability_surface_name(segment))
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

fn subtractability_surface_name(name: &str) -> String {
    if is_plain_name(name) || is_sigil_name(name) {
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

fn is_sigil_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    matches!(first, '&' | '$') && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
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
        let neu_a = arena.alloc_neu(Neu::Bounds(pos_a, neg_a));
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
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
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
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
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
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
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
    fn brackets_row_intersection_parts_with_bare_space() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let e = TypeVar(1);
        let arg = arena.alloc_neg(Neg::Var(a));
        let signal = arena.alloc_neg(Neg::Con(vec!["signal".into()], Vec::new()));
        let row_tail = arena.alloc_neg(Neg::Var(e));
        let row = arena.alloc_neg(Neg::Row(vec![signal], row_tail));
        let var = arena.alloc_neg(Neg::Var(e));
        let arg_eff = arena.alloc_neg(Neg::Intersection(var, row));
        let ret_eff = arena.alloc_pos(Pos::Bot);
        let ret = arena.alloc_pos(Pos::Var(a));
        let predicate = arena.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        let scheme = Scheme {
            quantifiers: vec![a, e],
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        };

        assert_eq!(
            format_scheme(&arena, &scheme),
            "'a ['b & [signal; 'b]] -> 'a"
        );
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
        let neu_a = arena.alloc_neu(Neu::Bounds(pos_a, neg_a));
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
        let neu_a = arena.alloc_neu(Neu::Bounds(pos_a, neg_a));
        let inner = arena.alloc_neu(Neu::Con(vec!["list".into()], vec![neu_a]));
        let outer = arena.alloc_pos(Pos::Con(vec!["list".into()], vec![inner]));

        assert_eq!(format_pos(&arena, outer), "list(list 'a)");
    }

    #[test]
    fn formats_exact_pinned_bounds_as_concrete() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let item_pos = arena.alloc_pos(Pos::Con(vec!["file".into()], Vec::new()));
        let item_neg = arena.alloc_neg(Neg::Con(vec!["file".into()], Vec::new()));
        let var_pos = arena.alloc_pos(Pos::Var(a));
        let var_neg = arena.alloc_neg(Neg::Var(a));
        let lower = arena.alloc_pos(Pos::Union(item_pos, var_pos));
        let upper = arena.alloc_neg(Neg::Intersection(var_neg, item_neg));
        let arg = arena.alloc_neu(Neu::Bounds(lower, upper));
        let outer = arena.alloc_pos(Pos::Con(vec!["box".into()], vec![arg]));

        assert_eq!(format_pos(&arena, outer), "box file");
    }

    #[test]
    fn exact_bounds_keep_rendered_bare_space_metadata() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let neu_a = plain_neu(&mut arena, a);
        let lower = arena.alloc_pos(Pos::Con(vec!["list".into()], vec![neu_a]));
        let upper = arena.alloc_neg(Neg::Con(vec!["list".into()], vec![neu_a]));
        let exact = arena.alloc_neu(Neu::Bounds(lower, upper));
        let outer = arena.alloc_pos(Pos::Con(vec!["box".into()], vec![exact]));

        assert_eq!(format_pos(&arena, outer), "box(list 'a)");
    }

    #[test]
    fn hidden_quantifier_stack_does_not_duplicate_bounds_var() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let subtract = SubtractId(1);
        let pos_a = arena.alloc_pos(Pos::Var(a));
        let stacked_a = arena.alloc_pos(Pos::Stack {
            inner: pos_a,
            weight: StackWeight::pops(subtract, u32::MAX),
        });
        let neg_a = arena.alloc_neg(Neg::Var(a));
        let neu_a = arena.alloc_neu(Neu::Bounds(stacked_a, neg_a));
        let list_a = arena.alloc_pos(Pos::Con(vec!["list".into()], vec![neu_a]));
        let scheme = Scheme {
            quantifiers: vec![a],
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: vec![subtract],
            predicate: list_a,
        };

        assert_eq!(format_scheme(&arena, &scheme), "list 'a");
    }

    #[test]
    fn brackets_stack_subtractability_head_with_bare_space() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let neu_a = plain_neu(&mut arena, a);
        let inner = arena.alloc_pos(Pos::Var(a));
        let stacked = arena.alloc_pos(Pos::Stack {
            inner,
            weight: StackWeight::push(
                SubtractId(2),
                crate::types::Subtractability::Set(vec!["&var".into()], vec![neu_a]),
            ),
        });

        assert_eq!(
            format_pos(&arena, stacked),
            "stack('a, { #2 -> pop(0)[[&var 'a]] })"
        );
    }

    #[test]
    fn formats_role_predicates_as_scheme_where_suffix() {
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
                inputs: vec![
                    RolePredicateArg::Invariant(neu_a),
                    RolePredicateArg::Invariant(neu_b),
                ],
                associated: vec![crate::types::RoleAssociatedType {
                    name: "out".into(),
                    value: neu_c,
                }],
            }],
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        };

        assert_eq!(
            format_scheme(&arena, &scheme),
            "'c where 'a: Mul('b, out = 'c)"
        );
    }

    #[test]
    fn formats_multi_input_role_predicate_with_first_input_as_subject() {
        let mut arena = TypeArena::new();
        let container = TypeVar(0);
        let key = TypeVar(1);
        let item = TypeVar(2);
        let neu_container = plain_neu(&mut arena, container);
        let neu_key = plain_neu(&mut arena, key);
        let neu_item = plain_neu(&mut arena, item);
        let predicate = arena.alloc_pos(Pos::Var(item));
        let scheme = Scheme {
            quantifiers: vec![container, key, item],
            role_predicates: vec![RolePredicate {
                role: vec!["Index".into()],
                inputs: vec![
                    RolePredicateArg::Invariant(neu_container),
                    RolePredicateArg::Invariant(neu_key),
                ],
                associated: vec![crate::types::RoleAssociatedType {
                    name: "value".into(),
                    value: neu_item,
                }],
            }],
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        };

        assert_eq!(
            format_scheme(&arena, &scheme),
            "'c where 'a: Index('b, value = 'c)"
        );
    }

    #[test]
    fn formats_role_predicate_with_union_subject_as_call() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let b = TypeVar(1);
        let c = TypeVar(2);
        let pos_a = arena.alloc_pos(Pos::Var(a));
        let pos_b = arena.alloc_pos(Pos::Var(b));
        let union = arena.alloc_pos(Pos::Union(pos_a, pos_b));
        let predicate = arena.alloc_pos(Pos::Var(c));
        let scheme = Scheme {
            quantifiers: vec![a, b, c],
            role_predicates: vec![RolePredicate {
                role: vec!["Debug".into()],
                inputs: vec![RolePredicateArg::Covariant(union)],
                associated: Vec::new(),
            }],
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        };

        assert_eq!(format_scheme(&arena, &scheme), "'c where Debug('a | 'b)");
    }

    #[test]
    fn formats_role_predicate_with_applied_subject_as_call() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let b = TypeVar(1);
        let c = TypeVar(2);
        let neu_a = plain_neu(&mut arena, a);
        let neu_b = plain_neu(&mut arena, b);
        let list_a = arena.alloc_neu(Neu::Con(vec!["list".into()], vec![neu_a]));
        let predicate = arena.alloc_pos(Pos::Var(c));
        let scheme = Scheme {
            quantifiers: vec![a, b, c],
            role_predicates: vec![RolePredicate {
                role: vec!["Role".into()],
                inputs: vec![
                    RolePredicateArg::Invariant(list_a),
                    RolePredicateArg::Invariant(neu_b),
                ],
                associated: Vec::new(),
            }],
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        };

        assert_eq!(format_scheme(&arena, &scheme), "'c where Role(list 'a, 'b)");
    }

    #[test]
    fn spaces_sandwich_bounds_operators() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let int_pos = arena.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
        let var_pos = arena.alloc_pos(Pos::Var(a));
        let lower = arena.alloc_pos(Pos::Union(int_pos, var_pos));
        let var_neg = arena.alloc_neg(Neg::Var(a));
        let str_neg = arena.alloc_neg(Neg::Con(vec!["str".into()], Vec::new()));
        let upper = arena.alloc_neg(Neg::Intersection(var_neg, str_neg));
        let bounds = arena.alloc_neu(Neu::Bounds(lower, upper));

        assert_eq!(format_neu(&arena, bounds), "int | 'a & str");
    }

    #[test]
    fn formats_non_subtract_as_weight_suffix() {
        let mut arena = TypeArena::new();
        let a = TypeVar(0);
        let pos_a = arena.alloc_pos(Pos::Var(a));
        let weighted = arena.alloc_pos(Pos::NonSubtract(pos_a, SubtractId(1)));

        assert_eq!(format_pos(&arena, weighted), "'a#1");
    }

    fn plain_neu(arena: &mut TypeArena, var: TypeVar) -> NeuId {
        let pos = arena.alloc_pos(Pos::Var(var));
        let neg = arena.alloc_neg(Neg::Var(var));
        arena.alloc_neu(Neu::Bounds(pos, neg))
    }
}
