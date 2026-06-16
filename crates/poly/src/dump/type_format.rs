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

mod formatter;

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

impl<'a> TypeFormatter<'a> {}

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
