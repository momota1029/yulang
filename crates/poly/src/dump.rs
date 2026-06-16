//! `poly::Arena` を短いテキストへ落とす debug dump。
//!
//! 式は一行に畳み、定義は一行、module だけをインデントしたブロックとして表示する。
//! lowering / resolver / SCC の足場を作る途中で、どの `DefId` がどこに現れ、
//! `RefId` / `SelectId` がどこまで解けているかを読むための表現である。

use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use std::fmt::Write as _;

use crate::expr::{
    Arena, CaseArm, CatchArm, Def, DefId, Expr, ExprId, Lit, Pat, PatId, RecordPatField,
    RecordSpread, RefId, RuntimeRoot, SelectId, SelectResolution, Stmt, Vis,
};

mod raw;
mod surface;
mod type_format;
mod type_raw;
pub use self::type_format::{format_neg, format_neu, format_pos, format_scheme};
pub use self::type_raw::{dump_neg_raw, dump_neu_raw, dump_pos_raw, dump_scheme_raw};

/// `poly::Arena` を compact dump として返す。
///
/// source 名は `poly` 単体には残らないため、標準の dump は arena-local ID だけを使う。
/// 名前も併記したい呼び出し側は `dump_arena_with_labels` に `DumpLabels` を渡す。
pub fn dump_arena(arena: &Arena) -> String {
    let labels = DumpLabels::new();
    dump_arena_with_labels(arena, &labels)
}

/// 呼び出し側が知っている source 名を併記しながら compact dump を返す。
pub fn dump_arena_with_labels(arena: &Arena, labels: &DumpLabels) -> String {
    Dumper::new(arena, labels).dump()
}

/// 指定した root def だけを compact dump として返す。
pub fn dump_defs_with_labels(arena: &Arena, labels: &DumpLabels, roots: &[DefId]) -> String {
    Dumper::new_with_roots(arena, labels, roots.to_vec(), false).dump()
}

/// 呼び出し側が知っている source 名を併記しながら raw debug dump を返す。
///
/// compact dump は surface に近い読みやすさを優先する。こちらは scheme の型 graph と
/// 式 graph を ID のまま出し、stack weight や極性付き node がどこに残ったかを見るための入口。
pub fn dump_arena_raw_with_labels(arena: &Arena, labels: &DumpLabels) -> String {
    RawDumper::new(arena, labels).dump()
}

/// 指定した root def だけを raw debug dump として返す。
pub fn dump_defs_raw_with_labels(arena: &Arena, labels: &DumpLabels, roots: &[DefId]) -> String {
    RawDumper::new_with_roots(arena, labels, roots.to_vec(), false).dump()
}

/// compact dump にだけ使う表示名 table。
///
/// `poly` 本体は source 名を必須にしない。resolver / lowering 側が名前を持っている場合だけ、
/// debug 表示用に `d0:name` / `r0:name` のような補助 label を足せる。
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DumpLabels {
    defs: FxHashMap<DefId, String>,
    refs: FxHashMap<RefId, String>,
}

impl DumpLabels {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set_def_label(&mut self, id: DefId, label: impl Into<String>) -> &mut Self {
        self.defs.insert(id, label.into());
        self
    }

    pub fn set_ref_label(&mut self, id: RefId, label: impl Into<String>) -> &mut Self {
        self.refs.insert(id, label.into());
        self
    }

    pub fn def_label(&self, id: DefId) -> Option<&str> {
        self.defs.get(&id).map(String::as_str)
    }
}

struct Dumper<'a> {
    arena: &'a Arena,
    labels: &'a DumpLabels,
    out: String,
    roots: Vec<DefId>,
    root_exprs: Vec<ExprId>,
    include_detached: bool,
    visited_defs: FxHashSet<DefId>,
}

struct RawDumper<'a> {
    arena: &'a Arena,
    labels: &'a DumpLabels,
    out: String,
    roots: Vec<DefId>,
    root_exprs: Vec<ExprId>,
    include_all_defs: bool,
    extra_defs: std::collections::BTreeSet<u32>,
    exprs: std::collections::BTreeSet<u32>,
    pats: std::collections::BTreeSet<u32>,
}

fn primitive_op_name(op: crate::expr::PrimitiveOp) -> &'static str {
    use crate::expr::PrimitiveOp;
    match op {
        PrimitiveOp::YadaYada => "yada_yada",
        PrimitiveOp::BoolNot => "bool_not",
        PrimitiveOp::BoolEq => "bool_eq",
        PrimitiveOp::ListEmpty => "list_empty",
        PrimitiveOp::ListSingleton => "list_singleton",
        PrimitiveOp::ListLen => "list_len",
        PrimitiveOp::ListMerge => "list_merge",
        PrimitiveOp::ListIndex => "list_index",
        PrimitiveOp::ListIndexRange => "list_index_range",
        PrimitiveOp::ListSplice => "list_splice",
        PrimitiveOp::ListIndexRangeRaw => "list_index_range_raw",
        PrimitiveOp::ListSpliceRaw => "list_splice_raw",
        PrimitiveOp::ListViewRaw => "list_view_raw",
        PrimitiveOp::StringLen => "string_len",
        PrimitiveOp::StringIndex => "string_index",
        PrimitiveOp::StringIndexRange => "string_index_range",
        PrimitiveOp::StringSplice => "string_splice",
        PrimitiveOp::StringIndexRangeRaw => "string_index_range_raw",
        PrimitiveOp::StringSpliceRaw => "string_splice_raw",
        PrimitiveOp::StringLineCount => "string_line_count",
        PrimitiveOp::StringLineRange => "string_line_range",
        PrimitiveOp::IntAdd => "int_add",
        PrimitiveOp::IntSub => "int_sub",
        PrimitiveOp::IntMul => "int_mul",
        PrimitiveOp::IntDiv => "int_div",
        PrimitiveOp::IntMod => "int_mod",
        PrimitiveOp::IntEq => "int_eq",
        PrimitiveOp::IntLt => "int_lt",
        PrimitiveOp::IntLe => "int_le",
        PrimitiveOp::IntGt => "int_gt",
        PrimitiveOp::IntGe => "int_ge",
        PrimitiveOp::FloatAdd => "float_add",
        PrimitiveOp::FloatSub => "float_sub",
        PrimitiveOp::FloatMul => "float_mul",
        PrimitiveOp::FloatDiv => "float_div",
        PrimitiveOp::FloatEq => "float_eq",
        PrimitiveOp::FloatLt => "float_lt",
        PrimitiveOp::FloatLe => "float_le",
        PrimitiveOp::FloatGt => "float_gt",
        PrimitiveOp::FloatGe => "float_ge",
        PrimitiveOp::StringEq => "string_eq",
        PrimitiveOp::StringConcat => "string_concat",
        PrimitiveOp::StringToBytes => "string_to_bytes",
        PrimitiveOp::CharEq => "char_eq",
        PrimitiveOp::CharToString => "char_to_string",
        PrimitiveOp::CharIsWhitespace => "char_is_whitespace",
        PrimitiveOp::CharIsPunctuation => "char_is_punctuation",
        PrimitiveOp::CharIsWord => "char_is_word",
        PrimitiveOp::BytesLen => "bytes_len",
        PrimitiveOp::BytesEq => "bytes_eq",
        PrimitiveOp::BytesConcat => "bytes_concat",
        PrimitiveOp::BytesIndex => "bytes_index",
        PrimitiveOp::BytesIndexRange => "bytes_index_range",
        PrimitiveOp::BytesToUtf8Raw => "bytes_to_utf8_raw",
        PrimitiveOp::BytesToPath => "bytes_to_path",
        PrimitiveOp::PathToBytes => "path_to_bytes",
        PrimitiveOp::IntToString => "int_to_string",
        PrimitiveOp::IntToHex => "int_to_hex",
        PrimitiveOp::IntToUpperHex => "int_to_upper_hex",
        PrimitiveOp::IntToFloat => "int_to_float",
        PrimitiveOp::FloatToString => "float_to_string",
        PrimitiveOp::BoolToString => "bool_to_string",
    }
}

fn vis_prefix(vis: Vis) -> &'static str {
    match vis {
        Vis::Pub => "pub ",
        Vis::Our => "",
        Vis::My => "my ",
    }
}

fn raw_vis(vis: Vis) -> &'static str {
    match vis {
        Vis::Pub => "pub",
        Vis::Our => "our",
        Vis::My => "my",
    }
}

fn raw_lit(lit: &Lit) -> String {
    match lit {
        Lit::Int(value) => format!("Int({value})"),
        Lit::BigInt(value) => format!("BigInt({value})"),
        Lit::Float(value) => format!("Float({})", float_lit(*value)),
        Lit::Str(value) => format!("Str({value:?})"),
        Lit::Bool(value) => format!("Bool({value})"),
        Lit::Unit => "Unit".to_string(),
    }
}

fn field_name(name: &str) -> String {
    if is_plain_name(name) {
        name.to_string()
    } else {
        format!("{name:?}")
    }
}

fn label_name(name: &str) -> String {
    if is_plain_name(name) {
        name.to_string()
    } else {
        format!("{name:?}")
    }
}

fn float_lit(value: f64) -> String {
    let mut out = value.to_string();
    if value.is_finite() && !out.contains('.') && !out.contains('e') && !out.contains('E') {
        out.push_str(".0");
    }
    out
}

fn is_plain_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Pos, Scheme, TypeVar};

    #[test]
    fn dumps_let_body_on_one_line() {
        let mut arena = Arena::new();
        let def = arena.defs.fresh();
        let body = arena.add_expr(Expr::Lit(Lit::Int(1)));
        arena.defs.set(
            def,
            Def::Let {
                vis: Vis::Our,
                scheme: None,
                body: Some(body),
                children: Vec::new(),
            },
        );
        arena.roots.push(def);

        assert_eq!(dump_arena(&arena), "roots d0\nd0 = e0:1\n");
    }

    #[test]
    fn dumps_let_scheme_before_body() {
        let mut arena = Arena::new();
        let def = arena.defs.fresh();
        let body = arena.add_expr(Expr::Lit(Lit::Int(1)));
        let var = TypeVar(0);
        let predicate = arena.typ.alloc_pos(Pos::Var(var));
        arena.defs.set(
            def,
            Def::Let {
                vis: Vis::Our,
                scheme: Some(Scheme {
                    quantifiers: vec![var],
                    role_predicates: Vec::new(),
                    recursive_bounds: Vec::new(),
                    stack_quantifiers: Vec::new(),
                    predicate,
                }),
                body: Some(body),
                children: Vec::new(),
            },
        );
        arena.roots.push(def);

        assert_eq!(dump_arena(&arena), "roots d0\nd0: 'a = e0:1\n");
    }

    #[test]
    fn raw_dump_includes_scheme_type_graph_and_expr_graph() {
        let mut arena = Arena::new();
        let def = arena.defs.fresh();
        let arg = arena.defs.fresh();
        let pat = arena.add_pat(Pat::Var(arg));
        let body = arena.add_expr(Expr::Lit(Lit::Int(1)));
        let lambda = arena.add_expr(Expr::Lambda(pat, body));
        let var = TypeVar(0);
        let arg_ty = arena.typ.alloc_neg(crate::types::Neg::Var(var));
        let arg_eff = arena.typ.alloc_neg(crate::types::Neg::Bot);
        let ret_eff = arena.typ.alloc_pos(Pos::Bot);
        let ret = arena.typ.alloc_pos(Pos::Var(var));
        let predicate = arena.typ.alloc_pos(Pos::Fun {
            arg: arg_ty,
            arg_eff,
            ret_eff,
            ret,
        });
        arena.defs.set(
            def,
            Def::Let {
                vis: Vis::Our,
                scheme: Some(Scheme {
                    quantifiers: vec![var],
                    role_predicates: Vec::new(),
                    recursive_bounds: Vec::new(),
                    stack_quantifiers: Vec::new(),
                    predicate,
                }),
                body: Some(lambda),
                children: Vec::new(),
            },
        );
        arena.defs.set(arg, Def::Arg);
        arena.roots.push(def);

        let raw = dump_arena_raw_with_labels(&arena, &DumpLabels::new());

        assert!(raw.contains("raw roots [d0]"), "{raw}");
        assert!(raw.contains("scheme {"), "{raw}");
        assert!(
            raw.contains("p2 = Fun { arg: n0, arg_eff: n1, ret_eff: p0, ret: p1 }"),
            "{raw}"
        );
        assert!(raw.contains("e1 = Lambda(p0, e0)"), "{raw}");
        assert!(raw.contains("p0 = Var(d1)"), "{raw}");
    }

    #[test]
    fn dumps_module_children_with_indentation() {
        let mut arena = Arena::new();
        let module = arena.defs.fresh();
        let value = arena.defs.fresh();
        let target = arena.defs.fresh();
        let reference = arena.add_ref();
        arena.resolve_ref(reference, target);
        let body = arena.add_expr(Expr::Var(reference));

        arena.defs.set(
            module,
            Def::Mod {
                vis: Vis::Our,
                children: vec![value, target],
            },
        );
        arena.defs.set(
            value,
            Def::Let {
                vis: Vis::Our,
                scheme: None,
                body: Some(body),
                children: Vec::new(),
            },
        );
        let target_body = arena.add_expr(Expr::Lit(Lit::Unit));
        arena.defs.set(
            target,
            Def::Let {
                vis: Vis::My,
                scheme: None,
                body: Some(target_body),
                children: Vec::new(),
            },
        );
        arena.roots.push(module);

        assert_eq!(
            dump_arena(&arena),
            "roots d0\nd0 mod {\n  d1 = e0:r0->d2\n  my d2 = e1:()\n}\n"
        );
    }

    #[test]
    fn dumps_detached_args_and_labels() {
        let mut arena = Arena::new();
        let function = arena.defs.fresh();
        let arg = arena.defs.fresh();
        let pat = arena.add_pat(Pat::Var(arg));
        let reference = arena.add_ref();
        arena.resolve_ref(reference, arg);
        let body = arena.add_expr(Expr::Var(reference));
        let lambda = arena.add_expr(Expr::Lambda(pat, body));

        arena.defs.set(
            function,
            Def::Let {
                vis: Vis::Our,
                scheme: None,
                body: Some(lambda),
                children: Vec::new(),
            },
        );
        arena.defs.set(arg, Def::Arg);
        arena.roots.push(function);

        let mut labels = DumpLabels::new();
        labels.set_def_label(function, "id");
        labels.set_def_label(arg, "x");
        labels.set_ref_label(reference, "x");

        assert_eq!(
            dump_arena_with_labels(&arena, &labels),
            "roots d0:id\nd0:id = e1:(fn p0:d1:x -> e0:r0:x->d1:x)\ndetached {\n  d1:x arg\n}\n"
        );
    }

    #[test]
    fn dumps_selection_resolution_inline() {
        let mut arena = Arena::new();
        let method = arena.defs.fresh();
        let value = arena.defs.fresh();
        let receiver = arena.add_expr(Expr::Lit(Lit::Int(1)));
        let select = arena.add_select("display");
        arena.resolve_select(select, SelectResolution::Method { def: method });
        let body = arena.add_expr(Expr::Select(receiver, select));

        arena.defs.set(method, Def::Arg);
        arena.defs.set(
            value,
            Def::Let {
                vis: Vis::Our,
                scheme: None,
                body: Some(body),
                children: Vec::new(),
            },
        );
        arena.roots.push(value);

        assert_eq!(
            dump_arena(&arena),
            "roots d1\nd1 = e1:(e0:1.s0.display->d0)\ndetached {\n  d0 arg\n}\n"
        );
    }

    #[test]
    fn detached_module_does_not_repeat_children() {
        let mut arena = Arena::new();
        let module = arena.defs.fresh();
        let value = arena.defs.fresh();
        let body = arena.add_expr(Expr::Lit(Lit::Bool(true)));

        arena.defs.set(
            module,
            Def::Mod {
                vis: Vis::Our,
                children: vec![value],
            },
        );
        arena.defs.set(
            value,
            Def::Let {
                vis: Vis::Our,
                scheme: None,
                body: Some(body),
                children: Vec::new(),
            },
        );

        assert_eq!(
            dump_arena(&arena),
            "roots\ndetached {\n  d0 mod {\n    d1 = e0:true\n  }\n}\n"
        );
    }
}
