//! `poly::Arena` を短いテキストへ落とす debug dump。
//!
//! 式は一行に畳み、定義は一行、module だけをインデントしたブロックとして表示する。
//! lowering / resolver / SCC の足場を作る途中で、どの `DefId` がどこに現れ、
//! `RefId` / `SelectId` がどこまで解けているかを読むための表現である。

use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Write as _;

use crate::expr::{
    Arena, Def, DefId, Expr, ExprId, Lit, Pat, PatId, RecordSpread, RefId, SelectId,
    SelectResolution, Stmt, Vis,
};

mod type_format;
pub use self::type_format::{format_neg, format_neu, format_pos, format_scheme};

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

/// compact dump にだけ使う表示名 table。
///
/// `poly` 本体は source 名を必須にしない。resolver / lowering 側が名前を持っている場合だけ、
/// debug 表示用に `d0:name` / `r0:name` のような補助 label を足せる。
#[derive(Debug, Clone, Default)]
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
}

struct Dumper<'a> {
    arena: &'a Arena,
    labels: &'a DumpLabels,
    out: String,
    visited_defs: FxHashSet<DefId>,
}

impl<'a> Dumper<'a> {
    fn new(arena: &'a Arena, labels: &'a DumpLabels) -> Self {
        Self {
            arena,
            labels,
            out: String::new(),
            visited_defs: FxHashSet::default(),
        }
    }

    fn dump(mut self) -> String {
        let roots = self
            .arena
            .roots
            .iter()
            .map(|id| self.def_id(*id))
            .collect::<Vec<_>>()
            .join(" ");
        if roots.is_empty() {
            let _ = writeln!(self.out, "roots");
        } else {
            let _ = writeln!(self.out, "roots {roots}");
        }

        for root in &self.arena.roots {
            self.write_def(*root, 0);
        }

        let detached = self.detached_defs();
        if !detached.is_empty() {
            let _ = writeln!(self.out, "detached {{");
            for id in detached {
                if !self.visited_defs.contains(&id) {
                    self.write_def(id, 1);
                }
            }
            let _ = writeln!(self.out, "}}");
        }

        self.out
    }

    fn detached_defs(&self) -> Vec<DefId> {
        let mut ids = self
            .arena
            .defs
            .iter()
            .map(|(id, _)| id)
            .filter(|id| !self.visited_defs.contains(id))
            .collect::<Vec<_>>();
        ids.sort_by_key(|id| id.0);
        ids
    }

    fn write_def(&mut self, id: DefId, indent: usize) {
        self.write_indent(indent);
        if !self.visited_defs.insert(id) {
            let _ = writeln!(self.out, "{} <seen>", self.def_id(id));
            return;
        }

        let Some(def) = self.arena.defs.get(id) else {
            let _ = writeln!(self.out, "{} <missing>", self.def_id(id));
            return;
        };

        match def {
            Def::Mod { vis, children } => {
                let _ = writeln!(self.out, "{}{} mod {{", vis_prefix(*vis), self.def_id(id));
                self.write_children(children, indent + 1);
                self.write_indent(indent);
                let _ = writeln!(self.out, "}}");
            }
            Def::Let {
                vis,
                scheme,
                body,
                children,
            } => {
                let expr = body
                    .map(|body| self.expr(body))
                    .unwrap_or_else(|| "<missing>".to_string());
                let head = self.let_head(*vis, id, scheme.as_ref());
                if children.is_empty() {
                    let _ = writeln!(self.out, "{head} = {expr}");
                } else {
                    let _ = writeln!(self.out, "{head} = {expr} {{");
                    self.write_children(children, indent + 1);
                    self.write_indent(indent);
                    let _ = writeln!(self.out, "}}");
                }
            }
            Def::Arg => {
                let _ = writeln!(self.out, "{} arg", self.def_id(id));
            }
        }
    }

    fn let_head(&self, vis: Vis, id: DefId, scheme: Option<&crate::types::Scheme>) -> String {
        let head = format!("{}{}", vis_prefix(vis), self.def_id(id));
        match scheme {
            Some(scheme) => format!("{head}: {}", format_scheme(&self.arena.typ, scheme)),
            None => head,
        }
    }

    fn write_children(&mut self, children: &[DefId], indent: usize) {
        for child in children {
            self.write_def(*child, indent);
        }
    }

    fn write_indent(&mut self, indent: usize) {
        for _ in 0..indent {
            self.out.push_str("  ");
        }
    }

    fn expr(&self, id: ExprId) -> String {
        format!("e{}:{}", id.0, self.expr_body(id))
    }

    fn expr_body(&self, id: ExprId) -> String {
        match self.arena.expr(id) {
            Expr::Lit(lit) => self.lit(lit),
            Expr::Var(reference) => self.ref_id(*reference),
            Expr::App(callee, arg) => format!("({} {})", self.expr(*callee), self.expr(*arg)),
            Expr::RefSet(target, value) => {
                format!("({} := {})", self.expr(*target), self.expr(*value))
            }
            Expr::Lambda(param, body) => {
                format!("(fn {} -> {})", self.pat(*param), self.expr(*body))
            }
            Expr::Tuple(items) => self.tuple_expr(items),
            Expr::Record { fields, spread } => self.record_expr(fields, spread),
            Expr::PolyVariant(name, payloads) => self.poly_variant_expr(name, payloads),
            Expr::Select(receiver, select) => {
                format!("({}.{})", self.expr(*receiver), self.select_id(*select))
            }
            Expr::Case(scrutinee, arms) => self.case_expr(*scrutinee, arms),
            Expr::Catch(body, arms) => self.catch_expr(*body, arms),
            Expr::Block(stmts, tail) => self.block_expr(stmts, *tail),
        }
    }

    fn pat(&self, id: PatId) -> String {
        format!("p{}:{}", id.0, self.pat_body(id))
    }

    fn pat_body(&self, id: PatId) -> String {
        match self.arena.pat(id) {
            Pat::Wild => "_".to_string(),
            Pat::Lit(lit) => self.lit(lit),
            Pat::Tuple(items) => self.tuple_pat(items),
            Pat::List {
                prefix,
                spread,
                suffix,
            } => self.list_pat(prefix, *spread, suffix),
            Pat::Record { fields, spread } => self.record_pat(fields, spread),
            Pat::PolyVariant(name, payloads) => self.poly_variant_pat(name, payloads),
            Pat::Con(reference, payloads) => {
                if payloads.is_empty() {
                    self.ref_id(*reference)
                } else {
                    format!("{}({})", self.ref_id(*reference), self.join_pats(payloads))
                }
            }
            Pat::Ref(reference) => format!("ref {}", self.ref_id(*reference)),
            Pat::Var(def) => self.def_id(*def),
            Pat::Or(lhs, rhs) => format!("({} | {})", self.pat(*lhs), self.pat(*rhs)),
            Pat::As(pat, def) => format!("({} as {})", self.pat(*pat), self.def_id(*def)),
        }
    }

    fn tuple_expr(&self, items: &[ExprId]) -> String {
        match items {
            [] => "()".to_string(),
            [only] => format!("({},)", self.expr(*only)),
            _ => format!("({})", self.join_exprs(items)),
        }
    }

    fn tuple_pat(&self, items: &[PatId]) -> String {
        match items {
            [] => "()".to_string(),
            [only] => format!("({},)", self.pat(*only)),
            _ => format!("({})", self.join_pats(items)),
        }
    }

    fn list_pat(&self, prefix: &[PatId], spread: Option<PatId>, suffix: &[PatId]) -> String {
        let mut parts = prefix.iter().map(|id| self.pat(*id)).collect::<Vec<_>>();
        if let Some(spread) = spread {
            parts.push(format!("..{}", self.pat(spread)));
        }
        parts.extend(suffix.iter().map(|id| self.pat(*id)));
        format!("[{}]", parts.join(", "))
    }

    fn record_expr(&self, fields: &[(String, ExprId)], spread: &RecordSpread<ExprId>) -> String {
        let mut parts = Vec::new();
        if let RecordSpread::Head(spread) = spread {
            parts.push(format!("..{}", self.expr(*spread)));
        }
        parts.extend(
            fields
                .iter()
                .map(|(name, expr)| format!("{}: {}", field_name(name), self.expr(*expr))),
        );
        if let RecordSpread::Tail(spread) = spread {
            parts.push(format!("..{}", self.expr(*spread)));
        }
        format!("{{{}}}", parts.join(", "))
    }

    fn record_pat(&self, fields: &[(String, PatId)], spread: &RecordSpread<DefId>) -> String {
        let mut parts = Vec::new();
        if let RecordSpread::Head(spread) = spread {
            parts.push(format!("..{}", self.def_id(*spread)));
        }
        parts.extend(
            fields
                .iter()
                .map(|(name, pat)| format!("{}: {}", field_name(name), self.pat(*pat))),
        );
        if let RecordSpread::Tail(spread) = spread {
            parts.push(format!("..{}", self.def_id(*spread)));
        }
        format!("{{{}}}", parts.join(", "))
    }

    fn poly_variant_expr(&self, name: &str, payloads: &[ExprId]) -> String {
        if payloads.is_empty() {
            format!(":{}", field_name(name))
        } else {
            format!(":{}({})", field_name(name), self.join_exprs(payloads))
        }
    }

    fn poly_variant_pat(&self, name: &str, payloads: &[PatId]) -> String {
        if payloads.is_empty() {
            format!(":{}", field_name(name))
        } else {
            format!(":{}({})", field_name(name), self.join_pats(payloads))
        }
    }

    fn case_expr(&self, scrutinee: ExprId, arms: &[(PatId, ExprId)]) -> String {
        let arms = arms
            .iter()
            .map(|(pat, body)| format!("{} -> {}", self.pat(*pat), self.expr(*body)))
            .collect::<Vec<_>>()
            .join("; ");
        if arms.is_empty() {
            format!("case {} {{}}", self.expr(scrutinee))
        } else {
            format!("case {} {{ {arms} }}", self.expr(scrutinee))
        }
    }

    fn catch_expr(&self, body: ExprId, arms: &[(PatId, Option<PatId>, ExprId)]) -> String {
        let arms = arms
            .iter()
            .map(|(pat, guard, handler)| {
                let guard = guard
                    .map(|guard| format!(" if {}", self.pat(guard)))
                    .unwrap_or_default();
                format!("{}{} -> {}", self.pat(*pat), guard, self.expr(*handler))
            })
            .collect::<Vec<_>>()
            .join("; ");
        if arms.is_empty() {
            format!("catch {} {{}}", self.expr(body))
        } else {
            format!("catch {} {{ {arms} }}", self.expr(body))
        }
    }

    fn block_expr(&self, stmts: &[Stmt], tail: Option<ExprId>) -> String {
        let mut parts = stmts.iter().map(|stmt| self.stmt(stmt)).collect::<Vec<_>>();
        if let Some(tail) = tail {
            parts.push(self.expr(tail));
        }
        if parts.is_empty() {
            "block {}".to_string()
        } else {
            format!("block {{ {} }}", parts.join("; "))
        }
    }

    fn stmt(&self, stmt: &Stmt) -> String {
        match stmt {
            Stmt::Let(vis, pat, expr) => {
                format!(
                    "let {}{} = {}",
                    vis_prefix(*vis),
                    self.pat(*pat),
                    self.expr(*expr)
                )
            }
            Stmt::Expr(expr) => self.expr(*expr),
            Stmt::Module(def, stmts) => {
                let stmts = stmts
                    .iter()
                    .map(|stmt| self.stmt(stmt))
                    .collect::<Vec<_>>()
                    .join("; ");
                format!("module {} {{ {stmts} }}", self.def_id(*def))
            }
        }
    }

    fn join_exprs(&self, ids: &[ExprId]) -> String {
        ids.iter()
            .map(|id| self.expr(*id))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn join_pats(&self, ids: &[PatId]) -> String {
        ids.iter()
            .map(|id| self.pat(*id))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn lit(&self, lit: &Lit) -> String {
        match lit {
            Lit::Int(value) => value.to_string(),
            Lit::BigInt(value) => format!("{value}n"),
            Lit::Float(value) => float_lit(*value),
            Lit::Str(value) => format!("{value:?}"),
            Lit::Bool(value) => value.to_string(),
            Lit::Unit => "()".to_string(),
        }
    }

    fn ref_id(&self, id: RefId) -> String {
        let mut out = self.id_with_label("r", id.0, self.labels.refs.get(&id));
        match self.arena.ref_target(id) {
            Some(target) => {
                out.push_str("->");
                out.push_str(&self.def_id(target));
            }
            None => out.push('?'),
        }
        out
    }

    fn select_id(&self, id: SelectId) -> String {
        let select = self.arena.select(id);
        let mut out = format!("s{}.{}", id.0, field_name(&select.name));
        match select.resolution {
            Some(SelectResolution::RecordField) => out.push_str("#field"),
            Some(SelectResolution::Method { def }) => {
                out.push_str("->");
                out.push_str(&self.def_id(def));
            }
            Some(SelectResolution::TypeclassMethod { member }) => {
                out.push_str("=>");
                out.push_str(&self.def_id(member));
            }
            None => out.push('?'),
        }
        out
    }

    fn def_id(&self, id: DefId) -> String {
        self.id_with_label("d", id.0, self.labels.defs.get(&id))
    }

    fn id_with_label(&self, prefix: &str, number: u32, label: Option<&String>) -> String {
        match label {
            Some(label) => format!("{prefix}{number}:{}", label_name(label)),
            None => format!("{prefix}{number}"),
        }
    }
}

fn vis_prefix(vis: Vis) -> &'static str {
    match vis {
        Vis::Pub => "pub ",
        Vis::Our => "",
        Vis::My => "my ",
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
                    predicate,
                    subtracts: Vec::new(),
                }),
                body: Some(body),
                children: Vec::new(),
            },
        );
        arena.roots.push(def);

        assert_eq!(dump_arena(&arena), "roots d0\nd0: 'a = e0:1\n");
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
