//! `poly::Arena` を短いテキストへ落とす debug dump。
//!
//! 式は一行に畳み、定義は一行、module だけをインデントしたブロックとして表示する。
//! lowering / resolver / SCC の足場を作る途中で、どの `DefId` がどこに現れ、
//! `RefId` / `SelectId` がどこまで解けているかを読むための表現である。

use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Write as _;

use crate::expr::{
    Arena, CaseArm, CatchArm, Def, DefId, Expr, ExprId, Lit, Pat, PatId, RecordSpread, RefId,
    SelectId, SelectResolution, Stmt, Vis,
};

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

    pub fn def_label(&self, id: DefId) -> Option<&str> {
        self.defs.get(&id).map(String::as_str)
    }
}

struct Dumper<'a> {
    arena: &'a Arena,
    labels: &'a DumpLabels,
    out: String,
    roots: Vec<DefId>,
    include_detached: bool,
    visited_defs: FxHashSet<DefId>,
}

struct RawDumper<'a> {
    arena: &'a Arena,
    labels: &'a DumpLabels,
    out: String,
    roots: Vec<DefId>,
    include_all_defs: bool,
    extra_defs: std::collections::BTreeSet<u32>,
    exprs: std::collections::BTreeSet<u32>,
    pats: std::collections::BTreeSet<u32>,
}

impl<'a> RawDumper<'a> {
    fn new(arena: &'a Arena, labels: &'a DumpLabels) -> Self {
        Self::new_with_roots(arena, labels, arena.roots.clone(), true)
    }

    fn new_with_roots(
        arena: &'a Arena,
        labels: &'a DumpLabels,
        roots: Vec<DefId>,
        include_all_defs: bool,
    ) -> Self {
        Self {
            arena,
            labels,
            out: String::new(),
            roots,
            include_all_defs,
            extra_defs: std::collections::BTreeSet::new(),
            exprs: std::collections::BTreeSet::new(),
            pats: std::collections::BTreeSet::new(),
        }
    }

    fn dump(mut self) -> String {
        let roots = self
            .roots
            .iter()
            .map(|id| self.def_id(*id))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(self.out, "raw roots [{roots}]");
        let _ = writeln!(self.out, "defs {{");
        let mut defs = if self.include_all_defs {
            self.arena.defs.iter().map(|(id, _)| id).collect::<Vec<_>>()
        } else {
            self.roots.clone()
        };
        defs.sort_by_key(|id| id.0);
        for id in defs {
            self.write_raw_def(id);
        }
        if !self.include_all_defs {
            let root_set = self.roots.iter().map(|id| id.0).collect::<FxHashSet<_>>();
            let extra_defs = self.extra_defs.iter().copied().collect::<Vec<_>>();
            for id in extra_defs {
                if !root_set.contains(&id) {
                    self.write_raw_def(DefId(id));
                }
            }
        }
        let _ = writeln!(self.out, "}}");
        self.write_raw_exprs();
        self.write_raw_pats();
        self.out
    }

    fn write_raw_def(&mut self, id: DefId) {
        let Some(def) = self.arena.defs.get(id) else {
            let _ = writeln!(self.out, "  {} = <missing>", self.def_id(id));
            return;
        };
        match def {
            Def::Mod { vis, children } => {
                let children = children
                    .iter()
                    .map(|child| self.def_id(*child))
                    .collect::<Vec<_>>()
                    .join(", ");
                let _ = writeln!(
                    self.out,
                    "  {} = Mod {{ vis: {}, children: [{children}] }}",
                    self.def_id(id),
                    raw_vis(*vis)
                );
            }
            Def::Let {
                vis,
                scheme,
                body,
                children,
            } => {
                let children = children
                    .iter()
                    .map(|child| self.def_id(*child))
                    .collect::<Vec<_>>()
                    .join(", ");
                let body_text = body
                    .map(|body| {
                        self.mark_expr(body);
                        self.expr_id(body)
                    })
                    .unwrap_or_else(|| "<missing>".to_string());
                let _ = writeln!(
                    self.out,
                    "  {} = Let {{ vis: {}, body: {body_text}, children: [{children}] }}",
                    self.def_id(id),
                    raw_vis(*vis)
                );
                if let Some(scheme) = scheme {
                    let _ = writeln!(self.out, "    scheme:");
                    for line in dump_scheme_raw(&self.arena.typ, scheme).lines() {
                        let _ = writeln!(self.out, "      {line}");
                    }
                }
            }
            Def::Arg => {
                let _ = writeln!(self.out, "  {} = Arg", self.def_id(id));
            }
        }
    }

    fn write_raw_exprs(&mut self) {
        if self.exprs.is_empty() {
            return;
        }
        let _ = writeln!(self.out, "exprs {{");
        let exprs = self.exprs.iter().copied().collect::<Vec<_>>();
        for id in exprs {
            let id = ExprId(id);
            let _ = writeln!(self.out, "  {} = {}", self.expr_id(id), self.raw_expr(id));
        }
        let _ = writeln!(self.out, "}}");
    }

    fn write_raw_pats(&mut self) {
        if self.pats.is_empty() {
            return;
        }
        let _ = writeln!(self.out, "pats {{");
        let pats = self.pats.iter().copied().collect::<Vec<_>>();
        for id in pats {
            let id = PatId(id);
            let _ = writeln!(self.out, "  {} = {}", self.pat_id(id), self.raw_pat(id));
        }
        let _ = writeln!(self.out, "}}");
    }

    fn mark_expr(&mut self, id: ExprId) {
        if !self.exprs.insert(id.0) {
            return;
        }
        match self.arena.expr(id) {
            Expr::Lit(_) | Expr::PrimitiveOp(_) | Expr::Var(_) => {}
            Expr::App(callee, arg) | Expr::RefSet(callee, arg) => {
                self.mark_expr(*callee);
                self.mark_expr(*arg);
            }
            Expr::Lambda(param, body) => {
                self.mark_pat(*param);
                self.mark_expr(*body);
            }
            Expr::Tuple(items) => {
                for item in items {
                    self.mark_expr(*item);
                }
            }
            Expr::Record { fields, spread } => {
                for (_, expr) in fields {
                    self.mark_expr(*expr);
                }
                if let RecordSpread::Head(spread) | RecordSpread::Tail(spread) = spread {
                    self.mark_expr(*spread);
                }
            }
            Expr::PolyVariant(_, payloads) => {
                for payload in payloads {
                    self.mark_expr(*payload);
                }
            }
            Expr::Select(receiver, _) => self.mark_expr(*receiver),
            Expr::Case(scrutinee, arms) => {
                self.mark_expr(*scrutinee);
                for arm in arms {
                    self.mark_pat(arm.pat);
                    if let Some(guard) = arm.guard {
                        self.mark_expr(guard);
                    }
                    self.mark_expr(arm.body);
                }
            }
            Expr::Catch(body, arms) => {
                self.mark_expr(*body);
                for arm in arms {
                    self.mark_pat(arm.pat);
                    if let Some(continuation) = arm.continuation {
                        self.mark_pat(continuation);
                    }
                    if let Some(guard) = arm.guard {
                        self.mark_expr(guard);
                    }
                    self.mark_expr(arm.body);
                }
            }
            Expr::Block(stmts, tail) => {
                for stmt in stmts {
                    self.mark_stmt(stmt);
                }
                if let Some(tail) = tail {
                    self.mark_expr(*tail);
                }
            }
        }
    }

    fn mark_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let(_, pat, expr) => {
                self.mark_pat(*pat);
                self.mark_expr(*expr);
            }
            Stmt::Expr(expr) => self.mark_expr(*expr),
            Stmt::Module(_, stmts) => {
                for stmt in stmts {
                    self.mark_stmt(stmt);
                }
            }
        }
    }

    fn mark_pat(&mut self, id: PatId) {
        if !self.pats.insert(id.0) {
            return;
        }
        match self.arena.pat(id) {
            Pat::Wild | Pat::Lit(_) | Pat::Ref(_) => {}
            Pat::Tuple(items) => {
                for item in items {
                    self.mark_pat(*item);
                }
            }
            Pat::List {
                prefix,
                spread,
                suffix,
            } => {
                for item in prefix {
                    self.mark_pat(*item);
                }
                if let Some(spread) = spread {
                    self.mark_pat(*spread);
                }
                for item in suffix {
                    self.mark_pat(*item);
                }
            }
            Pat::Record { fields, .. } => {
                for (_, pat) in fields {
                    self.mark_pat(*pat);
                }
            }
            Pat::PolyVariant(_, payloads) | Pat::Con(_, payloads) => {
                for payload in payloads {
                    self.mark_pat(*payload);
                }
            }
            Pat::Or(lhs, rhs) => {
                self.mark_pat(*lhs);
                self.mark_pat(*rhs);
            }
            Pat::Var(def) => {
                self.extra_defs.insert(def.0);
            }
            Pat::As(pat, def) => {
                self.extra_defs.insert(def.0);
                self.mark_pat(*pat);
            }
        }
    }

    fn raw_expr(&self, id: ExprId) -> String {
        match self.arena.expr(id) {
            Expr::Lit(lit) => format!("Lit({})", raw_lit(lit)),
            Expr::PrimitiveOp(op) => format!("PrimitiveOp({})", primitive_op_name(*op)),
            Expr::Var(reference) => format!("Var({})", self.ref_id(*reference)),
            Expr::App(callee, arg) => {
                format!("App({}, {})", self.expr_id(*callee), self.expr_id(*arg))
            }
            Expr::RefSet(target, value) => {
                format!(
                    "RefSet({}, {})",
                    self.expr_id(*target),
                    self.expr_id(*value)
                )
            }
            Expr::Lambda(param, body) => {
                format!("Lambda({}, {})", self.pat_id(*param), self.expr_id(*body))
            }
            Expr::Tuple(items) => format!("Tuple({})", self.expr_ids(items)),
            Expr::Record { fields, spread } => {
                let fields = fields
                    .iter()
                    .map(|(name, expr)| format!("{}: {}", label_name(name), self.expr_id(*expr)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("Record({fields}; spread: {})", self.expr_spread(spread))
            }
            Expr::PolyVariant(name, payloads) => {
                format!(
                    "PolyVariant({}, {})",
                    label_name(name),
                    self.expr_ids(payloads)
                )
            }
            Expr::Select(receiver, select) => {
                format!(
                    "Select({}, {})",
                    self.expr_id(*receiver),
                    self.select_id(*select)
                )
            }
            Expr::Case(scrutinee, arms) => {
                let arms = arms
                    .iter()
                    .map(|arm| {
                        let guard = arm
                            .guard
                            .map(|guard| self.expr_id(guard))
                            .unwrap_or_else(|| "none".to_string());
                        format!(
                            "{{ pat: {}, guard: {guard}, body: {} }}",
                            self.pat_id(arm.pat),
                            self.expr_id(arm.body)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("Case({}, [{arms}])", self.expr_id(*scrutinee))
            }
            Expr::Catch(body, arms) => {
                let arms = arms
                    .iter()
                    .map(|arm| {
                        let continuation = arm
                            .continuation
                            .map(|continuation| self.pat_id(continuation))
                            .unwrap_or_else(|| "none".to_string());
                        let guard = arm
                            .guard
                            .map(|guard| self.expr_id(guard))
                            .unwrap_or_else(|| "none".to_string());
                        format!(
                            "{{ pat: {}, k: {continuation}, guard: {guard}, body: {} }}",
                            self.pat_id(arm.pat),
                            self.expr_id(arm.body)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("Catch({}, [{arms}])", self.expr_id(*body))
            }
            Expr::Block(stmts, tail) => {
                let stmts = stmts
                    .iter()
                    .map(|stmt| self.raw_stmt(stmt))
                    .collect::<Vec<_>>()
                    .join(", ");
                let tail = tail
                    .map(|tail| self.expr_id(tail))
                    .unwrap_or_else(|| "none".to_string());
                format!("Block([{stmts}], {tail})")
            }
        }
    }

    fn raw_stmt(&self, stmt: &Stmt) -> String {
        match stmt {
            Stmt::Let(vis, pat, expr) => {
                format!(
                    "Let({}, {}, {})",
                    raw_vis(*vis),
                    self.pat_id(*pat),
                    self.expr_id(*expr)
                )
            }
            Stmt::Expr(expr) => format!("Expr({})", self.expr_id(*expr)),
            Stmt::Module(def, stmts) => {
                let stmts = stmts
                    .iter()
                    .map(|stmt| self.raw_stmt(stmt))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("Module({}, [{stmts}])", self.def_id(*def))
            }
        }
    }

    fn raw_pat(&self, id: PatId) -> String {
        match self.arena.pat(id) {
            Pat::Wild => "Wild".to_string(),
            Pat::Lit(lit) => format!("Lit({})", raw_lit(lit)),
            Pat::Tuple(items) => format!("Tuple({})", self.pat_ids(items)),
            Pat::List {
                prefix,
                spread,
                suffix,
            } => format!(
                "List(prefix: {}, spread: {}, suffix: {})",
                self.pat_ids(prefix),
                spread
                    .map(|spread| self.pat_id(spread))
                    .unwrap_or_else(|| "none".to_string()),
                self.pat_ids(suffix)
            ),
            Pat::Record { fields, spread } => {
                let fields = fields
                    .iter()
                    .map(|(name, pat)| format!("{}: {}", label_name(name), self.pat_id(*pat)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("Record({fields}; spread: {})", self.def_spread(spread))
            }
            Pat::PolyVariant(name, payloads) => {
                format!(
                    "PolyVariant({}, {})",
                    label_name(name),
                    self.pat_ids(payloads)
                )
            }
            Pat::Con(reference, payloads) => {
                format!(
                    "Con({}, {})",
                    self.ref_id(*reference),
                    self.pat_ids(payloads)
                )
            }
            Pat::Ref(reference) => format!("Ref({})", self.ref_id(*reference)),
            Pat::Var(def) => format!("Var({})", self.def_id(*def)),
            Pat::Or(lhs, rhs) => format!("Or({}, {})", self.pat_id(*lhs), self.pat_id(*rhs)),
            Pat::As(pat, def) => format!("As({}, {})", self.pat_id(*pat), self.def_id(*def)),
        }
    }

    fn expr_ids(&self, ids: &[ExprId]) -> String {
        format!(
            "[{}]",
            ids.iter()
                .map(|id| self.expr_id(*id))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn pat_ids(&self, ids: &[PatId]) -> String {
        format!(
            "[{}]",
            ids.iter()
                .map(|id| self.pat_id(*id))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn expr_spread(&self, spread: &RecordSpread<ExprId>) -> String {
        match spread {
            RecordSpread::None => "none".to_string(),
            RecordSpread::Head(expr) => format!("head {}", self.expr_id(*expr)),
            RecordSpread::Tail(expr) => format!("tail {}", self.expr_id(*expr)),
        }
    }

    fn def_spread(&self, spread: &RecordSpread<DefId>) -> String {
        match spread {
            RecordSpread::None => "none".to_string(),
            RecordSpread::Head(def) => format!("head {}", self.def_id(*def)),
            RecordSpread::Tail(def) => format!("tail {}", self.def_id(*def)),
        }
    }

    fn expr_id(&self, id: ExprId) -> String {
        format!("e{}", id.0)
    }

    fn pat_id(&self, id: PatId) -> String {
        format!("p{}", id.0)
    }

    fn ref_id(&self, id: RefId) -> String {
        Dumper::new(self.arena, self.labels).ref_id(id)
    }

    fn select_id(&self, id: SelectId) -> String {
        Dumper::new(self.arena, self.labels).select_id(id)
    }

    fn def_id(&self, id: DefId) -> String {
        Dumper::new(self.arena, self.labels).def_id(id)
    }
}

impl<'a> Dumper<'a> {
    fn new(arena: &'a Arena, labels: &'a DumpLabels) -> Self {
        Self::new_with_roots(arena, labels, arena.roots.clone(), true)
    }

    fn new_with_roots(
        arena: &'a Arena,
        labels: &'a DumpLabels,
        roots: Vec<DefId>,
        include_detached: bool,
    ) -> Self {
        Self {
            arena,
            labels,
            out: String::new(),
            roots,
            include_detached,
            visited_defs: FxHashSet::default(),
        }
    }

    fn dump(mut self) -> String {
        let roots = self
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

        let roots_to_write = self.roots.clone();
        for root in roots_to_write {
            self.write_def(root, 0);
        }

        if self.include_detached {
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
            Expr::PrimitiveOp(op) => format!("builtin_op::{}", primitive_op_name(*op)),
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

    fn case_expr(&self, scrutinee: ExprId, arms: &[CaseArm]) -> String {
        let arms = arms
            .iter()
            .map(|arm| {
                let guard = arm
                    .guard
                    .map(|guard| format!(" if {}", self.expr(guard)))
                    .unwrap_or_default();
                format!("{}{} -> {}", self.pat(arm.pat), guard, self.expr(arm.body))
            })
            .collect::<Vec<_>>()
            .join("; ");
        if arms.is_empty() {
            format!("case {} {{}}", self.expr(scrutinee))
        } else {
            format!("case {} {{ {arms} }}", self.expr(scrutinee))
        }
    }

    fn catch_expr(&self, body: ExprId, arms: &[CatchArm]) -> String {
        let arms = arms
            .iter()
            .map(|arm| {
                let continuation = arm
                    .continuation
                    .map(|continuation| format!(", {}", self.pat(continuation)))
                    .unwrap_or_default();
                let guard = arm
                    .guard
                    .map(|guard| format!(" if {}", self.expr(guard)))
                    .unwrap_or_default();
                format!(
                    "{}{}{} -> {}",
                    self.pat(arm.pat),
                    continuation,
                    guard,
                    self.expr(arm.body)
                )
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
                    subtracts: Vec::new(),
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
