use super::*;

impl<'a> Dumper<'a> {
    pub(super) fn new(arena: &'a Arena, labels: &'a DumpLabels) -> Self {
        Self::new_with_roots_and_exprs(
            arena,
            labels,
            arena.roots.clone(),
            arena.root_exprs.clone(),
            true,
        )
    }

    pub(super) fn new_with_roots(
        arena: &'a Arena,
        labels: &'a DumpLabels,
        roots: Vec<DefId>,
        include_detached: bool,
    ) -> Self {
        Self::new_with_roots_and_exprs(arena, labels, roots, Vec::new(), include_detached)
    }

    pub(super) fn new_with_roots_and_exprs(
        arena: &'a Arena,
        labels: &'a DumpLabels,
        roots: Vec<DefId>,
        root_exprs: Vec<ExprId>,
        include_detached: bool,
    ) -> Self {
        Self {
            arena,
            labels,
            out: String::new(),
            roots,
            root_exprs,
            include_detached,
            visited_defs: FxHashSet::default(),
        }
    }

    pub(super) fn dump(mut self) -> String {
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
        if !self.root_exprs.is_empty() {
            let root_exprs = self
                .root_exprs
                .iter()
                .map(|expr| self.expr(*expr))
                .collect::<Vec<_>>()
                .join(" ");
            let _ = writeln!(self.out, "root exprs {root_exprs}");
        }
        if !self.arena.runtime_roots.is_empty() {
            let runtime_roots = self
                .arena
                .runtime_roots
                .iter()
                .map(|root| self.runtime_root(*root))
                .collect::<Vec<_>>()
                .join(" ");
            let _ = writeln!(self.out, "runtime roots {runtime_roots}");
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

    pub(super) fn runtime_root(&self, root: RuntimeRoot) -> String {
        match root {
            RuntimeRoot::Expr(expr) => self.expr(expr),
            RuntimeRoot::ComputedDef(def) => self.def_id(def),
        }
    }

    pub(super) fn detached_defs(&self) -> Vec<DefId> {
        let root_expr_defs = self
            .arena
            .root_expr_defs
            .values()
            .map(|def| def.0)
            .collect::<FxHashSet<_>>();
        let mut ids = self
            .arena
            .defs
            .iter()
            .map(|(id, _)| id)
            .filter(|id| !self.visited_defs.contains(id))
            .filter(|id| !root_expr_defs.contains(&id.0))
            .collect::<Vec<_>>();
        ids.sort_by_key(|id| id.0);
        ids
    }

    pub(super) fn write_def(&mut self, id: DefId, indent: usize) {
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

    pub(super) fn let_head(
        &self,
        vis: Vis,
        id: DefId,
        scheme: Option<&crate::types::Scheme>,
    ) -> String {
        let head = format!("{}{}", vis_prefix(vis), self.def_id(id));
        match scheme {
            Some(scheme) => format!("{head}: {}", format_scheme(&self.arena.typ, scheme)),
            None => head,
        }
    }

    pub(super) fn write_children(&mut self, children: &[DefId], indent: usize) {
        for child in children {
            self.write_def(*child, indent);
        }
    }

    pub(super) fn write_indent(&mut self, indent: usize) {
        for _ in 0..indent {
            self.out.push_str("  ");
        }
    }

    pub(super) fn expr(&self, id: ExprId) -> String {
        format!("e{}:{}", id.0, self.expr_body(id))
    }

    pub(super) fn expr_body(&self, id: ExprId) -> String {
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

    pub(super) fn pat(&self, id: PatId) -> String {
        format!("p{}:{}", id.0, self.pat_body(id))
    }

    pub(super) fn pat_body(&self, id: PatId) -> String {
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

    pub(super) fn tuple_expr(&self, items: &[ExprId]) -> String {
        match items {
            [] => "()".to_string(),
            [only] => format!("({},)", self.expr(*only)),
            _ => format!("({})", self.join_exprs(items)),
        }
    }

    pub(super) fn tuple_pat(&self, items: &[PatId]) -> String {
        match items {
            [] => "()".to_string(),
            [only] => format!("({},)", self.pat(*only)),
            _ => format!("({})", self.join_pats(items)),
        }
    }

    pub(super) fn list_pat(
        &self,
        prefix: &[PatId],
        spread: Option<PatId>,
        suffix: &[PatId],
    ) -> String {
        let mut parts = prefix.iter().map(|id| self.pat(*id)).collect::<Vec<_>>();
        if let Some(spread) = spread {
            parts.push(format!("..{}", self.pat(spread)));
        }
        parts.extend(suffix.iter().map(|id| self.pat(*id)));
        format!("[{}]", parts.join(", "))
    }

    pub(super) fn record_expr(
        &self,
        fields: &[(String, ExprId)],
        spread: &RecordSpread<ExprId>,
    ) -> String {
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

    pub(super) fn record_pat(
        &self,
        fields: &[RecordPatField],
        spread: &RecordSpread<DefId>,
    ) -> String {
        let mut parts = Vec::new();
        if let RecordSpread::Head(spread) = spread {
            parts.push(format!("..{}", self.def_id(*spread)));
        }
        parts.extend(fields.iter().map(|field| {
            let default = field
                .default
                .map(|default| format!(" = {}", self.expr(default)))
                .unwrap_or_default();
            format!(
                "{}: {}{default}",
                field_name(&field.name),
                self.pat(field.pat)
            )
        }));
        if let RecordSpread::Tail(spread) = spread {
            parts.push(format!("..{}", self.def_id(*spread)));
        }
        format!("{{{}}}", parts.join(", "))
    }

    pub(super) fn poly_variant_expr(&self, name: &str, payloads: &[ExprId]) -> String {
        if payloads.is_empty() {
            format!(":{}", field_name(name))
        } else {
            format!(":{}({})", field_name(name), self.join_exprs(payloads))
        }
    }

    pub(super) fn poly_variant_pat(&self, name: &str, payloads: &[PatId]) -> String {
        if payloads.is_empty() {
            format!(":{}", field_name(name))
        } else {
            format!(":{}({})", field_name(name), self.join_pats(payloads))
        }
    }

    pub(super) fn case_expr(&self, scrutinee: ExprId, arms: &[CaseArm]) -> String {
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

    pub(super) fn catch_expr(&self, body: ExprId, arms: &[CatchArm]) -> String {
        let arms = arms
            .iter()
            .map(|arm| {
                let head = match &arm.operation {
                    Some(operation) => {
                        format!("{} {}", operation.path.join("::"), self.pat(arm.pat))
                    }
                    None => self.pat(arm.pat),
                };
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
                    head,
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

    pub(super) fn block_expr(&self, stmts: &[Stmt], tail: Option<ExprId>) -> String {
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

    pub(super) fn stmt(&self, stmt: &Stmt) -> String {
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

    pub(super) fn join_exprs(&self, ids: &[ExprId]) -> String {
        ids.iter()
            .map(|id| self.expr(*id))
            .collect::<Vec<_>>()
            .join(", ")
    }

    pub(super) fn join_pats(&self, ids: &[PatId]) -> String {
        ids.iter()
            .map(|id| self.pat(*id))
            .collect::<Vec<_>>()
            .join(", ")
    }

    pub(super) fn lit(&self, lit: &Lit) -> String {
        match lit {
            Lit::Int(value) => value.to_string(),
            Lit::BigInt(value) => format!("{value}n"),
            Lit::Float(value) => float_lit(*value),
            Lit::Str(value) => format!("{value:?}"),
            Lit::Bool(value) => value.to_string(),
            Lit::Unit => "()".to_string(),
        }
    }

    pub(super) fn ref_id(&self, id: RefId) -> String {
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

    pub(super) fn select_id(&self, id: SelectId) -> String {
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

    pub(super) fn def_id(&self, id: DefId) -> String {
        self.id_with_label("d", id.0, self.labels.defs.get(&id))
    }

    pub(super) fn id_with_label(
        &self,
        prefix: &str,
        number: u32,
        label: Option<&String>,
    ) -> String {
        match label {
            Some(label) => format!("{prefix}{number}:{}", label_name(label)),
            None => format!("{prefix}{number}"),
        }
    }
}
