use super::*;

impl<'a> RawDumper<'a> {
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
        include_all_defs: bool,
    ) -> Self {
        Self::new_with_roots_and_exprs(arena, labels, roots, Vec::new(), include_all_defs)
    }

    pub(super) fn new_with_roots_and_exprs(
        arena: &'a Arena,
        labels: &'a DumpLabels,
        roots: Vec<DefId>,
        root_exprs: Vec<ExprId>,
        include_all_defs: bool,
    ) -> Self {
        Self {
            arena,
            labels,
            out: String::new(),
            roots,
            root_exprs,
            include_all_defs,
            extra_defs: std::collections::BTreeSet::new(),
            exprs: std::collections::BTreeSet::new(),
            pats: std::collections::BTreeSet::new(),
        }
    }

    pub(super) fn dump(mut self) -> String {
        let roots = self
            .roots
            .iter()
            .map(|id| self.def_id(*id))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(self.out, "raw roots [{roots}]");
        if !self.root_exprs.is_empty() {
            let root_exprs = self
                .root_exprs
                .iter()
                .map(|id| self.expr_id(*id))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(self.out, "raw root exprs [{root_exprs}]");
        }
        if !self.arena.runtime_roots.is_empty() {
            let runtime_roots = self
                .arena
                .runtime_roots
                .iter()
                .map(|root| self.raw_runtime_root(*root))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(self.out, "raw runtime roots [{runtime_roots}]");
        }
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
        for expr in self.root_exprs.clone() {
            self.mark_expr(expr);
        }
        for root in self.arena.runtime_roots.clone() {
            if let RuntimeRoot::Expr(expr) = root {
                self.mark_expr(expr);
            }
        }
        let _ = writeln!(self.out, "}}");
        self.write_raw_exprs();
        self.write_raw_pats();
        self.out
    }

    pub(super) fn raw_runtime_root(&self, root: RuntimeRoot) -> String {
        match root {
            RuntimeRoot::Expr(expr) => self.expr_id(expr),
            RuntimeRoot::ComputedDef(def) => self.def_id(def),
        }
    }

    pub(super) fn write_raw_def(&mut self, id: DefId) {
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

    pub(super) fn write_raw_exprs(&mut self) {
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

    pub(super) fn write_raw_pats(&mut self) {
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

    pub(super) fn mark_expr(&mut self, id: ExprId) {
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

    pub(super) fn mark_stmt(&mut self, stmt: &Stmt) {
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

    pub(super) fn mark_pat(&mut self, id: PatId) {
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
                for field in fields {
                    self.mark_pat(field.pat);
                    if let Some(default) = field.default {
                        self.mark_expr(default);
                    }
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

    pub(super) fn raw_expr(&self, id: ExprId) -> String {
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
                        let operation = arm
                            .operation
                            .as_ref()
                            .map(|operation| operation.path.join("::"))
                            .unwrap_or_else(|| "value".to_string());
                        let continuation = arm
                            .continuation
                            .map(|continuation| self.pat_id(continuation))
                            .unwrap_or_else(|| "none".to_string());
                        let guard = arm
                            .guard
                            .map(|guard| self.expr_id(guard))
                            .unwrap_or_else(|| "none".to_string());
                        format!(
                            "{{ op: {operation}, pat: {}, k: {continuation}, guard: {guard}, body: {} }}",
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

    pub(super) fn raw_stmt(&self, stmt: &Stmt) -> String {
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

    pub(super) fn raw_pat(&self, id: PatId) -> String {
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
                    .map(|field| {
                        let default = field
                            .default
                            .map(|default| format!(", default: {}", self.expr_id(default)))
                            .unwrap_or_default();
                        format!(
                            "{}: {}{default}",
                            label_name(&field.name),
                            self.pat_id(field.pat)
                        )
                    })
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

    pub(super) fn expr_ids(&self, ids: &[ExprId]) -> String {
        format!(
            "[{}]",
            ids.iter()
                .map(|id| self.expr_id(*id))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    pub(super) fn pat_ids(&self, ids: &[PatId]) -> String {
        format!(
            "[{}]",
            ids.iter()
                .map(|id| self.pat_id(*id))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    pub(super) fn expr_spread(&self, spread: &RecordSpread<ExprId>) -> String {
        match spread {
            RecordSpread::None => "none".to_string(),
            RecordSpread::Head(expr) => format!("head {}", self.expr_id(*expr)),
            RecordSpread::Tail(expr) => format!("tail {}", self.expr_id(*expr)),
        }
    }

    pub(super) fn def_spread(&self, spread: &RecordSpread<DefId>) -> String {
        match spread {
            RecordSpread::None => "none".to_string(),
            RecordSpread::Head(def) => format!("head {}", self.def_id(*def)),
            RecordSpread::Tail(def) => format!("tail {}", self.def_id(*def)),
        }
    }

    pub(super) fn expr_id(&self, id: ExprId) -> String {
        format!("e{}", id.0)
    }

    pub(super) fn pat_id(&self, id: PatId) -> String {
        format!("p{}", id.0)
    }

    pub(super) fn ref_id(&self, id: RefId) -> String {
        Dumper::new(self.arena, self.labels).ref_id(id)
    }

    pub(super) fn select_id(&self, id: SelectId) -> String {
        Dumper::new(self.arena, self.labels).select_id(id)
    }

    pub(super) fn def_id(&self, id: DefId) -> String {
        Dumper::new(self.arena, self.labels).def_id(id)
    }
}
