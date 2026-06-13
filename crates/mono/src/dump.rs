use std::fmt::Write as _;

use crate::{
    Block, CatchArm, Expr, ExprKind, Instance, Lit, Pat, Program, RecordField, RecordSpread,
    SelectResolution, Stmt, Vis,
};

pub fn dump_program(program: &Program) -> String {
    let mut dumper = Dumper { out: String::new() };
    dumper.program(program);
    dumper.out
}

struct Dumper {
    out: String,
}

impl Dumper {
    fn program(&mut self, program: &Program) {
        let roots = program
            .roots
            .iter()
            .map(|root| format!("m{}", root.0))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(self.out, "mono roots [{roots}]");
        for instance in &program.instances {
            self.instance(instance);
        }
    }

    fn instance(&mut self, instance: &Instance) {
        let _ = writeln!(
            self.out,
            "m{} = d{} : {}",
            instance.id.0,
            match instance.source {
                crate::InstanceSource::Def(def) => def.0,
            },
            instance.signature.text
        );
        let body = self.expr(&instance.body);
        let _ = writeln!(self.out, "  {body}");
    }

    fn block(&self, block: &Block) -> String {
        let mut parts = block
            .stmts
            .iter()
            .map(|stmt| self.stmt(stmt))
            .collect::<Vec<_>>();
        if let Some(tail) = &block.tail {
            parts.push(self.expr(tail));
        }
        format!("{{ {} }}", parts.join("; "))
    }

    fn stmt(&self, stmt: &Stmt) -> String {
        match stmt {
            Stmt::Let(vis, pat, value) => {
                format!(
                    "{} {} = {}",
                    self.vis(*vis),
                    self.pat(pat),
                    self.expr(value)
                )
            }
            Stmt::Expr(expr) => self.expr(expr),
            Stmt::Module(def, stmts) => {
                let body = stmts
                    .iter()
                    .map(|stmt| self.stmt(stmt))
                    .collect::<Vec<_>>()
                    .join("; ");
                format!("mod d{} {{ {body} }}", def.0)
            }
        }
    }

    fn expr(&self, expr: &Expr) -> String {
        match &expr.kind {
            ExprKind::Lit(lit) => self.lit(lit),
            ExprKind::PrimitiveOp(name) => format!("<prim {name}>"),
            ExprKind::Local(def) => format!("d{}", def.0),
            ExprKind::InstanceRef(instance) => format!("m{}", instance.0),
            ExprKind::Apply(callee, arg) => {
                format!("({} {})", self.expr(callee), self.expr(arg))
            }
            ExprKind::RefSet(reference, value) => {
                format!("({} := {})", self.expr(reference), self.expr(value))
            }
            ExprKind::Lambda(param, body) => {
                format!("\\{} -> {}", self.pat(param), self.expr(body))
            }
            ExprKind::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.expr(item))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({items})")
            }
            ExprKind::Record { fields, spread } => self.record(fields, spread),
            ExprKind::PolyVariant { tag, payloads } => {
                if payloads.is_empty() {
                    return format!("'{tag}");
                }
                let payloads = payloads
                    .iter()
                    .map(|payload| self.expr(payload))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("'{tag} {payloads}")
            }
            ExprKind::Select {
                base,
                name,
                resolution,
            } => {
                let suffix = match resolution {
                    Some(SelectResolution::RecordField) => "",
                    Some(SelectResolution::Method { .. }) => " <method>",
                    Some(SelectResolution::TypeclassMethod { .. }) => " <role>",
                    None => " <unresolved>",
                };
                format!("{}.{}{suffix}", self.expr(base), name)
            }
            ExprKind::Case { scrutinee, arms } => {
                let arms = arms
                    .iter()
                    .map(|arm| {
                        let guard = arm
                            .guard
                            .as_ref()
                            .map(|guard| format!(" if {}", self.expr(guard)))
                            .unwrap_or_default();
                        format!(
                            "{}{} -> {}",
                            self.pat(&arm.pat),
                            guard,
                            self.expr(&arm.body)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("case {}: {arms}", self.expr(scrutinee))
            }
            ExprKind::Catch { body, arms } => {
                let arms = arms
                    .iter()
                    .map(|arm| self.catch_arm(arm))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("catch {}: {arms}", self.expr(body))
            }
            ExprKind::Block(block) => self.block(block),
        }
    }

    fn record(&self, fields: &[RecordField], spread: &RecordSpread<Box<Expr>>) -> String {
        let mut parts = fields
            .iter()
            .map(|field| format!("{}: {}", field.name, self.expr(&field.value)))
            .collect::<Vec<_>>();
        match spread {
            RecordSpread::Head(expr) => parts.insert(0, format!("..{}", self.expr(expr))),
            RecordSpread::Tail(expr) => parts.push(format!("..{}", self.expr(expr))),
            RecordSpread::None => {}
        }
        format!("{{{}}}", parts.join(", "))
    }

    fn catch_arm(&self, arm: &CatchArm) -> String {
        let continuation = arm
            .continuation
            .as_ref()
            .map(|pat| format!(", {}", self.pat(pat)))
            .unwrap_or_default();
        let guard = arm
            .guard
            .as_ref()
            .map(|guard| format!(" if {}", self.expr(guard)))
            .unwrap_or_default();
        format!(
            "{}{}{} -> {}",
            self.pat(&arm.pat),
            continuation,
            guard,
            self.expr(&arm.body)
        )
    }

    fn pat(&self, pat: &Pat) -> String {
        match pat {
            Pat::Wild => "_".to_string(),
            Pat::Lit(lit) => self.lit(lit),
            Pat::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.pat(item))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({items})")
            }
            Pat::List {
                prefix,
                spread,
                suffix,
            } => {
                let mut items = prefix.iter().map(|item| self.pat(item)).collect::<Vec<_>>();
                if let Some(spread) = spread {
                    items.push(format!("..{}", self.pat(spread)));
                }
                items.extend(suffix.iter().map(|item| self.pat(item)));
                format!("[{}]", items.join(", "))
            }
            Pat::Record { fields, spread } => {
                let mut parts = fields
                    .iter()
                    .map(|(name, pat)| format!("{name}: {}", self.pat(pat)))
                    .collect::<Vec<_>>();
                match spread {
                    RecordSpread::Head(def) => parts.insert(0, format!("..d{}", def.0)),
                    RecordSpread::Tail(def) => parts.push(format!("..d{}", def.0)),
                    RecordSpread::None => {}
                }
                format!("{{{}}}", parts.join(", "))
            }
            Pat::PolyVariant(tag, payloads) => {
                let payloads = payloads
                    .iter()
                    .map(|payload| self.pat(payload))
                    .collect::<Vec<_>>()
                    .join(" ");
                if payloads.is_empty() {
                    format!("'{tag}")
                } else {
                    format!("'{tag} {payloads}")
                }
            }
            Pat::Con(instance, payloads) => {
                let payloads = payloads
                    .iter()
                    .map(|payload| self.pat(payload))
                    .collect::<Vec<_>>()
                    .join(" ");
                if payloads.is_empty() {
                    format!("m{}", instance.0)
                } else {
                    format!("m{} {payloads}", instance.0)
                }
            }
            Pat::Ref(instance) => format!("m{}", instance.0),
            Pat::Var(def) => format!("d{}", def.0),
            Pat::Or(left, right) => format!("({} | {})", self.pat(left), self.pat(right)),
            Pat::As(pat, def) => format!("{} as d{}", self.pat(pat), def.0),
        }
    }

    fn lit(&self, lit: &Lit) -> String {
        match lit {
            Lit::Int(value) => value.to_string(),
            Lit::BigInt(value) => value.to_string(),
            Lit::Float(value) => value.to_string(),
            Lit::Str(value) => format!("{value:?}"),
            Lit::Bool(value) => value.to_string(),
            Lit::Unit => "()".to_string(),
        }
    }

    fn vis(&self, vis: Vis) -> &'static str {
        match vis {
            Vis::Pub => "pub",
            Vis::Our => "our",
            Vis::My => "my",
        }
    }
}
