use std::fmt::Write as _;

use crate::{
    Block, CatchArm, ComputationType, EffectFamilies, EffectiveThunkType, Expr, ExprKind,
    FunctionAdapterHygiene, GuardMarker, Instance, Lit, Pat, Program, RecordField, RecordSpread,
    Root, SelectResolution, StackWeight, Stmt, Type, TypeField, TypeVariant, Vis,
};

pub fn dump_program(program: &Program) -> String {
    let mut dumper = Dumper { out: String::new() };
    dumper.program(program);
    dumper.out
}

pub fn dump_type(ty: &Type) -> String {
    TypeDumper.ty(ty)
}

struct Dumper {
    out: String,
}

impl Dumper {
    fn program(&mut self, program: &Program) {
        let roots = program
            .roots
            .iter()
            .map(|root| self.root(root))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(self.out, "mono roots [{roots}]");
        for instance in &program.instances {
            self.instance(instance);
        }
    }

    fn root(&self, root: &Root) -> String {
        match root {
            Root::Instance(instance) => format!("m{}", instance.0),
            Root::Expr(expr) => self.expr(expr),
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
            dump_type(&instance.signature.ty)
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
            ExprKind::EffectOp { path } => format!("<effect-op {}>", path.join("::")),
            ExprKind::Local(def) => format!("d{}", def.0),
            ExprKind::InstanceRef(instance) => format!("m{}", instance.0),
            ExprKind::Coerce {
                source,
                target,
                expr,
            } => format!(
                "coerce[{} => {}]({})",
                dump_type(source),
                dump_type(target),
                self.expr(expr)
            ),
            ExprKind::MakeThunk {
                source,
                target,
                body,
            } => format!(
                "make-thunk[{} => {}]({})",
                self.computation_type(source),
                self.effective_thunk_type(target),
                self.expr(body)
            ),
            ExprKind::ForceThunk {
                source,
                target,
                thunk,
            } => format!(
                "force-thunk[{} => {}]({})",
                self.effective_thunk_type(source),
                self.computation_type(target),
                self.expr(thunk)
            ),
            ExprKind::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => format!(
                "adapter[{} => {}; {}]({})",
                dump_type(source),
                dump_type(target),
                self.function_adapter_hygiene(hygiene),
                self.expr(function)
            ),
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
        let head = match &arm.operation_path {
            Some(path) => format!("{} {}", path.join("::"), self.pat(&arm.pat)),
            None => self.pat(&arm.pat),
        };
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
            head,
            continuation,
            guard,
            self.expr(&arm.body)
        )
    }

    fn computation_type(&self, ty: &ComputationType) -> String {
        format!("{} ! {}", dump_type(&ty.value), dump_type(&ty.effect))
    }

    fn effective_thunk_type(&self, ty: &EffectiveThunkType) -> String {
        format!("thunk[{}, {}]", dump_type(&ty.effect), dump_type(&ty.value))
    }

    fn function_adapter_hygiene(&self, hygiene: &FunctionAdapterHygiene) -> String {
        if hygiene.markers.is_empty() {
            return "hygiene[]".to_string();
        }
        let markers = hygiene
            .markers
            .iter()
            .map(|marker| self.guard_marker(marker))
            .collect::<Vec<_>>()
            .join(", ");
        format!("hygiene[{markers}]")
    }

    fn guard_marker(&self, marker: &GuardMarker) -> String {
        format!("add_id[{}, {}]", marker.depth, marker.path.join("::"))
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
            Pat::Con(def, payloads) => {
                let payloads = payloads
                    .iter()
                    .map(|payload| self.pat(payload))
                    .collect::<Vec<_>>()
                    .join(" ");
                if payloads.is_empty() {
                    format!("d{}", def.0)
                } else {
                    format!("d{} {payloads}", def.0)
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

struct TypeDumper;

impl TypeDumper {
    fn ty(&self, ty: &Type) -> String {
        match ty {
            Type::Any => "any".to_string(),
            Type::Never => "never".to_string(),
            Type::Con { path, args } => self.con(path, args),
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => self.fun(arg, arg_effect, ret_effect, ret),
            Type::Thunk { effect, value } => {
                format!("thunk[{}, {}]", self.ty(effect), self.ty(value))
            }
            Type::Record(fields) => self.record_type(fields),
            Type::PolyVariant(variants) => self.variant_type(variants),
            Type::Tuple(items) => self.tuple_type(items),
            Type::EffectRow(items) => self.effect_row(items),
            Type::Stack { inner, weight } => {
                format!("stack({}, {})", self.ty(inner), self.stack_weight(weight))
            }
            Type::Union(left, right) => format!("{} | {}", self.ty(left), self.ty(right)),
            Type::Intersection(left, right) => {
                format!("{} & {}", self.ty(left), self.ty(right))
            }
            Type::OpenVar(id) => format!("'open{id}"),
        }
    }

    fn con(&self, path: &[String], args: &[Type]) -> String {
        let name = path.join("::");
        if args.is_empty() {
            return name;
        }
        let args = args.iter().map(|arg| self.ty(arg)).collect::<Vec<_>>();
        format!("{name}({})", args.join(", "))
    }

    fn fun(&self, arg: &Type, arg_effect: &Type, ret_effect: &Type, ret: &Type) -> String {
        let arg = self.parenthesize_function_arg(arg);
        let ret = self.ty(ret);
        if arg_effect.is_pure_effect() && ret_effect.is_pure_effect() {
            return format!("{arg} -> {ret}");
        }
        format!(
            "{arg} -[{}, {}]-> {ret}",
            self.ty(arg_effect),
            self.ty(ret_effect)
        )
    }

    fn record_type(&self, fields: &[TypeField]) -> String {
        let fields = fields
            .iter()
            .map(|field| {
                let optional = if field.optional { "?" } else { "" };
                format!("{}{}: {}", field.name, optional, self.ty(&field.value))
            })
            .collect::<Vec<_>>();
        format!("{{{}}}", fields.join(", "))
    }

    fn variant_type(&self, variants: &[TypeVariant]) -> String {
        variants
            .iter()
            .map(|variant| {
                if variant.payloads.is_empty() {
                    return format!("'{}", variant.name);
                }
                let payloads = variant
                    .payloads
                    .iter()
                    .map(|payload| self.ty(payload))
                    .collect::<Vec<_>>();
                format!("'{}({})", variant.name, payloads.join(", "))
            })
            .collect::<Vec<_>>()
            .join(" | ")
    }

    fn tuple_type(&self, items: &[Type]) -> String {
        let items = items.iter().map(|item| self.ty(item)).collect::<Vec<_>>();
        format!("({})", items.join(", "))
    }

    fn effect_row(&self, items: &[Type]) -> String {
        if items.is_empty() {
            return "[]".to_string();
        }
        let items = items.iter().map(|item| self.ty(item)).collect::<Vec<_>>();
        format!("[{}]", items.join(", "))
    }

    fn stack_weight(&self, weight: &StackWeight) -> String {
        let entries = weight
            .entries
            .iter()
            .map(|entry| {
                let mut parts = Vec::new();
                if entry.pops > 0 {
                    parts.push(format!("pop({})", entry.pops));
                }
                parts.extend(
                    entry
                        .floor
                        .iter()
                        .map(|families| format!("floor({})", self.effect_families(families))),
                );
                parts.extend(
                    entry
                        .stack
                        .iter()
                        .map(|families| format!("push({})", self.effect_families(families))),
                );
                format!("#{}:{}", entry.id, parts.join("+"))
            })
            .collect::<Vec<_>>();
        format!("@[{}]", entries.join(", "))
    }

    fn effect_families(&self, families: &EffectFamilies) -> String {
        match families {
            EffectFamilies::Empty => "empty".to_string(),
            EffectFamilies::All => "all".to_string(),
            EffectFamilies::AllExcept(items) => {
                format!("all_except({})", self.effect_family_list(items))
            }
            EffectFamilies::Set(items) => self.effect_family_list(items),
        }
    }

    fn effect_family_list(&self, families: &[crate::EffectFamily]) -> String {
        families
            .iter()
            .map(|family| {
                let path = family.path.join("::");
                if family.args.is_empty() {
                    return path;
                }
                let args = family
                    .args
                    .iter()
                    .map(|arg| self.ty(arg))
                    .collect::<Vec<_>>();
                format!("{path}({})", args.join(", "))
            })
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn parenthesize_function_arg(&self, arg: &Type) -> String {
        match arg {
            Type::Fun { .. } => format!("({})", self.ty(arg)),
            _ => self.ty(arg),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ComputationType, EffectiveThunkType, Expr, ExprKind, FunctionAdapterHygiene, GuardMarker,
        Lit, Program, Root, Type,
    };

    use super::{dump_program, dump_type};

    #[test]
    fn dump_boundary_nodes() {
        let program = Program {
            roots: vec![
                Root::Expr(Expr::new(ExprKind::Coerce {
                    source: int_type(),
                    target: Type::Any,
                    expr: Box::new(Expr::new(ExprKind::Lit(Lit::Int(1)))),
                })),
                Root::Expr(Expr::new(ExprKind::MakeThunk {
                    source: ComputationType {
                        effect: parse_effect_type(),
                        value: str_type(),
                    },
                    target: EffectiveThunkType {
                        effect: parse_effect_type(),
                        value: str_type(),
                    },
                    body: Box::new(Expr::new(ExprKind::Lit(Lit::Str("x".to_string())))),
                })),
                Root::Expr(Expr::new(ExprKind::ForceThunk {
                    source: EffectiveThunkType {
                        effect: parse_effect_type(),
                        value: str_type(),
                    },
                    target: ComputationType {
                        effect: parse_effect_type(),
                        value: str_type(),
                    },
                    thunk: Box::new(Expr::new(ExprKind::Local(crate::DefId(0)))),
                })),
                Root::Expr(Expr::new(ExprKind::FunctionAdapter {
                    source: pure_function_type(int_type(), int_type()),
                    target: pure_function_type(Type::Any, Type::Any),
                    function: Box::new(Expr::new(ExprKind::Local(crate::DefId(1)))),
                    hygiene: FunctionAdapterHygiene::default(),
                })),
                Root::Expr(Expr::new(ExprKind::EffectOp {
                    path: vec!["out".to_string(), "say".to_string()],
                })),
            ],
            instances: Vec::new(),
        };

        assert_eq!(
            dump_program(&program),
            concat!(
                "mono roots [",
                "coerce[int => any](1), ",
                "make-thunk[str ! [std::text::parse::parse] => thunk[[std::text::parse::parse], str]](\"x\"), ",
                "force-thunk[thunk[[std::text::parse::parse], str] => str ! [std::text::parse::parse]](d0), ",
                "adapter[int -> int => any -> any; hygiene[]](d1), ",
                "<effect-op out::say>",
                "]\n",
            )
        );
    }

    #[test]
    fn dump_thunk_type() {
        assert_eq!(
            dump_type(&Type::Thunk {
                effect: Box::new(parse_effect_type()),
                value: Box::new(str_type()),
            }),
            "thunk[[std::text::parse::parse], str]"
        );
    }

    #[test]
    fn dump_function_adapter_hygiene_markers() {
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::FunctionAdapter {
                source: pure_function_type(int_type(), int_type()),
                target: pure_function_type(Type::Any, Type::Any),
                function: Box::new(Expr::new(ExprKind::Local(crate::DefId(1)))),
                hygiene: FunctionAdapterHygiene {
                    markers: vec![GuardMarker {
                        path: vec![
                            "std".to_string(),
                            "text".to_string(),
                            "parse".to_string(),
                            "parse".to_string(),
                        ],
                        depth: 1,
                    }],
                },
            }))],
            instances: Vec::new(),
        };

        assert_eq!(
            dump_program(&program),
            concat!(
                "mono roots [",
                "adapter[int -> int => any -> any; hygiene[add_id[1, std::text::parse::parse]]](d1)",
                "]\n",
            )
        );
    }

    fn int_type() -> Type {
        Type::Con {
            path: vec!["int".to_string()],
            args: Vec::new(),
        }
    }

    fn str_type() -> Type {
        Type::Con {
            path: vec!["str".to_string()],
            args: Vec::new(),
        }
    }

    fn parse_effect_type() -> Type {
        Type::EffectRow(vec![Type::Con {
            path: vec![
                "std".to_string(),
                "text".to_string(),
                "parse".to_string(),
                "parse".to_string(),
            ],
            args: Vec::new(),
        }])
    }

    fn pure_function_type(arg: Type, ret: Type) -> Type {
        Type::Fun {
            arg: Box::new(arg),
            arg_effect: Box::new(Type::pure_effect()),
            ret_effect: Box::new(Type::pure_effect()),
            ret: Box::new(ret),
        }
    }
}
