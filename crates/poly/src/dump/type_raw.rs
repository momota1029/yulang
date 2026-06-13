//! polarity 付き型 arena を ID のまま読むための raw debug dump。
//!
//! `type_format` は surface に近い短い表記を作る。こちらは `PosId` / `NegId` / `NeuId`
//! と stack weight をそのまま残し、どの node に汚れが残ったかを見るための補助である。

use std::collections::{BTreeSet, VecDeque};
use std::fmt::Write as _;

use crate::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicate, Scheme, StackWeight,
    Subtractability, TypeArena, TypeVar,
};

pub fn dump_scheme_raw(arena: &TypeArena, scheme: &Scheme) -> String {
    RawTypeDumper::new(arena).dump_scheme(scheme)
}

pub fn dump_pos_raw(arena: &TypeArena, id: PosId) -> String {
    RawTypeDumper::new(arena).dump_pos(id)
}

pub fn dump_neg_raw(arena: &TypeArena, id: NegId) -> String {
    RawTypeDumper::new(arena).dump_neg(id)
}

pub fn dump_neu_raw(arena: &TypeArena, id: NeuId) -> String {
    RawTypeDumper::new(arena).dump_neu(id)
}

#[derive(Clone, Copy)]
enum TypeRef {
    Pos(PosId),
    Neg(NegId),
    Neu(NeuId),
}

struct RawTypeDumper<'a> {
    arena: &'a TypeArena,
    pos: BTreeSet<u32>,
    neg: BTreeSet<u32>,
    neu: BTreeSet<u32>,
    queue: VecDeque<TypeRef>,
}

impl<'a> RawTypeDumper<'a> {
    fn new(arena: &'a TypeArena) -> Self {
        Self {
            arena,
            pos: BTreeSet::new(),
            neg: BTreeSet::new(),
            neu: BTreeSet::new(),
            queue: VecDeque::new(),
        }
    }

    fn dump_scheme(mut self, scheme: &Scheme) -> String {
        self.mark_pos(scheme.predicate);
        for role in &scheme.role_predicates {
            self.mark_role(role);
        }
        for bound in &scheme.recursive_bounds {
            self.mark_neu(bound.bounds);
        }
        for fact in &scheme.subtracts {
            self.mark_subtractability(&fact.subtractability);
        }

        let mut out = String::new();
        let _ = writeln!(out, "scheme {{");
        let _ = writeln!(out, "  quantifiers: {}", vars(&scheme.quantifiers));
        let _ = writeln!(
            out,
            "  stack_quantifiers: [{}]",
            scheme
                .stack_quantifiers
                .iter()
                .map(|id| format!("#{}", id.0))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let _ = writeln!(out, "  predicate: {}", pos_ref(scheme.predicate));
        if !scheme.role_predicates.is_empty() {
            let _ = writeln!(out, "  roles:");
            for role in &scheme.role_predicates {
                let _ = writeln!(out, "    {}", self.role(role));
            }
        }
        if !scheme.recursive_bounds.is_empty() {
            let _ = writeln!(out, "  recursive_bounds:");
            for bound in &scheme.recursive_bounds {
                let _ = writeln!(out, "    {} = {}", var(bound.var), neu_ref(bound.bounds));
            }
        }
        if !scheme.subtracts.is_empty() {
            let _ = writeln!(out, "  subtracts:");
            for fact in &scheme.subtracts {
                let _ = writeln!(
                    out,
                    "    {}: #{} = {}",
                    var(fact.var),
                    fact.id.0,
                    self.subtractability(&fact.subtractability)
                );
            }
        }
        self.write_types(&mut out, 1);
        let _ = writeln!(out, "}}");
        out
    }

    fn dump_pos(mut self, id: PosId) -> String {
        self.mark_pos(id);
        let mut out = String::new();
        let _ = writeln!(out, "root {}", pos_ref(id));
        self.write_types(&mut out, 0);
        out
    }

    fn dump_neg(mut self, id: NegId) -> String {
        self.mark_neg(id);
        let mut out = String::new();
        let _ = writeln!(out, "root {}", neg_ref(id));
        self.write_types(&mut out, 0);
        out
    }

    fn dump_neu(mut self, id: NeuId) -> String {
        self.mark_neu(id);
        let mut out = String::new();
        let _ = writeln!(out, "root {}", neu_ref(id));
        self.write_types(&mut out, 0);
        out
    }

    fn write_types(&mut self, out: &mut String, indent: usize) {
        self.visit_reachable();
        if self.pos.is_empty() && self.neg.is_empty() && self.neu.is_empty() {
            return;
        }
        write_indent(out, indent);
        let _ = writeln!(out, "types:");
        for id in self.pos.iter().copied() {
            write_indent(out, indent + 1);
            let id = PosId(id);
            let _ = writeln!(out, "{} = {}", pos_ref(id), self.pos_node(id));
        }
        for id in self.neg.iter().copied() {
            write_indent(out, indent + 1);
            let id = NegId(id);
            let _ = writeln!(out, "{} = {}", neg_ref(id), self.neg_node(id));
        }
        for id in self.neu.iter().copied() {
            write_indent(out, indent + 1);
            let id = NeuId(id);
            let _ = writeln!(out, "{} = {}", neu_ref(id), self.neu_node(id));
        }
    }

    fn visit_reachable(&mut self) {
        while let Some(item) = self.queue.pop_front() {
            match item {
                TypeRef::Pos(id) => self.visit_pos(id),
                TypeRef::Neg(id) => self.visit_neg(id),
                TypeRef::Neu(id) => self.visit_neu(id),
            }
        }
    }

    fn visit_pos(&mut self, id: PosId) {
        match self.arena.pos(id) {
            Pos::Bot | Pos::Var(_) => {}
            Pos::Con(_, args) => {
                for arg in args {
                    self.mark_neu(*arg);
                }
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.mark_neg(*arg);
                self.mark_neg(*arg_eff);
                self.mark_pos(*ret_eff);
                self.mark_pos(*ret);
            }
            Pos::Record(fields) => self.mark_pos_fields(fields),
            Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { tail, fields } => {
                self.mark_pos_fields(fields);
                self.mark_pos(*tail);
            }
            Pos::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.mark_pos(*payload);
                    }
                }
            }
            Pos::Tuple(items) | Pos::Row(items) => {
                for item in items {
                    self.mark_pos(*item);
                }
            }
            Pos::Stack { inner, weight } => {
                self.mark_pos(*inner);
                self.mark_stack_weight(weight);
            }
            Pos::NonSubtract(inner, _) => self.mark_pos(*inner),
            Pos::Union(left, right) => {
                self.mark_pos(*left);
                self.mark_pos(*right);
            }
        }
    }

    fn visit_neg(&mut self, id: NegId) {
        match self.arena.neg(id) {
            Neg::Top | Neg::Bot | Neg::Var(_) => {}
            Neg::Con(_, args) => {
                for arg in args {
                    self.mark_neu(*arg);
                }
            }
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.mark_pos(*arg);
                self.mark_pos(*arg_eff);
                self.mark_neg(*ret_eff);
                self.mark_neg(*ret);
            }
            Neg::Record(fields) => self.mark_neg_fields(fields),
            Neg::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.mark_neg(*payload);
                    }
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.mark_neg(*item);
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.mark_neg(*item);
                }
                self.mark_neg(*tail);
            }
            Neg::Stack { inner, weight } => {
                self.mark_neg(*inner);
                self.mark_stack_weight(weight);
            }
            Neg::Intersection(left, right) => {
                self.mark_neg(*left);
                self.mark_neg(*right);
            }
        }
    }

    fn visit_neu(&mut self, id: NeuId) {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                self.mark_pos(*lower);
                self.mark_neg(*upper);
            }
            Neu::Con(_, args) => {
                for arg in args {
                    self.mark_neu(*arg);
                }
            }
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.mark_neu(*arg);
                self.mark_neu(*arg_eff);
                self.mark_neu(*ret_eff);
                self.mark_neu(*ret);
            }
            Neu::Record(fields) => self.mark_neu_fields(fields),
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.mark_neu(*payload);
                    }
                }
            }
            Neu::Tuple(items) => {
                for item in items {
                    self.mark_neu(*item);
                }
            }
        }
    }

    fn pos_node(&self, id: PosId) -> String {
        match self.arena.pos(id) {
            Pos::Bot => "Bot".to_string(),
            Pos::Var(var_id) => format!("Var({})", var(*var_id)),
            Pos::Con(path, args) => format!("Con({}, {})", path_name(path), neu_refs(args)),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => format!(
                "Fun {{ arg: {}, arg_eff: {}, ret_eff: {}, ret: {} }}",
                neg_ref(*arg),
                neg_ref(*arg_eff),
                pos_ref(*ret_eff),
                pos_ref(*ret)
            ),
            Pos::Record(fields) => format!("Record({})", pos_fields(fields)),
            Pos::RecordTailSpread { fields, tail } => {
                format!(
                    "RecordTailSpread({}, tail: {})",
                    pos_fields(fields),
                    pos_ref(*tail)
                )
            }
            Pos::RecordHeadSpread { tail, fields } => {
                format!(
                    "RecordHeadSpread(tail: {}, {})",
                    pos_ref(*tail),
                    pos_fields(fields)
                )
            }
            Pos::PolyVariant(items) => format!("PolyVariant({})", pos_variants(items)),
            Pos::Tuple(items) => format!("Tuple({})", pos_refs(items)),
            Pos::Row(items) => format!("Row({})", pos_refs(items)),
            Pos::Stack { inner, weight } => {
                format!(
                    "Stack {{ inner: {}, weight: {} }}",
                    pos_ref(*inner),
                    self.stack_weight(weight)
                )
            }
            Pos::NonSubtract(inner, id) => {
                format!("NonSubtract({}, #{})", pos_ref(*inner), id.0)
            }
            Pos::Union(left, right) => format!("Union({}, {})", pos_ref(*left), pos_ref(*right)),
        }
    }

    fn neg_node(&self, id: NegId) -> String {
        match self.arena.neg(id) {
            Neg::Top => "Top".to_string(),
            Neg::Bot => "Bot".to_string(),
            Neg::Var(var_id) => format!("Var({})", var(*var_id)),
            Neg::Con(path, args) => format!("Con({}, {})", path_name(path), neu_refs(args)),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => format!(
                "Fun {{ arg: {}, arg_eff: {}, ret_eff: {}, ret: {} }}",
                pos_ref(*arg),
                pos_ref(*arg_eff),
                neg_ref(*ret_eff),
                neg_ref(*ret)
            ),
            Neg::Record(fields) => format!("Record({})", neg_fields(fields)),
            Neg::PolyVariant(items) => format!("PolyVariant({})", neg_variants(items)),
            Neg::Tuple(items) => format!("Tuple({})", neg_refs(items)),
            Neg::Row(items, tail) => format!("Row({}, tail: {})", neg_refs(items), neg_ref(*tail)),
            Neg::Stack { inner, weight } => {
                format!(
                    "Stack {{ inner: {}, weight: {} }}",
                    neg_ref(*inner),
                    self.stack_weight(weight)
                )
            }
            Neg::Intersection(left, right) => {
                format!("Intersection({}, {})", neg_ref(*left), neg_ref(*right))
            }
        }
    }

    fn neu_node(&self, id: NeuId) -> String {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                format!("Bounds({}, {})", pos_ref(*lower), neg_ref(*upper))
            }
            Neu::Con(path, args) => format!("Con({}, {})", path_name(path), neu_refs(args)),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => format!(
                "Fun {{ arg: {}, arg_eff: {}, ret_eff: {}, ret: {} }}",
                neu_ref(*arg),
                neu_ref(*arg_eff),
                neu_ref(*ret_eff),
                neu_ref(*ret)
            ),
            Neu::Record(fields) => format!("Record({})", neu_fields(fields)),
            Neu::PolyVariant(items) => format!("PolyVariant({})", neu_variants(items)),
            Neu::Tuple(items) => format!("Tuple({})", neu_refs(items)),
        }
    }

    fn role(&self, role: &RolePredicate) -> String {
        let associated = role
            .associated
            .iter()
            .map(|associated| format!("{} = {}", associated.name, neu_ref(associated.value)))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "{} inputs: {}, associated: [{}]",
            path_name(&role.role),
            neu_refs(&role.inputs),
            associated
        )
    }

    fn stack_weight(&self, weight: &StackWeight) -> String {
        if weight.entries().is_empty() {
            return "{}".to_string();
        }
        let entries = weight
            .entries()
            .iter()
            .map(|entry| {
                let floor = entry
                    .floor
                    .iter()
                    .map(|item| self.subtractability(item))
                    .collect::<Vec<_>>()
                    .join(", ");
                let stack = entry
                    .stack
                    .iter()
                    .map(|item| self.subtractability(item))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "#{} -> floor: [{floor}], pops: {}, stack: [{stack}]",
                    entry.id.0, entry.pops
                )
            })
            .collect::<Vec<_>>()
            .join("; ");
        format!("{{ {entries} }}")
    }

    fn subtractability(&self, subtractability: &Subtractability) -> String {
        match subtractability {
            Subtractability::Empty => "Empty".to_string(),
            Subtractability::All => "All".to_string(),
            Subtractability::AllExcept(path, args) => {
                format!("AllExcept({}, {})", path_name(path), neu_refs(args))
            }
            Subtractability::AllExceptMany(families) => {
                format!("AllExceptMany({})", self.families(families))
            }
            Subtractability::Set(path, args) => {
                format!("Set({}, {})", path_name(path), neu_refs(args))
            }
            Subtractability::SetMany(families) => format!("SetMany({})", self.families(families)),
        }
    }

    fn families(&self, families: &[(Vec<String>, Vec<NeuId>)]) -> String {
        let families = families
            .iter()
            .map(|(path, args)| format!("({}, {})", path_name(path), neu_refs(args)))
            .collect::<Vec<_>>()
            .join(", ");
        format!("[{families}]")
    }

    fn mark_pos_fields(&mut self, fields: &[RecordField<PosId>]) {
        for field in fields {
            self.mark_pos(field.value);
        }
    }

    fn mark_neg_fields(&mut self, fields: &[RecordField<NegId>]) {
        for field in fields {
            self.mark_neg(field.value);
        }
    }

    fn mark_neu_fields(&mut self, fields: &[RecordField<NeuId>]) {
        for field in fields {
            self.mark_neu(field.value);
        }
    }

    fn mark_role(&mut self, role: &RolePredicate) {
        for input in &role.inputs {
            self.mark_neu(*input);
        }
        for associated in &role.associated {
            self.mark_neu(associated.value);
        }
    }

    fn mark_stack_weight(&mut self, weight: &StackWeight) {
        for entry in weight.entries() {
            for subtractability in entry.floor.iter().chain(entry.stack.iter()) {
                self.mark_subtractability(subtractability);
            }
        }
    }

    fn mark_subtractability(&mut self, subtractability: &Subtractability) {
        match subtractability {
            Subtractability::Empty | Subtractability::All => {}
            Subtractability::AllExcept(_, args) | Subtractability::Set(_, args) => {
                for arg in args {
                    self.mark_neu(*arg);
                }
            }
            Subtractability::AllExceptMany(families) | Subtractability::SetMany(families) => {
                for (_, args) in families {
                    for arg in args {
                        self.mark_neu(*arg);
                    }
                }
            }
        }
    }

    fn mark_pos(&mut self, id: PosId) {
        if self.pos.insert(id.0) {
            self.queue.push_back(TypeRef::Pos(id));
        }
    }

    fn mark_neg(&mut self, id: NegId) {
        if self.neg.insert(id.0) {
            self.queue.push_back(TypeRef::Neg(id));
        }
    }

    fn mark_neu(&mut self, id: NeuId) {
        if self.neu.insert(id.0) {
            self.queue.push_back(TypeRef::Neu(id));
        }
    }
}

fn pos_fields(fields: &[RecordField<PosId>]) -> String {
    fields
        .iter()
        .map(|field| {
            format!(
                "{}{}: {}",
                field.name,
                optional(field.optional),
                pos_ref(field.value)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn neg_fields(fields: &[RecordField<NegId>]) -> String {
    fields
        .iter()
        .map(|field| {
            format!(
                "{}{}: {}",
                field.name,
                optional(field.optional),
                neg_ref(field.value)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn neu_fields(fields: &[RecordField<NeuId>]) -> String {
    fields
        .iter()
        .map(|field| {
            format!(
                "{}{}: {}",
                field.name,
                optional(field.optional),
                neu_ref(field.value)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn pos_variants(items: &[(String, Vec<PosId>)]) -> String {
    variants(items, pos_refs)
}

fn neg_variants(items: &[(String, Vec<NegId>)]) -> String {
    variants(items, neg_refs)
}

fn neu_variants(items: &[(String, Vec<NeuId>)]) -> String {
    variants(items, neu_refs)
}

fn variants<Id>(items: &[(String, Vec<Id>)], ids: impl Fn(&[Id]) -> String) -> String {
    items
        .iter()
        .map(|(name, payloads)| format!("{}{}", name, ids(payloads)))
        .collect::<Vec<_>>()
        .join(", ")
}

fn pos_refs(items: &[PosId]) -> String {
    refs(items.iter().map(|id| pos_ref(*id)))
}

fn neg_refs(items: &[NegId]) -> String {
    refs(items.iter().map(|id| neg_ref(*id)))
}

fn neu_refs(items: &[NeuId]) -> String {
    refs(items.iter().map(|id| neu_ref(*id)))
}

fn refs(items: impl Iterator<Item = String>) -> String {
    format!("[{}]", items.collect::<Vec<_>>().join(", "))
}

fn pos_ref(id: PosId) -> String {
    format!("p{}", id.0)
}

fn neg_ref(id: NegId) -> String {
    format!("n{}", id.0)
}

fn neu_ref(id: NeuId) -> String {
    format!("u{}", id.0)
}

fn vars(vars: &[TypeVar]) -> String {
    refs(vars.iter().map(|id| var(*id)))
}

fn var(id: TypeVar) -> String {
    format!("'{}", id.0)
}

fn optional(optional: bool) -> &'static str {
    if optional { "?" } else { "" }
}

fn path_name(path: &[String]) -> String {
    if path.is_empty() {
        "<root>".to_string()
    } else {
        path.join("::")
    }
}

fn write_indent(out: &mut String, indent: usize) {
    for _ in 0..indent {
        out.push_str("  ");
    }
}
