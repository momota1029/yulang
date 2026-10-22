//! Lossless, borrowed candidate graph projection, before any display choices.
//! This is an experimental observation, not a generalized or accepted scheme.
use crate::output::{Output, cap};
use crate::render::OUTPUT_CAP;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use yu_solver::shadow_apply::{
    CandidateGraphBound, CandidateGraphEffectOperand, CandidateGraphExport,
    CandidateGraphFormalEffectPermission, CandidateGraphFormalPortStep, CandidateGraphLeaf,
    CandidateGraphNode, CandidateGraphRow,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NodeId(usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct RowId(usize);

struct Row<'a> {
    source: CandidateGraphRow<'a>,
    // The first exported coordinate is stable even when canonical rows alias.
    coordinate: usize,
}
struct Node<'a> {
    // Retains polarity and exact graph identity, including distinct equal leaves.
    source: CandidateGraphNode<'a>,
    kind: NodeKind<'a>,
}
enum NodeKind<'a> {
    Leaf(CandidateGraphLeaf),
    Row(RowId),
    Function([NodeId; 4]),
    Tuple(Vec<NodeId>),
    Record(Vec<(Box<str>, NodeId)>),
    Effect(Effect<'a>),
}
struct Effect<'a> {
    // Keep the complete typed variant: origin, owner, position, declaration,
    // occurrence, member, labels, route and instance are never stringified here.
    source: CandidateGraphEffectOperand<'a>,
    tail: Option<RowId>,
}
struct Constraint<'a> {
    source: CandidateGraphBound<'a>,
    lower: NodeId,
    upper: NodeId,
}
struct Permission<'a> {
    source: CandidateGraphFormalEffectPermission<'a>,
    tail: RowId,
}

pub(crate) struct CandidatePublicScheme<'a> {
    rows: Vec<Row<'a>>,
    nodes: Vec<Node<'a>>,
    root: NodeId,
    constraints: Vec<Constraint<'a>>,
    permissions: Vec<Permission<'a>>,
}

fn missing(what: &str) -> String {
    format!("candidate scheme {what} identity unavailable")
}
fn bounded(count: usize, what: &str) -> Result<(), String> {
    if count > OUTPUT_CAP {
        Err(format!(
            "tool output cap exceeded: more than {OUTPUT_CAP} {what}"
        ))
    } else {
        Ok(())
    }
}

impl<'a> CandidatePublicScheme<'a> {
    pub(crate) fn project(graph: &CandidateGraphExport<'a>) -> Result<Self, String> {
        let mut budget = Output::new();
        let mut rows: Vec<Row<'a>> = Vec::new();
        let mut row_ids = HashMap::new();
        for (coordinate, source) in graph.rows().enumerate() {
            budget.observe(1)?;
            bounded(coordinate + 1, "rows")?;
            if let Some(&RowId(index)) = row_ids.get(&source) {
                // Locality conflicts must not turn an outer anchor into a binder.
                if rows[index].source.kind() != source.kind()
                    || rows[index].source.is_local() != source.is_local()
                {
                    return Err("candidate scheme aliased rows disagree on kind or locality".into());
                }
            } else {
                row_ids.insert(source, RowId(rows.len()));
                rows.push(Row { source, coordinate });
            }
        }
        let row_id = |row| row_ids.get(&row).copied().ok_or_else(|| missing("row"));
        let effect_tail = |node: CandidateGraphNode<'a>| {
            let row = node.row().ok_or_else(|| missing("effect tail row"))?;
            if !row.is_effect() {
                return Err("effect operand tail has Value row kind".into());
            }
            row_id(row)
        };
        bounded(graph.node_count(), "nodes")?;
        budget.observe(graph.node_count())?;
        // Assign all nodes before resolving edges: forward references and cycles
        // do not cause recursion or a second identity allocation.
        let sources: Vec<_> = graph.nodes().collect();
        let node_ids: HashMap<_, _> = sources
            .iter()
            .copied()
            .enumerate()
            .map(|(index, source)| (source, NodeId(index)))
            .collect();
        let node_id = |node| node_ids.get(&node).copied().ok_or_else(|| missing("node"));
        let root = node_id(graph.root())?;
        let mut nodes = Vec::with_capacity(sources.len());
        for source in sources {
            let kind = if let Some(leaf) = source.leaf() {
                NodeKind::Leaf(leaf)
            } else if let Some(row) = source.row() {
                NodeKind::Row(row_id(row)?)
            } else if let Some(children) = source.children() {
                budget.observe(4)?;
                let [a, ae, re, r] = children;
                NodeKind::Function([node_id(a)?, node_id(ae)?, node_id(re)?, node_id(r)?])
            } else if let Some(fields) = source.record_fields() {
                budget.observe(fields.len())?;
                bounded(fields.len(), "record fields")?;
                NodeKind::Record(fields.map(|(label, child)| Ok((label.into(), node_id(child)?))).collect::<Result<_, String>>()?)
            } else if let Some(children) = source.tuple_children() {
                budget.observe(children.len())?;
                bounded(children.len(), "tuple elements")?;
                NodeKind::Tuple(children.map(node_id).collect::<Result<_, _>>()?)
            } else if let Some(operand) = source.effect_operand() {
                let (tail, permitted) = match operand {
                    CandidateGraphEffectOperand::Contribution { .. } => (None, 0),
                    CandidateGraphEffectOperand::AnnotationMember {
                        tail, permitted, ..
                    }
                    | CandidateGraphEffectOperand::OperationInterfaceMember {
                        tail,
                        permitted,
                        ..
                    }
                    | CandidateGraphEffectOperand::PermissionView {
                        tail, permitted, ..
                    }
                    | CandidateGraphEffectOperand::SupportView {
                        tail, permitted, ..
                    } => (tail, permitted.len()),
                };
                budget.observe(permitted + usize::from(tail.is_some()))?;
                // Validate the tail's node as well as its canonical row.
                if let Some(tail) = tail {
                    node_id(tail)?;
                }
                NodeKind::Effect(Effect {
                    source: operand,
                    tail: tail.map(effect_tail).transpose()?,
                })
            } else {
                return Err("candidate scheme contains an unsupported graph node".into());
            };
            nodes.push(Node { source, kind });
        }
        let mut constraints = Vec::new();
        for bound in graph.bounds() {
            budget.observe(1)?;
            bounded(constraints.len() + 1, "bounds")?;
            constraints.push(Constraint {
                lower: node_id(bound.lower())?,
                upper: node_id(bound.upper())?,
                source: bound,
            });
        }
        let mut permissions = Vec::new();
        for source in graph
            .formal_effect_permissions()
            .map_err(|_| "candidate scheme permission projection unavailable".to_owned())?
        {
            budget.observe(1 + source.path().len() + source.permitted().len())?;
            if source.path().is_empty() {
                return Err("candidate scheme permission path is empty".into());
            }
            node_id(source.open_tail())?;
            let tail = effect_tail(source.open_tail())?;
            permissions.push(Permission { source, tail });
        }
        Ok(Self {
            rows,
            nodes,
            root,
            constraints,
            permissions,
        })
    }

    fn row_name(&self, row: RowId, output: &mut Output) -> Result<(), String> {
        let row = &self.rows[row.0];
        let prefix = if row.source.is_effect() { "ε" } else { "α" };
        write!(output, "{prefix}{}", row.coordinate).map_err(cap)
    }

    /// Concrete heads are a display abbreviation only. All row references and
    /// both polarities remain in the typed carrier and every constraint is kept.
    fn heads(&self) -> Result<Vec<Option<NodeId>>, String> {
        let mut heads: Vec<Option<NodeId>> = vec![None; self.rows.len()];
        for bound in &self.constraints {
            let NodeKind::Row(row) = self.nodes[bound.upper.0].kind else {
                continue;
            };
            if self.rows[row.0].source.is_effect()
                || bound.source.kind() != self.rows[row.0].source.kind()
                || matches!(self.nodes[bound.lower.0].kind, NodeKind::Row(_))
            {
                continue;
            }
            if let Some(first) = heads[row.0] {
                if !self.nodes[first.0]
                    .source
                    .same_identity(self.nodes[bound.lower.0].source)
                {
                    return Err(
                        "candidate scheme has multiple concrete Value shapes for one row".into(),
                    );
                }
            }
            heads[row.0] = Some(bound.lower);
        }
        Ok(heads)
    }

    pub(crate) fn render(&self, name: &str) -> Result<String, String> {
        let heads = self.heads()?;
        let mut free = HashSet::new();
        let mut body = Output::new();
        self.render_node(self.root, true, &heads, &mut free, &mut body)?;
        body.write_char('\n').map_err(cap)?;
        let body = body.finish()?;
        let mut details = Output::new();
        for permission in &self.permissions {
            details.observe(1)?;
            details
                .write_str("  open formal effect permission ")
                .map_err(cap)?;
            for (index, step) in permission.source.path().iter().enumerate() {
                details.observe(1)?;
                if index != 0 {
                    details.write_char('/').map_err(cap)?;
                }
                match step {
                    CandidateGraphFormalPortStep::Argument => details.write_str("argument").map_err(cap)?,
                    CandidateGraphFormalPortStep::Result => details.write_str("result").map_err(cap)?,
                    CandidateGraphFormalPortStep::Element(element) => write!(details, "element[{element}]").map_err(cap)?,
                }
            }
            details.write_str(" permits [").map_err(cap)?;
            permitted(&mut details, permission.source.permitted())?;
            self.render_tail(Some(permission.tail), true, &mut free, &mut details)?;
        }
        for node in &self.nodes {
            let NodeKind::Effect(effect) = &node.kind else {
                continue;
            };
            details.observe(1)?;
            match effect.source {
                CandidateGraphEffectOperand::Contribution {
                    effect,
                    route,
                    instance,
                } => {
                    writeln!(
                        details,
                        "  effect label {effect:?} from {route:?} instance {instance}"
                    )
                    .map_err(cap)?;
                    continue;
                }
                CandidateGraphEffectOperand::AnnotationMember {
                    effect, position, ..
                } => write!(
                    details,
                    "  effect label {effect:?} at annotation {position:?} permits ["
                )
                .map_err(cap)?,
                CandidateGraphEffectOperand::OperationInterfaceMember {
                    effect,
                    occurrence,
                    ..
                } => write!(
                    details,
                    "  effect label {effect:?} at operation use {occurrence:?} permits ["
                )
                .map_err(cap)?,
                CandidateGraphEffectOperand::PermissionView { position, .. }
                | CandidateGraphEffectOperand::SupportView { position, .. } => {
                    write!(details, "  effect view at {position:?} permits [").map_err(cap)?
                }
            }
            permitted(&mut details, effect.permitted())?;
            self.render_tail(effect.tail, true, &mut free, &mut details)?;
        }
        for bound in &self.constraints {
            details.observe(1)?;
            write!(details, "  retained {:?} bound ", bound.source.kind()).map_err(cap)?;
            self.render_node(bound.lower, false, &heads, &mut free, &mut details)?;
            details.write_str(" ⊆ ").map_err(cap)?;
            self.render_node(bound.upper, false, &heads, &mut free, &mut details)?;
            details.write_char('\n').map_err(cap)?;
        }
        let details = details.finish()?;
        let mut output = Output::new();
        write!(output, "{name}: ").map_err(cap)?;
        let mut first = true;
        for (index, row) in self.rows.iter().enumerate() {
            if !row.source.is_local() || !free.contains(&RowId(index)) {
                continue;
            }
            output
                .write_str(if first { "∀ " } else { " " })
                .map_err(cap)?;
            first = false;
            self.row_name(RowId(index), &mut output)?;
        }
        if !first {
            output.write_str(". ").map_err(cap)?;
        }
        output.write_str(&body).map_err(cap)?;
        for (index, row) in self.rows.iter().enumerate() {
            if row.source.is_local() || !free.contains(&RowId(index)) {
                continue;
            }
            write!(output, "  shared {:?} anchor ", row.source.kind()).map_err(cap)?;
            self.row_name(RowId(index), &mut output)?;
            output
                .write_str(" (bounds owned by outer context)\n")
                .map_err(cap)?;
        }
        output.write_str(&details).map_err(cap)?;
        output.finish()
    }

    fn render_tail(
        &self,
        tail: Option<RowId>,
        summary: bool,
        free: &mut HashSet<RowId>,
        output: &mut Output,
    ) -> Result<(), String> {
        if let Some(row) = tail {
            free.insert(row);
            output
                .write_str(if summary { ", " } else { "open-tail=" })
                .map_err(cap)?;
            self.row_name(row, output)?;
            if summary {
                output.write_str("] (open)\n").map_err(cap)?;
            }
        } else {
            output
                .write_str(if summary {
                    "] (closed view)\n"
                } else {
                    "closed-view"
                })
                .map_err(cap)?;
        }
        Ok(())
    }

    fn render_node(
        &self,
        root: NodeId,
        shape: bool,
        heads: &[Option<NodeId>],
        free: &mut HashSet<RowId>,
        output: &mut Output,
    ) -> Result<(), String> {
        enum Step<'a> {
            Node(NodeId),
            Text(&'a str),
            Leave(RowId),
        }
        let mut stack = vec![Step::Node(root)];
        let mut active = HashSet::new();
        while let Some(step) = stack.pop() {
            output.observe(1)?;
            match step {
                Step::Text(text) => output.write_str(text).map_err(cap)?,
                Step::Leave(row) => {
                    active.remove(&row);
                }
                Step::Node(id) => match &self.nodes[id.0].kind {
                    NodeKind::Leaf(leaf) => {
                        if shape {
                            output.write_str(leaf_name(*leaf)).map_err(cap)?;
                        } else {
                            write!(output, "{leaf:?}").map_err(cap)?;
                        }
                    }
                    NodeKind::Row(row) => {
                        if !self.rows[row.0].source.is_effect()
                            && let Some(head) = heads[row.0]
                        {
                            if !shape {
                                write!(output, "r{}", self.rows[row.0].coordinate).map_err(cap)?;
                                continue;
                            }
                            if active.insert(*row) {
                                stack.push(Step::Leave(*row));
                                stack.push(Step::Node(head));
                                continue;
                            }
                        }
                        free.insert(*row);
                        self.row_name(*row, output)?;
                    }
                    NodeKind::Function(children) => {
                        output.write_str("Function(").map_err(cap)?;
                        stack.push(Step::Text(")"));
                        for (child, label) in children
                            .iter()
                            .zip([
                                "argument=",
                                ", argument-effect=",
                                ", result-effect=",
                                ", result=",
                            ])
                            .rev()
                        {
                            stack.push(Step::Node(*child));
                            stack.push(Step::Text(label));
                        }
                    }
                    NodeKind::Record(fields) => {
                        output.observe(fields.len())?;
                        output.write_char('{').map_err(cap)?;
                        stack.push(Step::Text("}"));
                        for (index, (label, child)) in fields.iter().enumerate().rev() {
                            stack.push(Step::Node(*child));
                            stack.push(Step::Text(": "));
                            stack.push(Step::Text(label));
                            if index != 0 { stack.push(Step::Text(", ")); }
                        }
                    }
                    NodeKind::Tuple(children) => {
                        output.observe(children.len())?;
                        output.write_char('(').map_err(cap)?;
                        stack.push(Step::Text(")"));
                        for (index, child) in children.iter().enumerate().rev() {
                            stack.push(Step::Node(*child));
                            if index != 0 {
                                stack.push(Step::Text(", "));
                            }
                        }
                    }
                    NodeKind::Effect(effect) => {
                        if shape {
                            return Err("candidate scheme contains an unsupported type node".into());
                        }
                        self.render_effect(effect, free, output)?;
                    }
                },
            }
            bounded(stack.len(), "pending display steps")?;
        }
        Ok(())
    }

    fn render_effect(
        &self,
        operand: &Effect<'a>,
        free: &mut HashSet<RowId>,
        output: &mut Output,
    ) -> Result<(), String> {
        match operand.source {
            CandidateGraphEffectOperand::Contribution {
                effect,
                route,
                instance,
            } => {
                return write!(
                    output,
                    "effect({effect:?}, route={route:?}, instance={instance})"
                )
                .map_err(cap);
            }
            CandidateGraphEffectOperand::AnnotationMember {
                position,
                member,
                effect,
                ..
            } => write!(
                output,
                "annotation-effect({effect:?}, position={position:?}, member={member}, permits=["
            )
            .map_err(cap)?,
            CandidateGraphEffectOperand::OperationInterfaceMember {
                occurrence,
                member,
                effect,
                ..
            } => write!(
                output,
                "operation-effect({effect:?}, occurrence={occurrence:?}, member={member}, permits=["
            )
            .map_err(cap)?,
            CandidateGraphEffectOperand::PermissionView { position, .. } => {
                write!(output, "permission-view(position={position:?}, permits=[").map_err(cap)?
            }
            CandidateGraphEffectOperand::SupportView { position, .. } => {
                write!(output, "support-view(position={position:?}, permits=[").map_err(cap)?
            }
        }
        permitted(output, operand.permitted())?;
        output.write_str("], ").map_err(cap)?;
        self.render_tail(operand.tail, false, free, output)
    }
}

impl Effect<'_> {
    fn permitted(&self) -> &[yu_hir::shadow::SourceEffectId] {
        match self.source {
            CandidateGraphEffectOperand::Contribution { .. } => &[],
            CandidateGraphEffectOperand::AnnotationMember { permitted, .. }
            | CandidateGraphEffectOperand::OperationInterfaceMember { permitted, .. }
            | CandidateGraphEffectOperand::PermissionView { permitted, .. }
            | CandidateGraphEffectOperand::SupportView { permitted, .. } => permitted,
        }
    }
}
fn permitted(
    output: &mut Output,
    effects: &[yu_hir::shadow::SourceEffectId],
) -> Result<(), String> {
    for (index, effect) in effects.iter().enumerate() {
        output.observe(1)?;
        if index != 0 {
            output.write_str(", ").map_err(cap)?;
        }
        write!(output, "{effect:?}").map_err(cap)?;
    }
    Ok(())
}
fn leaf_name(leaf: CandidateGraphLeaf) -> &'static str {
    use CandidateGraphLeaf::*;
    match leaf {
        IntPositive | IntNegative => "int",
        UnitPositive | UnitNegative => "unit",
        BoolPositive | BoolNegative => "bool",
        StrPositive | StrNegative => "str",
        Bottom | NegativeBottom => "⊥",
        Top => "⊤",
        EffectBottom => "∅+",
        EmptyEffect => "∅−",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yu_hir::{DefinitionRootId, HirItem, HirModule};
    use yu_solver::Polarity;

    fn root(hir: &HirModule, name: &str) -> DefinitionRootId {
        hir.items()
            .iter()
            .find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == name => {
                    Some(binding.definition_root().clone())
                }
                _ => None,
            })
            .unwrap()
    }

    // Check the whole graph relation, including nodes outside the displayed body.
    fn assert_correspondence(graph: &CandidateGraphExport<'_>, scheme: &CandidatePublicScheme<'_>) {
        assert_eq!(scheme.nodes.len(), graph.node_count());
        assert!(
            scheme.nodes[scheme.root.0]
                .source
                .same_identity(graph.root())
        );
        for (source, node) in graph.nodes().zip(&scheme.nodes) {
            assert!(source.same_identity(node.source));
            assert_eq!(source.polarity(), node.source.polarity());
            match &node.kind {
                NodeKind::Leaf(leaf) => assert_eq!(Some(*leaf), source.leaf()),
                NodeKind::Row(row) => assert!(
                    scheme.rows[row.0]
                        .source
                        .same_identity(source.row().unwrap())
                ),
                NodeKind::Function(children) => {
                    for (source, child) in source.children().unwrap().into_iter().zip(children) {
                        assert!(source.same_identity(scheme.nodes[child.0].source));
                    }
                }
                NodeKind::Record(fields) => {
                    let sources = source.record_fields().unwrap();
                    assert_eq!(sources.len(), fields.len());
                    for ((source_label, source), (label, child)) in sources.zip(fields) {
                        assert_eq!(source_label, label.as_ref());
                        assert!(source.same_identity(scheme.nodes[child.0].source));
                    }
                }
                NodeKind::Tuple(children) => {
                    let sources = source.tuple_children().unwrap();
                    assert_eq!(sources.len(), children.len());
                    for (source, child) in sources.zip(children) {
                        assert!(source.same_identity(scheme.nodes[child.0].source));
                    }
                }
                NodeKind::Effect(effect) => {
                    let original = source.effect_operand().unwrap();
                    assert_eq!(
                        std::mem::discriminant(&original),
                        std::mem::discriminant(&effect.source)
                    );
                    let tail = match original {
                        CandidateGraphEffectOperand::Contribution {
                            effect: label,
                            route,
                            instance,
                        } => {
                            let CandidateGraphEffectOperand::Contribution {
                                effect: retained,
                                route: retained_route,
                                instance: retained_instance,
                            } = effect.source
                            else {
                                panic!("lost contribution")
                            };
                            assert!(std::ptr::eq(label, retained));
                            assert!(std::ptr::eq(route, retained_route));
                            assert_eq!(instance, retained_instance);
                            None
                        }
                        CandidateGraphEffectOperand::AnnotationMember {
                            tail, permitted, ..
                        }
                        | CandidateGraphEffectOperand::OperationInterfaceMember {
                            tail,
                            permitted,
                            ..
                        }
                        | CandidateGraphEffectOperand::PermissionView {
                            tail, permitted, ..
                        }
                        | CandidateGraphEffectOperand::SupportView {
                            tail, permitted, ..
                        } => {
                            assert!(std::ptr::eq(permitted, effect.permitted()));
                            tail
                        }
                    };
                    assert_eq!(tail.is_some(), effect.tail.is_some());
                    if let (Some(source), Some(row)) = (tail, effect.tail) {
                        assert!(
                            scheme.rows[row.0]
                                .source
                                .same_identity(source.row().unwrap())
                        );
                        assert!(scheme.rows[row.0].source.is_effect());
                    }
                }
            }
        }
        assert_eq!(scheme.constraints.len(), graph.bounds().count());
        for (source, bound) in graph.bounds().zip(&scheme.constraints) {
            assert_eq!(source.kind(), bound.source.kind());
            assert!(
                source
                    .lower()
                    .same_identity(scheme.nodes[bound.lower.0].source)
            );
            assert!(
                source
                    .upper()
                    .same_identity(scheme.nodes[bound.upper.0].source)
            );
        }
        let permissions = graph.formal_effect_permissions().unwrap();
        assert_eq!(permissions.len(), scheme.permissions.len());
        for (source, permission) in permissions.iter().zip(&scheme.permissions) {
            assert_eq!(source.occurrence(), permission.source.occurrence());
            assert_eq!(source.source_row(), permission.source.source_row());
            assert_eq!(source.path(), permission.source.path());
            assert_eq!(source.permitted(), permission.source.permitted());
            assert!(
                source
                    .open_tail()
                    .row()
                    .unwrap()
                    .same_identity(scheme.rows[permission.tail.0].source)
            );
        }
        let exported: HashSet<_> = graph.rows().collect();
        assert_eq!(exported.len(), scheme.rows.len());
        for row in &scheme.rows {
            assert!(exported.contains(&row.source));
        }
    }

    #[test]
    fn record_projection_preserves_every_label_child_and_shared_row() {
        let (hir, candidate) = crate::prepare("pub make x = { first: x, nested: { again: x }, empty: {} }; pub main = make 3", "record-types.yu", false).unwrap();
        for name in ["make", "main"] {
            let graph = candidate.export(&root(&hir, name)).unwrap();
            let scheme = CandidatePublicScheme::project(&graph).unwrap();
            assert_correspondence(&graph, &scheme);
            assert!(scheme.nodes.iter().any(|node| matches!(&node.kind, NodeKind::Record(fields) if fields.is_empty())));
        }
    }

    #[test]
    fn unchanged_types_preserve_graph_and_shared_polar_row_identity() {
        let source = "// our and pub bindings appear in the Types pane.\n\nour id x = x\npub answer = id 42\npub name = id \"Yulang\"\npub pair = (answer, name)\n\npair.say\n";
        let (hir, candidate) = crate::prepare(source, "types.yu", false).unwrap();
        for name in ["id", "answer", "name", "pair"] {
            let graph = candidate.export(&root(&hir, name)).unwrap();
            let scheme = CandidatePublicScheme::project(&graph).unwrap();
            assert_correspondence(&graph, &scheme);
            if name != "id" {
                continue;
            }
            let NodeKind::Row(root_row) = scheme.nodes[scheme.root.0].kind else {
                panic!("missing root row")
            };
            let head = scheme.heads().unwrap()[root_row.0].unwrap();
            let NodeKind::Function([argument, _, _, result]) = scheme.nodes[head.0].kind else {
                panic!("missing function")
            };
            let (NodeKind::Row(argument_row), NodeKind::Row(result_row)) =
                (&scheme.nodes[argument.0].kind, &scheme.nodes[result.0].kind)
            else {
                panic!("missing ports")
            };
            assert_eq!(
                argument_row, result_row,
                "one canonical row across opposite polarities"
            );
            assert_eq!(
                scheme.nodes[argument.0].source.polarity(),
                Polarity::Negative
            );
            assert_eq!(scheme.nodes[result.0].source.polarity(), Polarity::Positive);
        }
    }

    #[test]
    fn open_io_permission_keeps_distinct_state_support_in_typed_residual() {
        let source = "act io:\n    our tick: int -> ()\nact state:\n    our tick: int -> ()\nmy bridge (callback: int -> [io] ()) = callback\nmy state_callback value = state::tick value\nmy answer = bridge state_callback\n";
        let (hir, candidate) = crate::prepare(source, "open-io-state.yu", false).unwrap();
        let graph = candidate.export(&root(&hir, "bridge")).unwrap();
        let bridge = CandidatePublicScheme::project(&graph).unwrap();
        assert_correspondence(&graph, &bridge);
        let permission = bridge
            .permissions
            .iter()
            .find(|permission| permission.source.permitted().len() == 1)
            .unwrap();
        assert!(bridge.rows[permission.tail.0].source.is_effect());
        let io = &permission.source.permitted()[0];
        let graph = candidate.export(&root(&hir, "answer")).unwrap();
        let answer = CandidatePublicScheme::project(&graph).unwrap();
        assert_correspondence(&graph, &answer);
        assert!(
            answer.constraints.iter().any(|bound| {
                if !bound.source.is_effect() {
                    return false;
                }
                let NodeKind::Effect(effect) = &answer.nodes[bound.lower.0].kind else {
                    return false;
                };
                let CandidateGraphEffectOperand::SupportView { permitted, .. } = effect.source
                else {
                    return false;
                };
                let NodeKind::Row(residual) = answer.nodes[bound.upper.0].kind else {
                    return false;
                };
                permitted.iter().any(|state| state != io)
                    && answer.rows[residual.0].source.is_effect()
            }),
            "state support remains connected to an actual typed Effect row"
        );
    }

    #[test]
    fn public_types_reject_a_separately_prepared_identical_source() {
        let source = "my id x = x";
        let (hir, candidate) = crate::prepare(source, "identity.yu", false).unwrap();
        let (other_hir, _) = crate::prepare(source, "identity.yu", false).unwrap();
        assert!(crate::candidate_public_types(&hir, &candidate).is_ok());
        assert!(
            crate::candidate_public_types(&other_hir, &candidate).is_err(),
            "equal source text does not establish candidate/HIR ownership"
        );
    }

    #[test]
    fn deep_display_is_iterative_and_exhaustion_withholds_result() {
        let (hir, candidate) = crate::prepare("my id x = x", "depth.yu", false).unwrap();
        let graph = candidate.export(&root(&hir, "id")).unwrap();
        let mut scheme = CandidatePublicScheme::project(&graph).unwrap();
        let source = scheme.nodes[scheme.root.0].source;
        // Synthetic display-only stress case: this is not source-adequacy evidence.
        for _ in 0..OUTPUT_CAP {
            let child = scheme.root;
            scheme.root = NodeId(scheme.nodes.len());
            scheme.nodes.push(Node {
                source,
                kind: NodeKind::Tuple(vec![child]),
            });
        }
        assert!(
            scheme
                .render("deep")
                .unwrap_err()
                .contains("tool output cap exceeded")
        );
    }
}
