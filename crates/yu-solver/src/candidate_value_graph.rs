//! Source Value references, independent of solver rows and copied descriptions.
use crate::*;
use yu_hir::{HirLocalId, shadow::{LocalSource, LocalSourceForm, LocalSourceResolution}};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) enum Value { Module(DefId), Local(HirLocalId), Parameter(HirParameterId), CatchBinder(yu_hir::shadow::LocalSourceCatchBinderId), Expression(HirOccurrenceId) }
#[derive(Clone, Copy, Debug)]
pub(super) struct Association { pub origin: usize, pub receiver: usize }
#[derive(Clone, Debug, Default)]
pub(super) struct Graph {
    modules: HashMap<DefinitionRootId, DefId>,
    vertices: HashMap<Value, usize>,
    edges: Vec<Vec<usize>>,
    reverse: Vec<Vec<usize>>,
    pub events: Vec<Association>,
    pub checking: HashMap<ConstraintOccurrenceId, usize>,
    components: Vec<usize>,
    edge_bytes: usize,
    identity_bytes: usize,
    pub seal_scratch_peak: usize,
    pub construction_scratch_peak: usize,
}
fn unavailable() -> CollectionAvailabilityError { CollectionAvailabilityError::ComponentIdentityExhausted }
impl Graph {
    // Observation only: auxiliary fragment vertices have no Value descriptor.
    pub fn observed_value(&self, ordinal: usize) -> Option<(&Value, usize)> {
        let value = self.vertices.iter().find_map(|(value, &id)| (id == ordinal).then_some(value))?;
        Some((value, *self.components.get(ordinal)?))
    }
    pub fn observed_checking(&self, event: usize) -> Option<&ConstraintOccurrenceId> {
        self.checking.iter().find_map(|(checking, &id)| (id == event).then_some(checking))
    }
    pub fn register_module(&mut self, root: DefinitionRootId, id: DefId) -> Result<(), CollectionAvailabilityError> {
        self.modules.try_reserve(1).map_err(|_| unavailable())?;
        self.identity_bytes = checked_usize_sum([self.identity_bytes, id.hash_eq_payload_bytes()], "Value module identity");
        self.modules.insert(root, id); Ok(())
    }
    fn intern(&mut self, value: Value) -> Result<usize, CollectionAvailabilityError> {
        if let Some(&id) = self.vertices.get(&value) { return Ok(id); }
        self.vertices.try_reserve(1).map_err(|_| unavailable())?;
        self.edges.try_reserve(1).map_err(|_| unavailable())?;
        self.reverse.try_reserve(1).map_err(|_| unavailable())?;
        if let Value::Module(id) = &value { self.identity_bytes = checked_usize_sum([self.identity_bytes, id.hash_eq_payload_bytes()], "Value identity"); }
        let id = self.edges.len(); self.vertices.insert(value, id);
        self.edges.push(Vec::new()); self.reverse.push(Vec::new()); Ok(id)
    }
    fn edge(&mut self, from: usize, to: usize) -> Result<(), CollectionAvailabilityError> {
        let previous = self.edges[from].capacity() + self.reverse[to].capacity();
        self.edges[from].try_reserve(1).map_err(|_| unavailable())?;
        self.reverse[to].try_reserve(1).map_err(|_| unavailable())?;
        self.edge_bytes = checked_usize_sum([self.edge_bytes, checked_capacity_bytes::<usize>(self.edges[from].capacity() + self.reverse[to].capacity() - previous, "Value edges")], "Value edges");
        self.edges[from].push(to); self.reverse[to].push(from); Ok(())
    }
    fn resolved(resolution: &LocalSourceResolution) -> Option<Value> {
        match resolution { LocalSourceResolution::ModuleDef(id) => Some(Value::Module(id.clone())),
            LocalSourceResolution::Local(id) => Some(Value::Local(id.clone())),
            LocalSourceResolution::CatchBinder(id) => Some(Value::CatchBinder(id.clone())),
            LocalSourceResolution::Parameter(id) => Some(Value::Parameter(id.clone())), _ => None }
    }
    fn expression_value(source: &LocalSource, mut index: usize) -> Value {
        loop { let expr = &source.expressions()[index]; match &expr.form {
            LocalSourceForm::Group { inner } | LocalSourceForm::Ascription { inner, .. } => index = inner.ordinal() as usize,
            LocalSourceForm::Name { resolution, .. } => return Self::resolved(resolution).unwrap_or_else(|| Value::Expression(expr.occurrence.clone())),
            _ => return Value::Expression(expr.occurrence.clone()),
        }}
    }
    pub fn retain_source(&mut self, source: &LocalSource) -> Result<(), CollectionAvailabilityError> {
        let module = self.modules.get(source.definition_root()).ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?.clone();
        let root = self.intern(Value::Module(module))?;
        let mut owners = Vec::new(); owners.try_reserve_exact(source.expressions().len()).map_err(|_| unavailable())?;
        owners.resize(source.expressions().len(), root);
        let mut work = Vec::new(); work.try_reserve(1).map_err(|_| unavailable())?; work.push((source.body().ordinal() as usize, root));
        // Tree construction assigns nested initializers to their own declaration.
        while let Some((index, owner)) = work.pop() {
            owners[index] = owner;
            let expr = &source.expressions()[index];
            match &expr.form {
                LocalSourceForm::Name { resolution, .. } => if let Some(value) = Self::resolved(resolution) {
                    let target = self.intern(value)?; self.edge(owner, target)?;
                },
                LocalSourceForm::Catch { scrutinee, arms } => {
                    work.try_reserve(arms.len().checked_add(1).ok_or_else(unavailable)?).map_err(|_| unavailable())?;
                    work.push((scrutinee.ordinal() as usize, owner));
                    for arm in arms { work.push((arm.body.ordinal() as usize, owner)); }
                },
                LocalSourceForm::If { arms, else_branch } => {
                    let count = arms.len().checked_mul(2).and_then(|n| n.checked_add(1)).ok_or_else(unavailable)?;
                    work.try_reserve(count).map_err(|_| unavailable())?;
                    work.push((else_branch.ordinal() as usize, owner));
                    for (condition, body) in arms {
                        work.push((condition.ordinal() as usize, owner));
                        work.push((body.ordinal() as usize, owner));
                    }
                },
                LocalSourceForm::Apply { callee, argument, .. } => {
                    work.try_reserve(2).map_err(|_| unavailable())?;
                    work.push((callee.ordinal() as usize, owner)); work.push((argument.ordinal() as usize, owner));
                },
                LocalSourceForm::Group { inner } | LocalSourceForm::Ascription { inner, .. } => { work.try_reserve(1).map_err(|_| unavailable())?; work.push((inner.ordinal() as usize, owner)); },
                LocalSourceForm::Lambda { body, .. } => { work.try_reserve(1).map_err(|_| unavailable())?; work.push((body.ordinal() as usize, owner)); },
                LocalSourceForm::Block { bindings, final_expression } => {
                    work.try_reserve(bindings.len() + 1).map_err(|_| unavailable())?;
                    work.push((final_expression.ordinal() as usize, owner));
                    for &binding in bindings {
                        let binding = &source.bindings()[binding as usize];
                        let local = self.intern(Value::Local(binding.id.clone()))?;
                        work.push((binding.initializer.ordinal() as usize, local));
                    }
                }, _ => {},
            }
        }
        // Fragment helpers are distinct from semantic Values. Every helper-only
        // path projects to the exact Name incidence, and every selected incidence
        // expands to such a path. Original-Value reachability and SCCs are unchanged.
        // Shared nested Apply/If fragments keep both work and storage linear.
        let mut fragments = Vec::new();
        fragments.try_reserve_exact(source.expressions().len()).map_err(|_| unavailable())?;
        for expr in source.expressions() {
            if matches!(expr.form, LocalSourceForm::Name { .. } | LocalSourceForm::Apply { .. } | LocalSourceForm::If { .. }) {
                self.edges.try_reserve(1).map_err(|_| unavailable())?;
                self.reverse.try_reserve(1).map_err(|_| unavailable())?;
                fragments.push(Some(self.edges.len()));
                self.edges.push(Vec::new()); self.reverse.push(Vec::new());
            } else { fragments.push(None); }
        }
        for (index, expr) in source.expressions().iter().enumerate() {
            if let LocalSourceForm::Name { resolution, .. } = &expr.form {
                if let Some(value) = Self::resolved(resolution) {
                    let target = self.intern(value)?;
                    self.edge(fragments[index].unwrap(), target)?;
                }
            }
            if let LocalSourceForm::If { arms, else_branch } = &expr.form {
                let result = self.intern(Value::Expression(expr.occurrence.clone()))?;
                let fragment = fragments[index].unwrap();
                self.edge(result, fragment)?;
                for (condition, body) in arms {
                    for child in [condition, body] {
                        if let Some(child) = fragments[child.ordinal() as usize] { self.edge(fragment, child)?; }
                    }
                }
                if let Some(child) = fragments[else_branch.ordinal() as usize] { self.edge(fragment, child)?; }
            }
            let LocalSourceForm::Apply { callee, argument, .. } = &expr.form else { continue; };
            let result = self.intern(Value::Expression(expr.occurrence.clone()))?;
            let fragment = fragments[index].unwrap();
            self.edge(result, fragment)?;
            for child in [callee, argument] {
                if let Some(child) = fragments[child.ordinal() as usize] { self.edge(fragment, child)?; }
            }
            let receiver = self.intern(Self::expression_value(source, callee.ordinal() as usize))?;
            self.events.try_reserve(1).map_err(|_| unavailable())?;
            self.checking.try_reserve(1).map_err(|_| unavailable())?;
            self.checking.insert(ConstraintOccurrenceId::new(expr.occurrence.clone(), 0), self.events.len());
            self.events.push(Association { origin: owners[index], receiver });
        }
        let scratch = checked_usize_sum([
            checked_capacity_bytes::<usize>(owners.capacity(), "Value owners"),
            checked_capacity_bytes::<(usize, usize)>(work.capacity(), "Value construction work"),
            checked_capacity_bytes::<Option<usize>>(fragments.capacity(), "Value fragments"),
        ], "Value construction scratch");
        self.construction_scratch_peak = self.construction_scratch_peak.max(scratch);
        Ok(())
    }
    pub fn seal(&mut self) -> Result<(), SolveAvailabilityError> {
        if self.components.len() == self.edges.len() { return Ok(()); }
        let fail = || SolveAvailabilityError::IdentityExhausted;
        let mut seen = Vec::new(); seen.try_reserve_exact(self.edges.len()).map_err(|_| fail())?; seen.resize(self.edges.len(), false);
        let mut finish = Vec::new(); finish.try_reserve_exact(self.edges.len()).map_err(|_| fail())?;
        let mut stack = Vec::new(); stack.try_reserve_exact(self.edges.len()).map_err(|_| fail())?;
        for start in 0..self.edges.len() {
            if seen[start] { continue; } seen[start] = true; stack.push((start, 0));
            while let Some((node, next)) = stack.last_mut() {
                if *next == self.edges[*node].len() { finish.push(*node); stack.pop(); }
                else { let child = self.edges[*node][*next]; *next += 1; if !seen[child] { seen[child] = true; stack.push((child, 0)); } }
            }
        }
        self.seal_scratch_peak = checked_usize_sum([checked_capacity_bytes::<bool>(seen.capacity(), "SCC seen"), checked_capacity_bytes::<usize>(finish.capacity(), "SCC finish"), checked_capacity_bytes::<(usize, usize)>(stack.capacity(), "SCC stack")], "SCC scratch");
        self.components.try_reserve_exact(self.edges.len()).map_err(|_| fail())?;
        self.components.resize(self.edges.len(), usize::MAX);
        for start in finish.into_iter().rev() {
            if self.components[start] != usize::MAX { continue; }
            self.components[start] = start; stack.push((start, 0));
            while let Some((node, _)) = stack.pop() { for &child in &self.reverse[node] {
                if self.components[child] == usize::MAX { self.components[child] = start; stack.push((child, 0)); }
            }}
        }
        Ok(())
    }
    pub fn qualifies(&self, event: usize) -> bool {
        self.events.get(event).is_some_and(|event| self.components.get(event.origin).zip(self.components.get(event.receiver)).is_some_and(|(a,b)| a == b))
    }
    pub fn bytes(&self) -> usize {
        checked_usize_sum([
            checked_capacity_bytes::<(DefinitionRootId, DefId)>(self.modules.capacity(), "Value modules"),
            checked_capacity_bytes::<(Value, usize)>(self.vertices.capacity(), "source Values"),
            checked_capacity_bytes::<Vec<usize>>(self.edges.capacity() + self.reverse.capacity(), "Value adjacency"),
            self.edge_bytes,
            self.identity_bytes,
            checked_capacity_bytes::<Association>(self.events.capacity(), "extrusion associations"),
            checked_capacity_bytes::<(ConstraintOccurrenceId, usize)>(self.checking.capacity(), "source associations"),
            checked_capacity_bytes::<usize>(self.components.capacity(), "Value SCCs"),
        ], "source Value graph")
    }
}

#[cfg(test)]
mod conditional_reference_tests {
    use super::*;

    fn fixture(text: &str) -> (Graph, LocalSource) {
        let input = text;
        let text: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "healthy source fixture: {input}");
        let hir = yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("conditional-references", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty()).unwrap();
        let mut graph = Graph::default();
        for item in hir.items() {
            if let yu_hir::HirItem::Binding(binding) = item {
                graph.register_module(binding.definition_root().clone(), binding.id().clone()).unwrap();
            }
        }
        let yu_hir::HirItem::Binding(binding) = hir.items().last().unwrap() else { panic!("binding"); };
        let source = hir.local_source(binding.definition_root()).unwrap().unwrap().clone();
        graph.retain_source(&source).unwrap();
        (graph, source)
    }

    fn named(source: &LocalSource, spelling: &str) -> Value {
        source.expressions().iter().find_map(|expr| match &expr.form {
            LocalSourceForm::Name { spelling: name, resolution } if name.as_ref() == spelling => Graph::resolved(resolution),
            _ => None,
        }).unwrap()
    }

    // Contract helper paths only: stop at semantic Values rather than following
    // their definition-owner references.
    fn references(graph: &Graph, value: &Value) -> std::collections::HashSet<Value> {
        let semantic: HashMap<_, _> = graph.vertices.iter().map(|(value, &id)| (id, value)).collect();
        let mut work = graph.edges[graph.vertices[value]].clone();
        let mut seen = std::collections::HashSet::new();
        let mut result = std::collections::HashSet::new();
        while let Some(id) = work.pop() {
            if !seen.insert(id) { continue; }
            if let Some(value) = semantic.get(&id) { result.insert((*value).clone()); }
            else { work.extend(&graph.edges[id]); }
        }
        result
    }

    fn conditional(source: &LocalSource) -> Value {
        let expr = source.expressions().iter().find(|expr| matches!(expr.form, LocalSourceForm::If { .. })).unwrap();
        Value::Expression(expr.occurrence.clone())
    }

    fn expected(source: &LocalSource, names: &[&str]) -> std::collections::HashSet<Value> {
        names.iter().map(|name| named(source, name)).collect()
    }

    #[test]
    fn conditional_result_retains_condition_and_every_branch_identity() {
        let (graph, source) = fixture("my choose p f g = if p: f else: g");
        assert_eq!(references(&graph, &conditional(&source)), expected(&source, &["p", "f", "g"]));
        for condition in ["true", "false"] {
            let (graph, source) = fixture(&format!("my choose f g = if {condition}: f else: g"));
            assert_eq!(references(&graph, &conditional(&source)), expected(&source, &["f", "g"]));
        }
        let (graph, source) = fixture("my p = true\nmy f = 1\nmy g = 2\nmy choose = if p: f else: g");
        let names = expected(&source, &["p", "f", "g"]);
        assert!(names.iter().all(|value| matches!(value, Value::Module(_))));
        assert_eq!(references(&graph, &conditional(&source)), names);
    }

    #[test]
    fn conditional_shared_fragments_follow_nested_if_elsif_and_apply() {
        let (graph, source) = fixture("my choose p q r f g h x = if p: f x elsif q: if r: g else: h else: x");
        assert_eq!(references(&graph, &conditional(&source)), expected(&source, &["p", "q", "r", "f", "g", "h", "x"]));
        assert_eq!(source.expressions().iter().filter(|expr| matches!(expr.form, LocalSourceForm::If { .. })).count(), 2);
    }

    #[test]
    fn apply_uses_direct_conditional_argument_fragment() {
        let (graph, source) = fixture("my choose p f g h = h(if p: f else: g)");
        let expr = source.expressions().iter().find(|expr| matches!(&expr.form,
            LocalSourceForm::Apply { argument, .. } if matches!(source.expression(argument).unwrap().form, LocalSourceForm::If { .. }))).unwrap();
        assert_eq!(references(&graph, &Value::Expression(expr.occurrence.clone())), expected(&source, &["h", "p", "f", "g"]));
    }

    #[test]
    fn grouped_conditional_callee_preserves_receiver_and_fragment_boundary() {
        let (mut graph, source) = fixture("my choose p f g x = (if p: f else: g) x");
        let conditional = conditional(&source);
        assert_eq!(references(&graph, &conditional), expected(&source, &["p", "f", "g"]));
        let apply = source.expressions().iter().find(|expr| matches!(&expr.form,
            LocalSourceForm::Apply { callee, .. } if matches!(source.expression(callee).unwrap().form, LocalSourceForm::Group { .. }))).unwrap();
        assert_eq!(references(&graph, &Value::Expression(apply.occurrence.clone())), expected(&source, &["x"]));
        let checking = ConstraintOccurrenceId::new(apply.occurrence.clone(), 0);
        let event = graph.checking[&checking];
        assert_eq!(graph.events[event].receiver, graph.vertices[&conditional]);
        let root = Value::Module(graph.modules[source.definition_root()].clone());
        assert_eq!(graph.events[event].origin, graph.vertices[&root]);
        graph.seal().unwrap();
        assert!(!graph.qualifies(event));
    }

    #[test]
    fn conditional_fragments_preserve_wrapper_boundaries() {
        for text in [
            "my choose p f g = if p: (f) else: g",
            "my choose p f g = if p: f as int else: g",
            "my choose p f g = if p:\n    f\nelse: g",
        ] {
            let (graph, source) = fixture(text);
            assert_eq!(references(&graph, &conditional(&source)), expected(&source, &["p", "g"]));
            let root = Value::Module(graph.modules[source.definition_root()].clone());
            assert!(references(&graph, &root).contains(&named(&source, "f")));
        }
    }

    #[test]
    fn conditional_nested_initializer_keeps_its_definition_owner() {
        let (graph, source) = fixture("my choose p f g = { my inner = if p: f else: g; inner }");
        let inner = Value::Local(source.bindings().iter().find(|binding| binding.spelling.as_ref() == "inner").unwrap().id.clone());
        let names = expected(&source, &["p", "f", "g"]);
        assert_eq!(references(&graph, &inner), names);
        assert_eq!(references(&graph, &conditional(&source)), names);
        let root = Value::Module(graph.modules[source.definition_root()].clone());
        assert_eq!(references(&graph, &root), [inner].into_iter().collect());
    }

    #[test]
    fn conditional_extension_preserves_semantic_sccs_and_qualification() {
        let (mut graph, source) = fixture("my loop p x = if p: loop x else: x");
        // Remove precisely the new If result/helper links to reconstruct the
        // previous graph on these same branded source identities.
        let mut previous = graph.clone();
        for expr in source.expressions() {
            if !matches!(expr.form, LocalSourceForm::If { .. }) { continue; }
            let result = graph.vertices[&Value::Expression(expr.occurrence.clone())];
            let helper = graph.edges[result][0];
            previous.edges[result].clear();
            previous.edges[helper].clear();
        }
        for incoming in &mut previous.reverse { incoming.clear(); }
        for (from, children) in previous.edges.iter().enumerate() {
            for &to in children { previous.reverse[to].push(from); }
        }
        graph.seal().unwrap(); previous.seal().unwrap();
        for &left in graph.vertices.values() {
            for &right in graph.vertices.values() {
                assert_eq!(graph.components[left] == graph.components[right], previous.components[left] == previous.components[right]);
            }
        }
        for event in 0..graph.events.len() { assert_eq!(graph.qualifies(event), previous.qualifies(event)); }
        assert!(graph.events.iter().enumerate().any(|(event, _)| graph.qualifies(event)));
        for (value, &id) in &graph.vertices {
            if matches!(value, Value::Expression(_)) { assert!(graph.reverse[id].is_empty()); }
        }
    }
}
