//! Source Value references, independent of solver rows and copied descriptions.
use crate::*;
use yu_hir::{HirLocalId, shadow::{LocalSource, LocalSourceForm, LocalSourceResolution}};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Value { Module(DefId), Local(HirLocalId), Parameter(HirParameterId), Expression(HirOccurrenceId) }
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
        // Shared nested Apply fragments keep both work and storage linear.
        let mut fragments = Vec::new();
        fragments.try_reserve_exact(source.expressions().len()).map_err(|_| unavailable())?;
        for expr in source.expressions() {
            if matches!(expr.form, LocalSourceForm::Name { .. } | LocalSourceForm::Apply { .. }) {
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
