use std::collections::{HashMap, HashSet};

use super::{CollectedSource, discover_module_loads};
use sources::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompilationUnits {
    pub units: Vec<SourceCompilationUnit>,
    pub file_units: Vec<usize>,
}

impl SourceCompilationUnits {
    pub fn unit_for_file(&self, file: usize) -> Option<usize> {
        self.file_units.get(file).copied()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompilationUnit {
    pub files: Vec<usize>,
    pub dependencies: Vec<usize>,
}

pub fn source_compilation_units(files: &[CollectedSource]) -> SourceCompilationUnits {
    let module_files = files
        .iter()
        .enumerate()
        .map(|(index, file)| (file.module_path.clone(), index))
        .collect::<HashMap<_, _>>();
    let edges = source_dependency_edges(files, &module_files);
    let mut units = tarjan_sccs(&edges)
        .into_iter()
        .map(|mut files| {
            files.sort_unstable();
            SourceCompilationUnit {
                files,
                dependencies: Vec::new(),
            }
        })
        .collect::<Vec<_>>();
    let mut file_units = file_units(files.len(), &units);

    attach_unit_dependencies(&edges, &file_units, &mut units);
    order_units_by_dependency(&mut units, &mut file_units);

    SourceCompilationUnits { units, file_units }
}

fn source_dependency_edges(
    files: &[CollectedSource],
    module_files: &HashMap<Path, usize>,
) -> Vec<Vec<usize>> {
    let mut edges = Vec::with_capacity(files.len());
    for file in files {
        let mut deps = discover_module_loads(&file.module_path, &file.source)
            .into_iter()
            .filter_map(|request| module_files.get(&request.module_path()).copied())
            .collect::<Vec<_>>();
        deps.sort_unstable();
        deps.dedup();
        edges.push(deps);
    }
    edges
}

fn file_units(file_count: usize, units: &[SourceCompilationUnit]) -> Vec<usize> {
    let mut file_units = vec![usize::MAX; file_count];
    for (unit, item) in units.iter().enumerate() {
        for file in &item.files {
            file_units[*file] = unit;
        }
    }
    file_units
}

fn attach_unit_dependencies(
    edges: &[Vec<usize>],
    file_units: &[usize],
    units: &mut [SourceCompilationUnit],
) {
    let mut deps = vec![HashSet::new(); units.len()];
    for (source, targets) in edges.iter().enumerate() {
        let source_unit = file_units[source];
        for target in targets {
            let target_unit = file_units[*target];
            if source_unit != target_unit {
                deps[source_unit].insert(target_unit);
            }
        }
    }
    for (unit, deps) in units.iter_mut().zip(deps) {
        unit.dependencies = deps.into_iter().collect();
        unit.dependencies.sort_unstable();
    }
}

fn order_units_by_dependency(units: &mut Vec<SourceCompilationUnit>, file_units: &mut Vec<usize>) {
    let mut order = Vec::with_capacity(units.len());
    let mut state = vec![VisitState::Unseen; units.len()];
    for unit in 0..units.len() {
        visit_unit(unit, units, &mut state, &mut order);
    }

    let mut new_index = vec![0; units.len()];
    for (index, old) in order.iter().enumerate() {
        new_index[*old] = index;
    }

    let mut ordered = order
        .into_iter()
        .map(|unit| units[unit].clone())
        .collect::<Vec<_>>();
    for unit in &mut ordered {
        for dep in &mut unit.dependencies {
            *dep = new_index[*dep];
        }
        unit.dependencies.sort_unstable();
    }
    for unit in file_units {
        *unit = new_index[*unit];
    }
    *units = ordered;
}

fn visit_unit(
    unit: usize,
    units: &[SourceCompilationUnit],
    state: &mut [VisitState],
    order: &mut Vec<usize>,
) {
    match state[unit] {
        VisitState::Done => return,
        VisitState::Visiting => return,
        VisitState::Unseen => {}
    }
    state[unit] = VisitState::Visiting;
    for dep in &units[unit].dependencies {
        visit_unit(*dep, units, state, order);
    }
    state[unit] = VisitState::Done;
    order.push(unit);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VisitState {
    Unseen,
    Visiting,
    Done,
}

fn tarjan_sccs(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut tarjan = Tarjan::new(edges);
    for node in 0..edges.len() {
        if tarjan.indexes[node].is_none() {
            tarjan.visit(node);
        }
    }
    tarjan.sccs
}

struct Tarjan<'a> {
    edges: &'a [Vec<usize>],
    next_index: usize,
    indexes: Vec<Option<usize>>,
    lowlinks: Vec<usize>,
    stack: Vec<usize>,
    on_stack: Vec<bool>,
    sccs: Vec<Vec<usize>>,
}

impl<'a> Tarjan<'a> {
    fn new(edges: &'a [Vec<usize>]) -> Self {
        Self {
            edges,
            next_index: 0,
            indexes: vec![None; edges.len()],
            lowlinks: vec![0; edges.len()],
            stack: Vec::new(),
            on_stack: vec![false; edges.len()],
            sccs: Vec::new(),
        }
    }

    fn visit(&mut self, node: usize) {
        let index = self.next_index;
        self.next_index += 1;
        self.indexes[node] = Some(index);
        self.lowlinks[node] = index;
        self.stack.push(node);
        self.on_stack[node] = true;

        for next in &self.edges[node] {
            match self.indexes[*next] {
                None => {
                    self.visit(*next);
                    self.lowlinks[node] = self.lowlinks[node].min(self.lowlinks[*next]);
                }
                Some(next_index) if self.on_stack[*next] => {
                    self.lowlinks[node] = self.lowlinks[node].min(next_index);
                }
                Some(_) => {}
            }
        }

        if self.lowlinks[node] == index {
            let mut scc = Vec::new();
            loop {
                let popped = self.stack.pop().expect("tarjan stack must contain node");
                self.on_stack[popped] = false;
                scc.push(popped);
                if popped == node {
                    break;
                }
            }
            self.sccs.push(scc);
        }
    }
}
