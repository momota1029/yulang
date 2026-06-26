use std::collections::{HashMap, HashSet};

use super::{CollectedSource, discover_module_loads};
use sources::{ModuleLoadRequest, Path, SourceFile, UseImport, UsePathRoute, Visibility};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompilationUnits {
    pub units: Vec<SourceCompilationUnit>,
    pub file_units: Vec<usize>,
    pub module_loads: Vec<Vec<ModuleLoadRequest>>,
}

impl SourceCompilationUnits {
    pub fn unit_for_file(&self, file: usize) -> Option<usize> {
        self.file_units.get(file).copied()
    }

    pub fn dependency_closed_available_units(&self, available: &[bool]) -> Vec<usize> {
        let mut selected = vec![false; self.units.len()];
        for (unit, item) in self.units.iter().enumerate() {
            let artifact_available = available.get(unit).copied().unwrap_or(false);
            if artifact_available && item.dependencies.iter().all(|dep| selected[*dep]) {
                selected[unit] = true;
            }
        }
        selected
            .into_iter()
            .enumerate()
            .filter_map(|(unit, selected)| selected.then_some(unit))
            .collect()
    }

    pub fn cache_selection(&self, available: &[bool]) -> SourceUnitCacheSelection {
        let cached_units = self.dependency_closed_available_units(available);
        let mut cached_unit = vec![false; self.units.len()];
        for unit in &cached_units {
            cached_unit[*unit] = true;
        }

        let mut cached_files = Vec::new();
        let mut source_files = Vec::new();
        for (file, unit) in self.file_units.iter().copied().enumerate() {
            if cached_unit[unit] {
                cached_files.push(file);
            } else {
                source_files.push(file);
            }
        }

        SourceUnitCacheSelection {
            cached_units,
            cached_files,
            source_files,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompilationUnit {
    pub files: Vec<usize>,
    pub dependencies: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceUnitCacheSelection {
    pub cached_units: Vec<usize>,
    pub cached_files: Vec<usize>,
    pub source_files: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceUnitLoweringInputError {
    UnknownUnit {
        unit: usize,
    },
    MissingModuleLoadVisibility {
        module_path: Path,
    },
    ConflictingModuleLoadVisibility {
        module_path: Path,
    },
    UnsupportedModuleLoadVisibility {
        module_path: Path,
        visibility: Visibility,
    },
}

pub fn source_compilation_units(files: &[CollectedSource]) -> SourceCompilationUnits {
    let module_files = files
        .iter()
        .enumerate()
        .map(|(index, file)| (file.module_path.clone(), index))
        .collect::<HashMap<_, _>>();
    let module_loads = files
        .iter()
        .map(|file| discover_module_loads(&file.module_path, &file.source))
        .collect::<Vec<_>>();
    let edges = source_dependency_edges(files, &module_loads, &module_files);
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

    SourceCompilationUnits {
        units,
        file_units,
        module_loads,
    }
}

pub fn source_unit_lowering_source_files(
    files: &[CollectedSource],
    units: &SourceCompilationUnits,
    unit: usize,
) -> Result<Vec<SourceFile>, SourceUnitLoweringInputError> {
    let source_unit = units
        .units
        .get(unit)
        .ok_or(SourceUnitLoweringInputError::UnknownUnit { unit })?;
    source_unit_lowering_source_files_for_indices(files, units, &source_unit.files)
}

pub fn source_unit_closure_file_indices(
    units: &SourceCompilationUnits,
    unit: usize,
) -> Result<Vec<usize>, SourceUnitLoweringInputError> {
    if unit >= units.units.len() {
        return Err(SourceUnitLoweringInputError::UnknownUnit { unit });
    }

    let mut selected = vec![false; units.units.len()];
    collect_source_unit_closure(units, unit, &mut selected);
    let mut files = Vec::new();
    for (unit, selected) in selected.into_iter().enumerate() {
        if selected {
            files.extend(units.units[unit].files.iter().copied());
        }
    }
    files.sort_unstable();
    files.dedup();
    Ok(files)
}

pub fn source_unit_closure_lowering_source_files(
    files: &[CollectedSource],
    units: &SourceCompilationUnits,
    unit: usize,
) -> Result<Vec<SourceFile>, SourceUnitLoweringInputError> {
    let file_indices = source_unit_closure_file_indices(units, unit)?;
    source_unit_lowering_source_files_for_indices(files, units, &file_indices)
}

fn source_unit_lowering_source_files_for_indices(
    files: &[CollectedSource],
    units: &SourceCompilationUnits,
    file_indices: &[usize],
) -> Result<Vec<SourceFile>, SourceUnitLoweringInputError> {
    let actual_paths = file_indices
        .iter()
        .map(|file| files[*file].module_path.clone())
        .collect::<HashSet<_>>();
    let module_load_visibility = module_load_visibility(&units.module_loads)?;
    let synthetic_paths = synthetic_parent_module_paths(file_indices, files, &actual_paths);
    let required_paths = actual_paths
        .iter()
        .cloned()
        .chain(synthetic_paths.iter().cloned())
        .collect::<HashSet<_>>();

    let mut lowering_files = synthetic_paths
        .into_iter()
        .map(|module_path| {
            synthetic_module_source_file(&module_path, &required_paths, &module_load_visibility)
        })
        .collect::<Result<Vec<_>, _>>()?;
    lowering_files.extend(file_indices.iter().map(|file| SourceFile {
        module_path: files[*file].module_path.clone(),
        source: files[*file].source.clone(),
    }));
    Ok(lowering_files)
}

fn collect_source_unit_closure(units: &SourceCompilationUnits, unit: usize, selected: &mut [bool]) {
    if selected[unit] {
        return;
    }
    selected[unit] = true;
    for dependency in &units.units[unit].dependencies {
        collect_source_unit_closure(units, *dependency, selected);
    }
}

fn source_dependency_edges(
    files: &[CollectedSource],
    module_loads: &[Vec<ModuleLoadRequest>],
    module_files: &HashMap<Path, usize>,
) -> Vec<Vec<usize>> {
    let mut edges = Vec::with_capacity(module_loads.len());
    for (file, requests) in files.iter().zip(module_loads) {
        let mut deps = requests
            .iter()
            .filter_map(|request| module_files.get(&request.module_path()).copied())
            .collect::<Vec<_>>();
        deps.extend(
            file.resolution_imports
                .iter()
                .filter_map(|import| import_dependency_file(import, module_files)),
        );
        deps.sort_unstable();
        deps.dedup();
        edges.push(deps);
    }
    edges
}

fn import_dependency_file(
    import: &UseImport,
    module_files: &HashMap<Path, usize>,
) -> Option<usize> {
    let (path, route) = match import {
        UseImport::Alias { path, route, .. } => (path, *route),
        UseImport::Glob { prefix, route, .. } => (prefix, *route),
    };
    match route {
        UsePathRoute::CurrentBand | UsePathRoute::CurrentRealm { .. } => {
            longest_existing_module_prefix(path, module_files)
        }
        UsePathRoute::Relative | UsePathRoute::SlashQualified { .. } => None,
    }
}

fn longest_existing_module_prefix(
    path: &Path,
    module_files: &HashMap<Path, usize>,
) -> Option<usize> {
    for len in (1..=path.segments.len()).rev() {
        let candidate = Path {
            segments: path.segments[..len].to_vec(),
        };
        if let Some(file) = module_files.get(&candidate).copied() {
            return Some(file);
        }
    }
    None
}

fn module_load_visibility(
    module_loads: &[Vec<ModuleLoadRequest>],
) -> Result<HashMap<Path, Visibility>, SourceUnitLoweringInputError> {
    let mut visibility = HashMap::new();
    for requests in module_loads {
        for request in requests {
            let module_path = request.module_path();
            match visibility.get(&module_path).copied() {
                Some(existing) if existing != request.visibility => {
                    return Err(
                        SourceUnitLoweringInputError::ConflictingModuleLoadVisibility {
                            module_path,
                        },
                    );
                }
                Some(_) => {}
                None => {
                    visibility.insert(module_path, request.visibility);
                }
            }
        }
    }
    Ok(visibility)
}

fn synthetic_parent_module_paths(
    file_indices: &[usize],
    files: &[CollectedSource],
    actual_paths: &HashSet<Path>,
) -> Vec<Path> {
    let mut paths = HashSet::new();
    for file in file_indices {
        let module_path = &files[*file].module_path;
        for depth in 0..module_path.segments.len() {
            let parent = Path {
                segments: module_path.segments[..depth].to_vec(),
            };
            if !actual_paths.contains(&parent) {
                paths.insert(parent);
            }
        }
    }
    let mut paths = paths.into_iter().collect::<Vec<_>>();
    paths.sort_by_key(|path| (path.segments.len(), module_path_sort_key(path)));
    paths
}

fn synthetic_module_source_file(
    module_path: &Path,
    required_paths: &HashSet<Path>,
    visibility: &HashMap<Path, Visibility>,
) -> Result<SourceFile, SourceUnitLoweringInputError> {
    let mut children = required_paths
        .iter()
        .filter_map(|path| direct_child_module_path(module_path, path))
        .collect::<Vec<_>>();
    children.sort_by_key(module_path_sort_key);
    children.dedup();

    let mut source = String::new();
    for child in children {
        let visibility = visibility.get(&child).copied().ok_or_else(|| {
            SourceUnitLoweringInputError::MissingModuleLoadVisibility {
                module_path: child.clone(),
            }
        })?;
        source.push_str(module_visibility_prefix(&child, visibility)?);
        source.push_str("mod ");
        source.push_str(
            &child
                .segments
                .last()
                .expect("child path should have name")
                .0,
        );
        source.push_str(";\n");
    }

    Ok(SourceFile {
        module_path: module_path.clone(),
        source,
    })
}

fn direct_child_module_path(parent: &Path, candidate: &Path) -> Option<Path> {
    if candidate.segments.len() != parent.segments.len() + 1 {
        return None;
    }
    if !candidate
        .segments
        .iter()
        .zip(&parent.segments)
        .all(|(candidate, parent)| candidate == parent)
    {
        return None;
    }
    Some(candidate.clone())
}

fn module_path_sort_key(path: &Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("\0")
}

fn module_visibility_prefix(
    module_path: &Path,
    visibility: Visibility,
) -> Result<&'static str, SourceUnitLoweringInputError> {
    match visibility {
        Visibility::Pub => Ok("pub "),
        Visibility::Our => Ok(""),
        Visibility::My => Err(
            SourceUnitLoweringInputError::UnsupportedModuleLoadVisibility {
                module_path: module_path.clone(),
                visibility,
            },
        ),
    }
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
