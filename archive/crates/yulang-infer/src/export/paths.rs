use std::collections::{HashMap, HashSet};

use crate::ids::DefId;
use crate::lower::LowerState;
use crate::symbols::Path;

pub(crate) fn collect_canonical_binding_paths(state: &LowerState) -> HashMap<DefId, Path> {
    let mut canonical = state.ctx.canonical_value_paths();
    let defined_defs = canonical.keys().copied().collect::<HashSet<_>>();
    for (path, def) in state.ctx.collect_all_binding_paths() {
        if defined_defs.contains(&def) {
            continue;
        }
        match canonical.get_mut(&def) {
            Some(current) => choose_preferred_binding_path(current, path),
            None => {
                canonical.insert(def, path);
            }
        }
    }
    canonical
}

fn choose_preferred_binding_path(current: &mut Path, candidate: Path) {
    let candidate_key = binding_path_preference_key(&candidate);
    let current_key = binding_path_preference_key(current);
    if candidate_key < current_key {
        *current = candidate;
    }
}

fn binding_path_preference_key(path: &Path) -> (usize, Vec<&str>) {
    let priority = path
        .segments
        .iter()
        .position(|segment| segment.0.starts_with('&') || segment.0.starts_with('#'))
        .unwrap_or(usize::MAX);
    let lexical = path
        .segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>();
    (priority, lexical)
}
