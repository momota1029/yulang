use std::collections::HashMap;

use super::*;
use crate::ir::{Binding, Module};
use crate::types::hir_type_has_vars;

#[derive(Debug, Default, Clone)]
pub struct SpecializationTable {
    cache: HashMap<DemandKey, core_ir::Path>,
    known: Vec<DemandSpecialization>,
    fresh: Vec<DemandSpecialization>,
    next_index: usize,
}

impl SpecializationTable {
    pub fn from_module(module: &Module) -> Self {
        let mut table = Self {
            next_index: next_specialization_index(module),
            ..Self::default()
        };
        table.seed_existing(module);
        table
    }

    pub fn intern(&mut self, checked: &CheckedDemand) -> core_ir::Path {
        let key = checked_key(checked);
        if !should_materialize_demand(&key) {
            return checked.target.clone();
        }
        if let Some(path) = self.cache.get(&key) {
            return path.clone();
        }
        let path = specialized_path(&checked.target, self.next_index);
        self.next_index += 1;
        let specialization = DemandSpecialization {
            target: checked.target.clone(),
            path: path.clone(),
            key,
            solved: checked.solved.clone(),
        };
        self.cache.insert(specialization.key.clone(), path.clone());
        self.known.push(specialization.clone());
        self.fresh.push(specialization);
        path
    }

    pub fn into_specializations(self) -> Vec<DemandSpecialization> {
        self.known
    }

    pub fn into_output(self) -> SpecializationOutput {
        SpecializationOutput {
            known: self.known,
            fresh: self.fresh,
        }
    }

    fn seed_existing(&mut self, module: &Module) {
        for binding in &module.bindings {
            let Some(target) = unspecialized_demand_path(&binding.name)
                .or_else(|| unspecialized_legacy_mono_path(&binding.name))
            else {
                continue;
            };
            if !binding.type_params.is_empty() || hir_type_has_vars(&binding.body.ty) {
                debug_seed_existing_specialization(
                    "skip-open-binding",
                    &target,
                    &binding.name,
                    None,
                );
                continue;
            }
            let signature = DemandSignature::from_runtime_type(&binding.body.ty);
            if !signature.is_closed() {
                debug_seed_existing_specialization(
                    "skip-open-signature",
                    &target,
                    &binding.name,
                    Some(&signature),
                );
                continue;
            }
            let specialization = existing_specialization(target, binding, signature);
            if !self.cache.contains_key(&specialization.key) {
                debug_seed_existing_specialization(
                    "seed",
                    &specialization.target,
                    &specialization.path,
                    Some(&specialization.key.signature),
                );
                self.cache
                    .insert(specialization.key.clone(), specialization.path.clone());
                self.known.push(specialization);
            }
        }
    }
}

pub(super) fn demand_call_target(path: &core_ir::Path) -> core_ir::Path {
    unspecialized_demand_path(path)
        .or_else(|| unspecialized_legacy_mono_path(path))
        .unwrap_or_else(|| path.clone())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecializationOutput {
    pub known: Vec<DemandSpecialization>,
    pub fresh: Vec<DemandSpecialization>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandSpecialization {
    pub target: core_ir::Path,
    pub path: core_ir::Path,
    pub key: DemandKey,
    pub solved: DemandSignature,
}

fn checked_key(checked: &CheckedDemand) -> DemandKey {
    DemandKey::from_signature(checked.target.clone(), checked.expected.clone())
}

fn specialized_path(target: &core_ir::Path, index: usize) -> core_ir::Path {
    let mut path = target.clone();
    match path.segments.last_mut() {
        Some(name) => {
            name.0 = format!("{}__ddmono{index}", name.0);
        }
        None => {
            path.segments
                .push(core_ir::Name(format!("__ddmono{index}")));
        }
    }
    path
}

fn existing_specialization(
    target: core_ir::Path,
    binding: &Binding,
    signature: DemandSignature,
) -> DemandSpecialization {
    DemandSpecialization {
        target: target.clone(),
        path: binding.name.clone(),
        key: DemandKey::from_signature(target, signature.clone()),
        solved: signature,
    }
}

fn should_materialize_demand(key: &DemandKey) -> bool {
    let arity = signature_arity(&key.signature);
    if path_ends_with(&key.target, &["std", "range", "fold_from"]) {
        return arity >= 3;
    }
    if path_ends_with(&key.target, &["std", "range", "fold_ints"]) {
        return arity >= 4;
    }
    true
}

fn signature_arity(signature: &DemandSignature) -> usize {
    let mut arity = 0;
    let mut current = signature;
    loop {
        match current {
            DemandSignature::Fun { ret, .. } => {
                arity += 1;
                current = ret;
            }
            DemandSignature::Thunk { effect, value }
                if demand_effect_is_empty_for_arity(effect) =>
            {
                current = value;
            }
            _ => break,
        }
    }
    arity
}

fn demand_effect_is_empty_for_arity(effect: &DemandEffect) -> bool {
    match effect {
        DemandEffect::Empty => true,
        DemandEffect::Row(items) => items.iter().all(demand_effect_is_empty_for_arity),
        DemandEffect::Hole(_) | DemandEffect::Atom(_) => false,
    }
}

fn debug_seed_existing_specialization(
    action: &str,
    target: &core_ir::Path,
    path: &core_ir::Path,
    signature: Option<&DemandSignature>,
) {
    if std::env::var_os("YULANG_DEBUG_DEMAND_SOURCE").is_none()
        || !(path_ends_with(target, &["std", "list", "fold_impl"])
            || path_ends_with(target, &["std", "list", "view_raw"]))
    {
        return;
    }
    eprintln!("specialization seed {action} {target:?} <- {path:?}: {signature:?}");
}

fn path_ends_with(path: &core_ir::Path, suffix: &[&str]) -> bool {
    path.segments.len() >= suffix.len()
        && path
            .segments
            .iter()
            .rev()
            .zip(suffix.iter().rev())
            .all(|(segment, expected)| segment.0 == *expected)
}

fn next_specialization_index(module: &Module) -> usize {
    module
        .bindings
        .iter()
        .filter_map(|binding| demand_specialization_suffix(&binding.name))
        .max()
        .map(|index| index + 1)
        .unwrap_or(0)
}

fn demand_specialization_suffix(path: &core_ir::Path) -> Option<usize> {
    path.segments
        .last()?
        .0
        .rsplit_once("__ddmono")?
        .1
        .parse()
        .ok()
}

fn unspecialized_demand_path(path: &core_ir::Path) -> Option<core_ir::Path> {
    let mut base = path.clone();
    let name = &mut base.segments.last_mut()?.0;
    let index = name.find("__ddmono")?;
    name.truncate(index);
    Some(base)
}

fn unspecialized_legacy_mono_path(path: &core_ir::Path) -> Option<core_ir::Path> {
    let mut base = path.clone();
    let name = &mut base.segments.last_mut()?.0;
    let index = name.find("__mono")?;
    name.truncate(index);
    Some(base)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn specialization_table_reuses_same_key() {
        let checked = checked("id", DemandSignature::Core(named("int")));
        let mut table = SpecializationTable::default();

        let first = table.intern(&checked);
        let second = table.intern(&checked);
        let specializations = table.into_specializations();

        assert_eq!(first, second);
        assert_eq!(specializations.len(), 1);
    }

    #[test]
    fn specialization_table_allocates_paths_in_order() {
        let mut table = SpecializationTable::default();
        let first = table.intern(&checked("id", DemandSignature::Core(named("int"))));
        let second = table.intern(&checked("id", DemandSignature::Core(named("str"))));

        assert_eq!(first, path("id__ddmono0"));
        assert_eq!(second, path("id__ddmono1"));
    }

    #[test]
    fn demand_call_target_strips_demand_and_legacy_suffixes() {
        assert_eq!(demand_call_target(&path("id__ddmono12")), path("id"));
        assert_eq!(demand_call_target(&path("id__mono3")), path("id"));
        assert_eq!(demand_call_target(&path("id")), path("id"));
    }

    fn checked(name: &str, signature: DemandSignature) -> CheckedDemand {
        CheckedDemand {
            target: path(name),
            expected: signature.clone(),
            actual: signature.clone(),
            solved: signature,
            substitutions: DemandSubstitution::default(),
            child_demands: DemandQueue::default(),
            local_signatures: HashMap::new(),
        }
    }

    fn named(name: &str) -> DemandCoreType {
        DemandCoreType::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }
}
