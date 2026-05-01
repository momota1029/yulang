use std::collections::HashMap;

use super::*;

#[derive(Debug, Default, Clone)]
pub struct SpecializationTable {
    cache: HashMap<DemandKey, core_ir::Path>,
    specializations: Vec<DemandSpecialization>,
}

impl SpecializationTable {
    pub fn intern(&mut self, checked: &CheckedDemand) -> core_ir::Path {
        if let Some(path) = self.cache.get(&checked_key(checked)) {
            return path.clone();
        }
        let path = specialized_path(&checked.target, self.specializations.len());
        let specialization = DemandSpecialization {
            target: checked.target.clone(),
            path: path.clone(),
            key: checked_key(checked),
            solved: checked.solved.clone(),
        };
        self.cache.insert(specialization.key.clone(), path.clone());
        self.specializations.push(specialization);
        path
    }

    pub fn into_specializations(self) -> Vec<DemandSpecialization> {
        self.specializations
    }
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

    fn checked(name: &str, signature: DemandSignature) -> CheckedDemand {
        CheckedDemand {
            target: path(name),
            expected: signature.clone(),
            actual: signature.clone(),
            solved: signature,
            substitutions: DemandSubstitution::default(),
            child_demands: DemandQueue::default(),
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
