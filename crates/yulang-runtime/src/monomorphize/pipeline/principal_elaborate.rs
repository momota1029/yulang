use crate::ir::Module;

use super::{SubstitutionSpecializeProfile, substitute_specialize_module_profiled};

pub(super) fn principal_elaborate_module_profiled(
    module: Module,
) -> (Module, SubstitutionSpecializeProfile) {
    // This pass is being migrated from substitution-specialize to
    // principal-elaborate. The main path should execute exported principal
    // elaboration evidence, not infer substitutions from runtime IR shapes.
    substitute_specialize_module_profiled(module)
}
