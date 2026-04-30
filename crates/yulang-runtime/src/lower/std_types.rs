use super::*;

pub(super) fn lit_type(lit: &core_ir::Lit) -> core_ir::Type {
    let name = match lit {
        core_ir::Lit::Int(_) => "int",
        core_ir::Lit::Float(_) => "float",
        core_ir::Lit::String(_) => return std_type("str", "str"),
        core_ir::Lit::Bool(_) => "bool",
        core_ir::Lit::Unit => "unit",
    };
    named_type(name)
}

pub(super) fn bool_type() -> core_ir::Type {
    named_type("bool")
}

pub(super) fn unit_type() -> core_ir::Type {
    named_type("unit")
}

pub(super) fn named_type(name: &str) -> core_ir::Type {
    core_ir::Type::Named {
        path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
        args: Vec::new(),
    }
}

pub(super) fn std_type(module: &str, name: &str) -> core_ir::Type {
    core_ir::Type::Named {
        path: core_ir::Path::new(vec![
            core_ir::Name("std".to_string()),
            core_ir::Name(module.to_string()),
            core_ir::Name(name.to_string()),
        ]),
        args: Vec::new(),
    }
}
