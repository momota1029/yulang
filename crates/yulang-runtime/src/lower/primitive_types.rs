use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub(super) enum PrimitiveTypeFamily {
    Int,
    Float,
    Bool,
    Unit,
    Str,
    List,
    Range,
}

#[derive(Debug, Clone, Default)]
pub(super) struct RuntimePrimitivePathTable;

impl RuntimePrimitivePathTable {
    pub(super) fn standard() -> Self {
        Self
    }

    pub(super) fn lit_type(&self, lit: &core_ir::Lit) -> core_ir::Type {
        let family = match lit {
            core_ir::Lit::Int(_) => PrimitiveTypeFamily::Int,
            core_ir::Lit::Float(_) => PrimitiveTypeFamily::Float,
            core_ir::Lit::String(_) => PrimitiveTypeFamily::Str,
            core_ir::Lit::Bool(_) => PrimitiveTypeFamily::Bool,
            core_ir::Lit::Unit => PrimitiveTypeFamily::Unit,
        };
        self.primitive_type(family, Vec::new())
    }

    pub(super) fn bool_type(&self) -> core_ir::Type {
        self.primitive_type(PrimitiveTypeFamily::Bool, Vec::new())
    }

    pub(super) fn unit_type(&self) -> core_ir::Type {
        self.primitive_type(PrimitiveTypeFamily::Unit, Vec::new())
    }

    pub(super) fn primitive_type(
        &self,
        family: PrimitiveTypeFamily,
        args: Vec<core_ir::TypeArg>,
    ) -> core_ir::Type {
        core_ir::Type::Named {
            path: primitive_type_path(family),
            args,
        }
    }
}

#[cfg(test)]
pub(super) fn bool_type() -> core_ir::Type {
    RuntimePrimitivePathTable::standard().bool_type()
}

#[cfg(test)]
pub(super) fn unit_type() -> core_ir::Type {
    RuntimePrimitivePathTable::standard().unit_type()
}

pub(super) fn primitive_type_path(family: PrimitiveTypeFamily) -> core_ir::Path {
    match family {
        PrimitiveTypeFamily::Int => bare_path("int"),
        PrimitiveTypeFamily::Float => bare_path("float"),
        PrimitiveTypeFamily::Bool => bare_path("bool"),
        PrimitiveTypeFamily::Unit => bare_path("unit"),
        PrimitiveTypeFamily::Str => std_path("str", "str"),
        PrimitiveTypeFamily::List => std_path("list", "list"),
        PrimitiveTypeFamily::Range => std_path("range", "range"),
    }
}

#[cfg(test)]
pub(super) fn named_type(name: &str) -> core_ir::Type {
    core_ir::Type::Named {
        path: bare_path(name),
        args: Vec::new(),
    }
}

fn bare_path(name: &str) -> core_ir::Path {
    core_ir::Path::from_name(core_ir::Name(name.to_string()))
}

fn std_path(module: &str, name: &str) -> core_ir::Path {
    core_ir::Path::new(vec![
        core_ir::Name("std".to_string()),
        core_ir::Name(module.to_string()),
        core_ir::Name(name.to_string()),
    ])
}
