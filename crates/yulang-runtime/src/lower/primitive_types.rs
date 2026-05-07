use super::*;
use std::collections::HashMap;

type PrimitiveTypeFamily = core_ir::PrimitiveTypeFamily;

#[derive(Debug, Clone)]
pub(super) struct RuntimePrimitivePathTable {
    types: HashMap<PrimitiveTypeFamily, core_ir::Path>,
}

impl RuntimePrimitivePathTable {
    pub(super) fn standard() -> Self {
        let mut types = HashMap::new();
        for family in [
            PrimitiveTypeFamily::Int,
            PrimitiveTypeFamily::Float,
            PrimitiveTypeFamily::Bool,
            PrimitiveTypeFamily::Unit,
            PrimitiveTypeFamily::Str,
            PrimitiveTypeFamily::List,
            PrimitiveTypeFamily::ListView,
            PrimitiveTypeFamily::Range,
        ] {
            types.insert(family, standard_primitive_type_path(family));
        }
        Self { types }
    }

    pub(super) fn from_graph(graph: &core_ir::CoreGraphView) -> Self {
        let mut table = Self::standard();
        for node in &graph.primitive_types {
            table.types.insert(node.family, node.path.clone());
        }
        table
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
            path: self.primitive_type_path(family),
            args,
        }
    }

    fn primitive_type_path(&self, family: PrimitiveTypeFamily) -> core_ir::Path {
        self.types
            .get(&family)
            .cloned()
            .unwrap_or_else(|| standard_primitive_type_path(family))
    }
}

impl Default for RuntimePrimitivePathTable {
    fn default() -> Self {
        Self::standard()
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

fn standard_primitive_type_path(family: PrimitiveTypeFamily) -> core_ir::Path {
    match family {
        PrimitiveTypeFamily::Int => bare_path("int"),
        PrimitiveTypeFamily::Float => bare_path("float"),
        PrimitiveTypeFamily::Bool => bare_path("bool"),
        PrimitiveTypeFamily::Unit => bare_path("unit"),
        PrimitiveTypeFamily::Str => std_path("str", "str"),
        PrimitiveTypeFamily::List => std_path("list", "list"),
        PrimitiveTypeFamily::ListView => std_path("list", "list_view"),
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
