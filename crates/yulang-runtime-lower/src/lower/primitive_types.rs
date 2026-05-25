use super::*;
use std::collections::HashMap;

type PrimitiveTypeFamily = typed_ir::PrimitiveTypeFamily;

#[derive(Debug, Clone)]
pub(super) struct RuntimePrimitivePathTable {
    types: HashMap<PrimitiveTypeFamily, typed_ir::Path>,
    type_order: typed_ir::PrimitiveTypeOrder,
}

impl RuntimePrimitivePathTable {
    pub(super) fn standard() -> Self {
        let mut types = HashMap::new();
        for family in [
            PrimitiveTypeFamily::Int,
            PrimitiveTypeFamily::Frac,
            PrimitiveTypeFamily::Float,
            PrimitiveTypeFamily::Bool,
            PrimitiveTypeFamily::Unit,
            PrimitiveTypeFamily::Str,
            PrimitiveTypeFamily::Char,
            PrimitiveTypeFamily::List,
            PrimitiveTypeFamily::ListView,
            PrimitiveTypeFamily::Range,
            PrimitiveTypeFamily::Bytes,
            PrimitiveTypeFamily::Path,
        ] {
            types.insert(family, standard_primitive_type_path(family));
        }
        Self {
            types,
            type_order: typed_ir::PrimitiveTypeOrder::standard(),
        }
    }

    pub(super) fn from_graph(graph: &typed_ir::CoreGraphView) -> Self {
        let mut table = Self::standard();
        for node in &graph.primitive_types {
            table.types.insert(node.family, node.path.clone());
        }
        table.type_order =
            typed_ir::PrimitiveTypeOrder::from_primitive_types(&graph.primitive_types);
        table
    }

    pub(super) fn lit_type(&self, lit: &typed_ir::Lit) -> typed_ir::Type {
        let family = match lit {
            typed_ir::Lit::Int(_) => PrimitiveTypeFamily::Int,
            typed_ir::Lit::Float(_) => PrimitiveTypeFamily::Float,
            typed_ir::Lit::String(_) => PrimitiveTypeFamily::Str,
            typed_ir::Lit::Bool(_) => PrimitiveTypeFamily::Bool,
            typed_ir::Lit::Unit => PrimitiveTypeFamily::Unit,
        };
        self.primitive_type(family, Vec::new())
    }

    pub(super) fn bool_type(&self) -> typed_ir::Type {
        self.primitive_type(PrimitiveTypeFamily::Bool, Vec::new())
    }

    pub(super) fn unit_type(&self) -> typed_ir::Type {
        self.primitive_type(PrimitiveTypeFamily::Unit, Vec::new())
    }

    pub(super) fn primitive_type(
        &self,
        family: PrimitiveTypeFamily,
        args: Vec<typed_ir::TypeArg>,
    ) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: self.primitive_type_path(family),
            args,
        }
    }

    pub(super) fn needs_runtime_coercion(
        &self,
        expected: &typed_ir::Type,
        actual: &typed_ir::Type,
    ) -> bool {
        yulang_runtime_types::types::needs_runtime_coercion_with_order(&self.type_order, expected, actual)
    }

    fn primitive_type_path(&self, family: PrimitiveTypeFamily) -> typed_ir::Path {
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
pub(super) fn bool_type() -> typed_ir::Type {
    RuntimePrimitivePathTable::standard().bool_type()
}

#[cfg(test)]
pub(super) fn unit_type() -> typed_ir::Type {
    RuntimePrimitivePathTable::standard().unit_type()
}

fn standard_primitive_type_path(family: PrimitiveTypeFamily) -> typed_ir::Path {
    match family {
        PrimitiveTypeFamily::Int => bare_path("int"),
        PrimitiveTypeFamily::Frac => std_path("frac", "frac"),
        PrimitiveTypeFamily::Float => bare_path("float"),
        PrimitiveTypeFamily::Bool => bare_path("bool"),
        PrimitiveTypeFamily::Unit => bare_path("unit"),
        PrimitiveTypeFamily::Str => std_path("str", "str"),
        PrimitiveTypeFamily::Char => std_path("char", "char"),
        PrimitiveTypeFamily::List => std_path("list", "list"),
        PrimitiveTypeFamily::ListView => std_path("list", "list_view"),
        PrimitiveTypeFamily::Range => std_path("range", "range"),
        PrimitiveTypeFamily::Bytes => std_path("bytes", "bytes"),
        PrimitiveTypeFamily::Path => std_path("path", "path"),
    }
}

#[cfg(test)]
pub(super) fn named_type(name: &str) -> typed_ir::Type {
    typed_ir::Type::Named {
        path: bare_path(name),
        args: Vec::new(),
    }
}

fn bare_path(name: &str) -> typed_ir::Path {
    typed_ir::Path::from_name(typed_ir::Name(name.to_string()))
}

fn std_path(module: &str, name: &str) -> typed_ir::Path {
    typed_ir::Path::new(vec![
        typed_ir::Name("std".to_string()),
        typed_ir::Name(module.to_string()),
        typed_ir::Name(name.to_string()),
    ])
}
