use std::collections::HashMap;

use yulang_core_ir as core_ir;

use crate::symbols::{Name, Path};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PrimitiveTypeFamily {
    List,
    ListView,
    Str,
    Range,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PrimitiveValueFamily {
    ListIndexRaw,
    StrConcat,
}

#[derive(Debug, Clone)]
pub(crate) struct PrimitivePathTable {
    source_types: HashMap<PrimitiveTypeFamily, Path>,
    source_type_aliases: HashMap<String, PrimitiveTypeFamily>,
    runtime_values: HashMap<PrimitiveValueFamily, core_ir::Path>,
}

impl PrimitivePathTable {
    pub(crate) fn standard() -> Self {
        let mut source_types = HashMap::new();
        for family in [
            PrimitiveTypeFamily::List,
            PrimitiveTypeFamily::ListView,
            PrimitiveTypeFamily::Str,
            PrimitiveTypeFamily::Range,
        ] {
            source_types.insert(family, standard_source_type_path(family));
        }

        let mut source_type_aliases = HashMap::new();
        source_type_aliases.insert("list".to_string(), PrimitiveTypeFamily::List);
        source_type_aliases.insert("list_view".to_string(), PrimitiveTypeFamily::ListView);
        source_type_aliases.insert("str".to_string(), PrimitiveTypeFamily::Str);
        source_type_aliases.insert("string".to_string(), PrimitiveTypeFamily::Str);
        source_type_aliases.insert("range".to_string(), PrimitiveTypeFamily::Range);

        let mut runtime_values = HashMap::new();
        for family in [
            PrimitiveValueFamily::ListIndexRaw,
            PrimitiveValueFamily::StrConcat,
        ] {
            runtime_values.insert(family, standard_runtime_value_path(family));
        }

        Self {
            source_types,
            source_type_aliases,
            runtime_values,
        }
    }

    pub(crate) fn source_type_path_by_name(&self, name: &str) -> Path {
        self.source_type_aliases
            .get(name)
            .and_then(|family| self.source_type_path(*family))
            .unwrap_or_else(|| Path {
                segments: vec![Name(name.to_string())],
            })
    }

    pub(crate) fn runtime_type_path_by_name(&self, name: &str) -> core_ir::Path {
        runtime_path(self.source_type_path_by_name(name))
    }

    pub(crate) fn canonical_builtin_type_path(&self, path: &Path) -> Option<Path> {
        let [name] = path.segments.as_slice() else {
            return None;
        };
        self.source_type_aliases
            .get(&name.0)
            .and_then(|family| self.source_type_path(*family))
    }

    pub(crate) fn source_type_path(&self, family: PrimitiveTypeFamily) -> Option<Path> {
        self.source_types.get(&family).cloned()
    }

    pub(crate) fn runtime_value_path(&self, family: PrimitiveValueFamily) -> Option<core_ir::Path> {
        self.runtime_values.get(&family).cloned()
    }
}

impl Default for PrimitivePathTable {
    fn default() -> Self {
        Self::standard()
    }
}

pub(crate) fn builtin_source_type_path(name: &str) -> Path {
    PrimitivePathTable::standard().source_type_path_by_name(name)
}

pub(crate) fn builtin_runtime_type_path(name: &str) -> core_ir::Path {
    PrimitivePathTable::standard().runtime_type_path_by_name(name)
}

pub(crate) fn canonical_builtin_type_path(path: &Path) -> Option<Path> {
    PrimitivePathTable::standard().canonical_builtin_type_path(path)
}

pub(crate) fn primitive_runtime_value_path(family: PrimitiveValueFamily) -> core_ir::Path {
    standard_runtime_value_path(family)
}

fn standard_source_type_path(family: PrimitiveTypeFamily) -> Path {
    let (module, type_name) = primitive_std_type_segments(family);
    Path {
        segments: vec![
            Name("std".to_string()),
            Name(module.to_string()),
            Name(type_name.to_string()),
        ],
    }
}

fn standard_runtime_value_path(family: PrimitiveValueFamily) -> core_ir::Path {
    let (module, value_name) = primitive_std_value_segments(family);
    core_ir::Path::new(vec![
        core_ir::Name("std".to_string()),
        core_ir::Name(module.to_string()),
        core_ir::Name(value_name.to_string()),
    ])
}

fn primitive_std_type_segments(family: PrimitiveTypeFamily) -> (&'static str, &'static str) {
    match family {
        PrimitiveTypeFamily::List => ("list", "list"),
        PrimitiveTypeFamily::ListView => ("list", "list_view"),
        PrimitiveTypeFamily::Str => ("str", "str"),
        PrimitiveTypeFamily::Range => ("range", "range"),
    }
}

fn primitive_std_value_segments(family: PrimitiveValueFamily) -> (&'static str, &'static str) {
    match family {
        PrimitiveValueFamily::ListIndexRaw => ("list", "index_raw"),
        PrimitiveValueFamily::StrConcat => ("str", "concat"),
    }
}

fn runtime_path(path: Path) -> core_ir::Path {
    core_ir::Path {
        segments: path
            .segments
            .into_iter()
            .map(|segment| core_ir::Name(segment.0))
            .collect(),
    }
}
