use std::collections::HashMap;

use yulang_typed_ir as typed_ir;

use crate::symbols::{Name, Path};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PrimitiveTypeFamily {
    List,
    ListView,
    Str,
    Char,
    Range,
    Bytes,
    Path,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PrimitiveValueFamily {
    ListIndexRaw,
    StrConcat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PrimitiveNumericTypeFamily {
    Int,
    Frac,
    Float,
}

impl PrimitiveNumericTypeFamily {
    fn rank(self) -> u8 {
        match self {
            Self::Int => 0,
            Self::Frac => 1,
            Self::Float => 2,
        }
    }

    fn from_rank(rank: u8) -> Option<Self> {
        match rank {
            0 => Some(Self::Int),
            1 => Some(Self::Frac),
            2 => Some(Self::Float),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct PrimitivePathTable {
    source_types: HashMap<PrimitiveTypeFamily, Path>,
    source_type_aliases: HashMap<String, PrimitiveTypeFamily>,
    runtime_values: HashMap<PrimitiveValueFamily, typed_ir::Path>,
}

impl PrimitivePathTable {
    pub(crate) fn standard() -> Self {
        let mut source_types = HashMap::new();
        for family in [
            PrimitiveTypeFamily::List,
            PrimitiveTypeFamily::ListView,
            PrimitiveTypeFamily::Str,
            PrimitiveTypeFamily::Char,
            PrimitiveTypeFamily::Range,
            PrimitiveTypeFamily::Bytes,
            PrimitiveTypeFamily::Path,
        ] {
            source_types.insert(family, standard_source_type_path(family));
        }

        let mut source_type_aliases = HashMap::new();
        source_type_aliases.insert("list".to_string(), PrimitiveTypeFamily::List);
        source_type_aliases.insert("list_view".to_string(), PrimitiveTypeFamily::ListView);
        source_type_aliases.insert("str".to_string(), PrimitiveTypeFamily::Str);
        source_type_aliases.insert("string".to_string(), PrimitiveTypeFamily::Str);
        source_type_aliases.insert("char".to_string(), PrimitiveTypeFamily::Char);
        source_type_aliases.insert("range".to_string(), PrimitiveTypeFamily::Range);
        source_type_aliases.insert("bytes".to_string(), PrimitiveTypeFamily::Bytes);
        source_type_aliases.insert("path".to_string(), PrimitiveTypeFamily::Path);

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

    pub(crate) fn runtime_type_path_by_name(&self, name: &str) -> typed_ir::Path {
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

    pub(crate) fn runtime_value_path(
        &self,
        family: PrimitiveValueFamily,
    ) -> Option<typed_ir::Path> {
        self.runtime_values.get(&family).cloned()
    }

    pub(crate) fn export_core_type_nodes(&self) -> Vec<typed_ir::PrimitiveTypeGraphNode> {
        let mut nodes = vec![
            core_primitive_type_node(typed_ir::PrimitiveTypeFamily::Int, bare_runtime_path("int")),
            core_primitive_type_node(
                typed_ir::PrimitiveTypeFamily::Frac,
                runtime_path(primitive_numeric_type_path(
                    PrimitiveNumericTypeFamily::Frac,
                )),
            ),
            core_primitive_type_node(
                typed_ir::PrimitiveTypeFamily::Float,
                bare_runtime_path("float"),
            ),
            core_primitive_type_node(
                typed_ir::PrimitiveTypeFamily::Bool,
                bare_runtime_path("bool"),
            ),
            core_primitive_type_node(
                typed_ir::PrimitiveTypeFamily::Unit,
                bare_runtime_path("unit"),
            ),
        ];
        nodes.extend([
            self.core_type_node(PrimitiveTypeFamily::Str, typed_ir::PrimitiveTypeFamily::Str),
            self.core_type_node(
                PrimitiveTypeFamily::Char,
                typed_ir::PrimitiveTypeFamily::Char,
            ),
            self.core_type_node(
                PrimitiveTypeFamily::List,
                typed_ir::PrimitiveTypeFamily::List,
            ),
            self.core_type_node(
                PrimitiveTypeFamily::ListView,
                typed_ir::PrimitiveTypeFamily::ListView,
            ),
            self.core_type_node(
                PrimitiveTypeFamily::Range,
                typed_ir::PrimitiveTypeFamily::Range,
            ),
            self.core_type_node(
                PrimitiveTypeFamily::Bytes,
                typed_ir::PrimitiveTypeFamily::Bytes,
            ),
            self.core_type_node(
                PrimitiveTypeFamily::Path,
                typed_ir::PrimitiveTypeFamily::Path,
            ),
        ]);
        nodes
    }

    fn core_type_node(
        &self,
        source_family: PrimitiveTypeFamily,
        core_family: typed_ir::PrimitiveTypeFamily,
    ) -> typed_ir::PrimitiveTypeGraphNode {
        let path = self
            .source_type_path(source_family)
            .map(runtime_path)
            .unwrap_or_else(|| runtime_path(standard_source_type_path(source_family)));
        core_primitive_type_node(core_family, path)
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

pub(crate) fn builtin_runtime_type_path(name: &str) -> typed_ir::Path {
    PrimitivePathTable::standard().runtime_type_path_by_name(name)
}

pub(crate) fn canonical_builtin_type_path(path: &Path) -> Option<Path> {
    PrimitivePathTable::standard().canonical_builtin_type_path(path)
}

pub(crate) fn primitive_numeric_type_family(path: &Path) -> Option<PrimitiveNumericTypeFamily> {
    match path.segments.as_slice() {
        [Name(name)] if name == "int" => Some(PrimitiveNumericTypeFamily::Int),
        [Name(std), Name(module), Name(name)]
            if std == "std" && module == "int" && name == "int" =>
        {
            Some(PrimitiveNumericTypeFamily::Int)
        }
        [Name(name)] if name == "float" => Some(PrimitiveNumericTypeFamily::Float),
        [Name(std), Name(module), Name(name)]
            if std == "std" && module == "float" && name == "float" =>
        {
            Some(PrimitiveNumericTypeFamily::Float)
        }
        [Name(std), Name(module), Name(name)]
            if std == "std" && module == "frac" && name == "frac" =>
        {
            Some(PrimitiveNumericTypeFamily::Frac)
        }
        _ => None,
    }
}

pub(crate) fn primitive_type_family(path: &Path) -> Option<PrimitiveTypeFamily> {
    let canonical = canonical_builtin_type_path(path).unwrap_or_else(|| path.clone());
    match canonical.segments.as_slice() {
        [Name(std), Name(module), Name(name)]
            if std == "std" && module == "str" && name == "str" =>
        {
            Some(PrimitiveTypeFamily::Str)
        }
        [Name(std), Name(module), Name(name)]
            if std == "std" && module == "path" && name == "path" =>
        {
            Some(PrimitiveTypeFamily::Path)
        }
        _ => None,
    }
}

pub(crate) fn join_primitive_numeric_type_paths(left: &Path, right: &Path) -> Option<Path> {
    let left = primitive_numeric_type_family(left)?;
    let right = primitive_numeric_type_family(right)?;
    let family = PrimitiveNumericTypeFamily::from_rank(left.rank().max(right.rank()))?;
    Some(primitive_numeric_type_path(family))
}

pub(crate) fn join_primitive_type_paths(left: &Path, right: &Path) -> Option<Path> {
    if let Some(joined) = join_primitive_numeric_type_paths(left, right) {
        return Some(joined);
    }
    match (primitive_type_family(left)?, primitive_type_family(right)?) {
        (PrimitiveTypeFamily::Str, PrimitiveTypeFamily::Path)
        | (PrimitiveTypeFamily::Path, PrimitiveTypeFamily::Str) => {
            Some(standard_source_type_path(PrimitiveTypeFamily::Path))
        }
        _ => None,
    }
}

pub(crate) fn primitive_numeric_type_path(family: PrimitiveNumericTypeFamily) -> Path {
    match family {
        PrimitiveNumericTypeFamily::Int => Path {
            segments: vec![Name("int".to_string())],
        },
        PrimitiveNumericTypeFamily::Frac => Path {
            segments: vec![
                Name("std".to_string()),
                Name("frac".to_string()),
                Name("frac".to_string()),
            ],
        },
        PrimitiveNumericTypeFamily::Float => Path {
            segments: vec![Name("float".to_string())],
        },
    }
}

pub(crate) fn can_widen_primitive_numeric_type_paths(actual: &Path, expected: &Path) -> bool {
    let Some(actual) = primitive_numeric_type_family(actual) else {
        return false;
    };
    let Some(expected) = primitive_numeric_type_family(expected) else {
        return false;
    };
    actual.rank() <= expected.rank()
}

pub(crate) fn can_widen_primitive_type_paths(actual: &Path, expected: &Path) -> bool {
    can_widen_primitive_numeric_type_paths(actual, expected)
        || matches!(
            (
                primitive_type_family(actual),
                primitive_type_family(expected)
            ),
            (
                Some(PrimitiveTypeFamily::Str),
                Some(PrimitiveTypeFamily::Path)
            )
        )
}

pub(crate) fn can_runtime_coerce_primitive_type_paths(actual: &Path, expected: &Path) -> bool {
    matches!(
        (
            primitive_numeric_type_family(actual),
            primitive_numeric_type_family(expected)
        ),
        (
            Some(PrimitiveNumericTypeFamily::Int),
            Some(PrimitiveNumericTypeFamily::Float)
        )
    ) || matches!(
        (
            primitive_type_family(actual),
            primitive_type_family(expected)
        ),
        (
            Some(PrimitiveTypeFamily::Str),
            Some(PrimitiveTypeFamily::Path)
        )
    )
}

pub(crate) fn primitive_runtime_value_path(family: PrimitiveValueFamily) -> typed_ir::Path {
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

fn standard_runtime_value_path(family: PrimitiveValueFamily) -> typed_ir::Path {
    let (module, value_name) = primitive_std_value_segments(family);
    typed_ir::Path::new(vec![
        typed_ir::Name("std".to_string()),
        typed_ir::Name(module.to_string()),
        typed_ir::Name(value_name.to_string()),
    ])
}

fn core_primitive_type_node(
    family: typed_ir::PrimitiveTypeFamily,
    path: typed_ir::Path,
) -> typed_ir::PrimitiveTypeGraphNode {
    typed_ir::PrimitiveTypeGraphNode { family, path }
}

fn bare_runtime_path(name: &str) -> typed_ir::Path {
    typed_ir::Path::from_name(typed_ir::Name(name.to_string()))
}

fn primitive_std_type_segments(family: PrimitiveTypeFamily) -> (&'static str, &'static str) {
    match family {
        PrimitiveTypeFamily::List => ("list", "list"),
        PrimitiveTypeFamily::ListView => ("list", "list_view"),
        PrimitiveTypeFamily::Str => ("str", "str"),
        PrimitiveTypeFamily::Char => ("char", "char"),
        PrimitiveTypeFamily::Range => ("range", "range"),
        PrimitiveTypeFamily::Bytes => ("bytes", "bytes"),
        PrimitiveTypeFamily::Path => ("path", "path"),
    }
}

fn primitive_std_value_segments(family: PrimitiveValueFamily) -> (&'static str, &'static str) {
    match family {
        PrimitiveValueFamily::ListIndexRaw => ("list", "index_raw"),
        PrimitiveValueFamily::StrConcat => ("str", "concat"),
    }
}

fn runtime_path(path: Path) -> typed_ir::Path {
    typed_ir::Path {
        segments: path
            .segments
            .into_iter()
            .map(|segment| typed_ir::Name(segment.0))
            .collect(),
    }
}
