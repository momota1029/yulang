use poly::expr::{Def, Vis};
use poly::types::{Neg, Neu, Pos, Scheme, TypeArena};
use serde::{Deserialize, Serialize};
use sources::{Name, Path};

use crate::lowering::BodyLowering;
use crate::{CompiledNamespaceSurface, CompiledNamespaceVisibility};

#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledTypedSurface {
    pub types: CompiledTypeArena,
    pub values: Vec<CompiledTypedValueScheme>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledTypeArena {
    pub pos: Vec<Pos>,
    pub neg: Vec<Neg>,
    pub neu: Vec<Neu>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledTypedValueScheme {
    pub symbol: u32,
    pub scheme: Scheme,
}

impl CompiledTypedSurface {
    pub fn from_lowering(lowering: &BodyLowering, namespace: &CompiledNamespaceSurface) -> Self {
        let mut values = Vec::new();
        for module in &namespace.modules {
            let Some(live_module) = lowering
                .modules
                .module_by_path(&path_from_strings(&module.path))
            else {
                continue;
            };
            for value in module
                .values
                .iter()
                .filter(|value| value.visibility != CompiledNamespaceVisibility::My)
            {
                let name = Name(value.name.clone());
                let Some(def) = lowering
                    .modules
                    .value_decls(live_module, &name)
                    .into_iter()
                    .find(|decl| decl.order.index() == value.order)
                    .map(|decl| decl.def)
                else {
                    continue;
                };
                let Some(Def::Let {
                    vis,
                    scheme: Some(scheme),
                    ..
                }) = lowering.session.poly.defs.get(def)
                else {
                    continue;
                };
                if *vis == Vis::My {
                    continue;
                }
                values.push(CompiledTypedValueScheme {
                    symbol: value.symbol,
                    scheme: scheme.clone(),
                });
            }
        }
        values.sort_by_key(|value| value.symbol);
        Self {
            types: CompiledTypeArena::from_type_arena(lowering.session.infer.constraints().types()),
            values,
        }
    }
}

impl CompiledTypeArena {
    pub fn from_type_arena(types: &TypeArena) -> Self {
        Self {
            pos: types.pos_nodes().to_vec(),
            neg: types.neg_nodes().to_vec(),
            neu: types.neu_nodes().to_vec(),
        }
    }
}

fn path_from_strings(path: &[String]) -> Path {
    Path {
        segments: path.iter().cloned().map(Name).collect(),
    }
}

#[cfg(test)]
mod tests {
    use sources::SourceFile;

    use crate::lowering::lower_loaded_files;

    use super::*;

    #[test]
    fn typed_surface_records_exported_value_schemes_by_namespace_symbol() {
        let loaded = sources::load(vec![
            source(&[], "mod ops;\npub use ops::*\n"),
            source(&["ops"], "pub x = 42\nmy hidden = 0\n"),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let typed = CompiledTypedSurface::from_lowering(&lowering, &namespace);
        let ops = namespace
            .modules
            .iter()
            .find(|module| module.path == ["ops".to_string()])
            .unwrap();
        let x = ops.values.iter().find(|value| value.name == "x").unwrap();
        let hidden = ops
            .values
            .iter()
            .find(|value| value.name == "hidden")
            .unwrap();

        assert!(typed.values.iter().any(|value| value.symbol == x.symbol));
        assert!(
            !typed
                .values
                .iter()
                .any(|value| value.symbol == hidden.symbol)
        );
    }

    fn source(module: &[&str], text: &str) -> SourceFile {
        SourceFile {
            module_path: Path {
                segments: module
                    .iter()
                    .map(|segment| Name((*segment).to_string()))
                    .collect(),
            },
            source: text.to_string(),
        }
    }
}
