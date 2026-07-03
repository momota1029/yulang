//! Host act manifest generation from compiled declarations.
//!
//! The source of truth is the compiled namespace plus lowering metadata. This
//! module does not classify use sites and does not influence type inference.

use std::collections::{BTreeMap, BTreeSet};

use poly::dump::format_scheme;
use poly::host_manifest::{
    HostActManifest, HostActManifestAct, HostActManifestOperationInput, HostManifestError,
    HostOperationSurface, HostOperationTier,
};

use crate::{
    CompiledLoweringSurface, CompiledNamespaceSurface, CompiledNamespaceTypeKind,
    CompiledTypedIndex, CompiledTypedSurface,
};

const RAW_COMPAT_OVERRIDES: &[(&str, &str)] = &[
    ("std.io.file.file", "read_at"),
    ("std.io.file.file", "write_at"),
];

pub fn host_act_manifest_from_compiled(
    namespace: &CompiledNamespaceSurface,
    lowering: &CompiledLoweringSurface,
    typed: &CompiledTypedSurface,
) -> Result<HostActManifest, HostActManifestBuildError> {
    host_act_manifest_from_compiled_with_raw_compat_overrides(
        namespace,
        lowering,
        typed,
        RAW_COMPAT_OVERRIDES,
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostActManifestBuildError {
    MissingHostOperationScheme {
        act_id: String,
        operation_id: String,
    },
    Manifest(HostManifestError),
}

impl From<HostManifestError> for HostActManifestBuildError {
    fn from(error: HostManifestError) -> Self {
        Self::Manifest(error)
    }
}

fn host_act_manifest_from_compiled_with_raw_compat_overrides(
    namespace: &CompiledNamespaceSurface,
    lowering: &CompiledLoweringSurface,
    typed: &CompiledTypedSurface,
    raw_compat_overrides: &[(&str, &str)],
) -> Result<HostActManifest, HostActManifestBuildError> {
    let host_acts = host_act_map(namespace);
    let acts = host_acts
        .values()
        .map(|act| HostActManifestAct {
            act_id: act.act_id.clone(),
            path: act.path.clone(),
        })
        .collect::<Vec<_>>();

    let raw_compat = raw_compat_set(raw_compat_overrides);
    let typed_index = CompiledTypedIndex::new(typed);
    let type_arena = typed.types.to_type_arena();

    let mut operations = Vec::new();
    for op in &lowering.act_operations {
        let Some(act) = host_acts.get(&op.type_symbol) else {
            continue;
        };
        let operation_id = op.name.clone();
        let raw_key = (act.act_id.clone(), operation_id.clone());
        let surface = if raw_compat.contains(&raw_key) {
            HostOperationSurface::RawCompat
        } else {
            HostOperationSurface::Contract
        };
        let Some(value_symbol) = op.value_symbol else {
            return Err(HostActManifestBuildError::MissingHostOperationScheme {
                act_id: act.act_id.clone(),
                operation_id,
            });
        };
        let Some(scheme) = typed_index.value_scheme(value_symbol) else {
            return Err(HostActManifestBuildError::MissingHostOperationScheme {
                act_id: act.act_id.clone(),
                operation_id,
            });
        };
        let mut path = act.path.clone();
        path.push(op.name.clone());
        operations.push(HostActManifestOperationInput {
            act_id: act.act_id.clone(),
            operation_id: op.name.clone(),
            path,
            tier: HostOperationTier::Sync,
            surface,
            signature: format_scheme(&type_arena, scheme),
        });
    }

    HostActManifest::new(acts, operations).map_err(Into::into)
}

fn host_act_map(namespace: &CompiledNamespaceSurface) -> BTreeMap<u32, HostActDecl> {
    namespace
        .types
        .iter()
        .filter(|ty| ty.kind == CompiledNamespaceTypeKind::Act && ty.host)
        .map(|ty| {
            (
                ty.unit_id,
                HostActDecl {
                    act_id: ty.path.join("."),
                    path: ty.path.clone(),
                },
            )
        })
        .collect()
}

fn raw_compat_set(overrides: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    overrides
        .iter()
        .map(|(act_id, operation_id)| ((*act_id).to_string(), (*operation_id).to_string()))
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct HostActDecl {
    act_id: String,
    path: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompiledLoweringActOperationSignature, CompiledNamespaceTypeSymbol, CompiledTypeArena,
        CompiledTypedValueScheme,
    };
    use poly::types::{Pos, Scheme, TypeArena};

    #[test]
    fn includes_host_acts_and_excludes_regular_acts() {
        let namespace = namespace_with_types(vec![
            type_symbol(0, &["test", "host", "file"], true),
            type_symbol(1, &["test", "regular", "act"], false),
        ]);
        let lowering = lowering_with_ops(vec![
            act_op(0, &["test", "host", "file"], "load", 10),
            act_op(1, &["test", "regular", "act"], "ignored", 11),
        ]);
        let typed = typed_with_unit_schemes([10, 11]);

        let manifest = host_act_manifest_from_compiled_with_raw_compat_overrides(
            &namespace,
            &lowering,
            &typed,
            &[],
        )
        .unwrap();

        assert_eq!(manifest.acts.len(), 1);
        assert_eq!(manifest.acts[0].act_id, "test.host.file");
        assert_eq!(manifest.operations.len(), 1);
        assert_eq!(manifest.operations[0].operation_id, "load");
        assert_eq!(manifest.operations[0].signature, "()");
    }

    #[test]
    fn applies_raw_compat_overrides_to_matching_operations_only() {
        let namespace = namespace_with_types(vec![type_symbol(0, &["test", "host", "file"], true)]);
        let typed = typed_with_unit_schemes([10]);
        let ok_lowering =
            lowering_with_ops(vec![act_op(0, &["test", "host", "file"], "read_at", 10)]);
        let manifest = host_act_manifest_from_compiled_with_raw_compat_overrides(
            &namespace,
            &ok_lowering,
            &typed,
            &[("test.host.file", "read_at")],
        )
        .unwrap();
        assert_eq!(
            manifest.operations[0].surface,
            HostOperationSurface::RawCompat
        );

        let manifest = host_act_manifest_from_compiled_with_raw_compat_overrides(
            &namespace,
            &ok_lowering,
            &typed,
            &[("test.host.file", "write_at")],
        )
        .unwrap();
        assert_eq!(
            manifest.operations[0].surface,
            HostOperationSurface::Contract
        );
    }

    fn namespace_with_types(types: Vec<CompiledNamespaceTypeSymbol>) -> CompiledNamespaceSurface {
        CompiledNamespaceSurface {
            modules: Vec::new(),
            values: Vec::new(),
            types,
        }
    }

    fn type_symbol(unit_id: u32, path: &[&str], host: bool) -> CompiledNamespaceTypeSymbol {
        CompiledNamespaceTypeSymbol {
            unit_id,
            path: path.iter().map(|segment| (*segment).to_string()).collect(),
            kind: CompiledNamespaceTypeKind::Act,
            host,
        }
    }

    fn lowering_with_ops(
        act_operations: Vec<CompiledLoweringActOperationSignature>,
    ) -> CompiledLoweringSurface {
        CompiledLoweringSurface {
            act_operations,
            ..CompiledLoweringSurface::default()
        }
    }

    fn act_op(
        type_symbol: u32,
        type_path: &[&str],
        name: &str,
        value_symbol: u32,
    ) -> CompiledLoweringActOperationSignature {
        CompiledLoweringActOperationSignature {
            type_symbol,
            type_path: type_path
                .iter()
                .map(|segment| (*segment).to_string())
                .collect(),
            source_def: None,
            value_symbol: Some(value_symbol),
            value_path: None,
            name: name.to_string(),
            signature: None,
        }
    }

    fn typed_with_unit_schemes<const N: usize>(symbols: [u32; N]) -> CompiledTypedSurface {
        let mut types = TypeArena::new();
        let unit = types.alloc_pos(Pos::Con(vec!["unit".into()], Vec::new()));
        let scheme = Scheme {
            quantifiers: Vec::new(),
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate: unit,
        };
        CompiledTypedSurface {
            types: CompiledTypeArena::from_type_arena(&types),
            values: symbols
                .into_iter()
                .map(|symbol| CompiledTypedValueScheme {
                    symbol,
                    scheme: scheme.clone(),
                })
                .collect(),
        }
    }
}
