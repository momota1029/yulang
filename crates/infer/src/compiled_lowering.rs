use poly::expr::DefId;
use poly::types::BuiltinType;
use serde::{Deserialize, Serialize};
use sources::{Name, Path};

use crate::lowering::{self, SignatureEffectAtom, SignatureEffectRow, SignatureType, SignatureVar};
use crate::{
    CompiledNamespaceSurface, CompiledNamespaceTypeKind, ConstructorPayload,
    ConstructorPayloadItem, ConstructorRecordPayloadField, ModuleTable, ModuleTypeDecl,
    ModuleTypeKind, RoleMethodDecl, StoredSignature, TypeDeclId, namespace_path,
};

/// Lowering-time metadata exported by a compiled unit.
///
/// Namespace and typed surfaces are enough for name lookup and imported value
/// schemes. Some downstream lowering rules also need declaration metadata that
/// is not part of the final poly arena. This surface keeps that information
/// structured so cached dependencies do not have to expose source CST just to
/// recover it.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringSurface {
    pub act_type_vars: Vec<CompiledLoweringActTypeVars>,
    pub constructor_payloads: Vec<CompiledLoweringConstructorPayload>,
    pub act_operations: Vec<CompiledLoweringActOperationSignature>,
    pub role_methods: Vec<CompiledLoweringRoleMethodSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringActTypeVars {
    pub type_symbol: u32,
    pub type_path: Vec<String>,
    pub vars: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringConstructorPayload {
    pub value_symbol: u32,
    pub value_path: Vec<String>,
    pub payload: CompiledConstructorPayload,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompiledConstructorPayload {
    Unit,
    Tuple(Vec<Option<CompiledSignatureType>>),
    Record(Vec<CompiledConstructorRecordPayloadField>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledConstructorRecordPayloadField {
    pub name: String,
    pub ty: Option<CompiledSignatureType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringActOperationSignature {
    pub type_symbol: u32,
    pub type_path: Vec<String>,
    pub name: String,
    pub signature: Option<CompiledSignatureType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringRoleMethodSignature {
    pub type_symbol: u32,
    pub type_path: Vec<String>,
    pub name: String,
    pub order: u32,
    pub signature: Option<CompiledSignatureType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompiledSignatureType {
    Builtin(BuiltinType),
    Named(Vec<String>),
    Var(String),
    EffectRow(CompiledSignatureEffectRow),
    Effectful {
        eff: CompiledSignatureEffectRow,
        ret: Box<CompiledSignatureType>,
    },
    Tuple(Vec<CompiledSignatureType>),
    Apply {
        callee: Box<CompiledSignatureType>,
        args: Vec<CompiledSignatureType>,
    },
    Function {
        param: Box<CompiledSignatureType>,
        arg_eff: Option<CompiledSignatureEffectRow>,
        ret_eff: Option<CompiledSignatureEffectRow>,
        ret: Box<CompiledSignatureType>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSignatureEffectRow {
    pub items: Vec<CompiledSignatureEffectAtom>,
    pub tail: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompiledSignatureEffectAtom {
    Type(CompiledSignatureType),
    Wildcard,
}

impl CompiledLoweringSurface {
    pub fn from_module_table(modules: &ModuleTable, namespace: &CompiledNamespaceSurface) -> Self {
        let mut act_type_vars = namespace
            .types
            .iter()
            .filter(|ty| ty.kind == CompiledNamespaceTypeKind::Act)
            .filter_map(|ty| {
                let decl = type_decl_for_namespace_path(modules, &ty.path)?;
                if decl.kind != ModuleTypeKind::Act {
                    return None;
                }
                let vars = modules.act_type_vars(decl.id)?.to_vec();
                Some(CompiledLoweringActTypeVars {
                    type_symbol: ty.unit_id,
                    type_path: ty.path.clone(),
                    vars,
                })
            })
            .collect::<Vec<_>>();
        act_type_vars.sort_by_key(|entry| entry.type_symbol);

        let mut constructor_payloads = namespace
            .values
            .iter()
            .filter_map(|value| {
                let def = value_def_for_namespace_symbol(modules, namespace, value.unit_id)?;
                let constructor = modules.constructor_by_def(def)?;
                Some(CompiledLoweringConstructorPayload {
                    value_symbol: value.unit_id,
                    value_path: value.path.clone(),
                    payload: compile_constructor_payload(modules, constructor)?,
                })
            })
            .collect::<Vec<_>>();
        constructor_payloads.sort_by_key(|entry| entry.value_symbol);

        let mut act_operations = namespace
            .types
            .iter()
            .filter(|ty| {
                matches!(
                    ty.kind,
                    CompiledNamespaceTypeKind::Act | CompiledNamespaceTypeKind::Error
                )
            })
            .filter_map(|ty| {
                let decl = type_decl_for_namespace_path(modules, &ty.path)?;
                if !matches!(decl.kind, ModuleTypeKind::Act | ModuleTypeKind::Error) {
                    return None;
                }
                let ops = modules.act_ops.get(&decl.id)?;
                Some(
                    ops.iter()
                        .filter_map(|op| {
                            Some(CompiledLoweringActOperationSignature {
                                type_symbol: ty.unit_id,
                                type_path: ty.path.clone(),
                                name: op.name.0.clone(),
                                signature: compile_act_operation_signature(
                                    modules,
                                    &decl,
                                    &op.signature,
                                )?,
                            })
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .flatten()
            .collect::<Vec<_>>();
        act_operations.sort_by(|left, right| {
            (left.type_symbol, &left.name).cmp(&(right.type_symbol, &right.name))
        });

        let mut role_methods = namespace
            .types
            .iter()
            .filter(|ty| ty.kind == CompiledNamespaceTypeKind::Role)
            .filter_map(|ty| {
                let decl = type_decl_for_namespace_path(modules, &ty.path)?;
                if decl.kind != ModuleTypeKind::Role {
                    return None;
                }
                Some(
                    modules
                        .role_methods(decl.id)
                        .iter()
                        .filter_map(|method| {
                            Some(CompiledLoweringRoleMethodSignature {
                                type_symbol: ty.unit_id,
                                type_path: ty.path.clone(),
                                name: method.name.0.clone(),
                                order: method.order.index(),
                                signature: compile_role_method_signature(modules, method)?,
                            })
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .flatten()
            .collect::<Vec<_>>();
        role_methods.sort_by(|left, right| {
            (left.type_symbol, left.order, &left.name).cmp(&(
                right.type_symbol,
                right.order,
                &right.name,
            ))
        });

        Self {
            act_type_vars,
            constructor_payloads,
            act_operations,
            role_methods,
        }
    }

    pub fn apply_to_module_table(&self, modules: &mut ModuleTable) {
        for entry in &self.act_type_vars {
            let Some(decl) = type_decl_for_namespace_path(modules, &entry.type_path) else {
                continue;
            };
            if decl.kind != ModuleTypeKind::Act {
                continue;
            }
            modules.set_act_type_vars(decl.id, entry.vars.clone());
        }

        for entry in &self.constructor_payloads {
            let Some(def) = value_def_for_namespace_path(modules, &entry.value_path) else {
                continue;
            };
            let Some(payload) = restore_constructor_payload(modules, &entry.payload) else {
                continue;
            };
            if let Some(constructor) = modules.constructors.get_mut(&def) {
                constructor.payload = payload;
            }
        }

        for entry in &self.act_operations {
            let Some(decl) = type_decl_for_namespace_path(modules, &entry.type_path) else {
                continue;
            };
            if !matches!(decl.kind, ModuleTypeKind::Act | ModuleTypeKind::Error) {
                continue;
            }
            let signature = restore_optional_stored_signature(modules, &entry.signature);
            if let Some(ops) = modules.act_ops.get_mut(&decl.id)
                && let Some(op) = ops.iter_mut().find(|op| op.name.0 == entry.name)
            {
                op.signature = signature;
            }
        }

        for entry in &self.role_methods {
            let Some(decl) = type_decl_for_namespace_path(modules, &entry.type_path) else {
                continue;
            };
            if decl.kind != ModuleTypeKind::Role {
                continue;
            }
            let signature = restore_optional_stored_signature(modules, &entry.signature);
            if let Some(methods) = modules.role_methods.get_mut(&decl.id)
                && let Some(method) = methods.iter_mut().find(|method| {
                    method.name.0 == entry.name && method.order.index() == entry.order
                })
            {
                method.signature = signature;
            }
        }
    }
}

fn compile_constructor_payload(
    modules: &ModuleTable,
    constructor: &crate::ConstructorDecl,
) -> Option<CompiledConstructorPayload> {
    match &constructor.payload {
        ConstructorPayload::Unit => Some(CompiledConstructorPayload::Unit),
        ConstructorPayload::Tuple(items) => items
            .iter()
            .map(|item| compile_constructor_payload_item(modules, constructor, item))
            .collect::<Option<Vec<_>>>()
            .map(CompiledConstructorPayload::Tuple),
        ConstructorPayload::Record(fields) => fields
            .iter()
            .map(|field| {
                Some(CompiledConstructorRecordPayloadField {
                    name: field.name.0.clone(),
                    ty: compile_optional_constructor_signature(
                        modules,
                        constructor,
                        field.ty.as_ref(),
                    )?,
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(CompiledConstructorPayload::Record),
    }
}

fn compile_constructor_payload_item(
    modules: &ModuleTable,
    constructor: &crate::ConstructorDecl,
    item: &ConstructorPayloadItem,
) -> Option<Option<CompiledSignatureType>> {
    compile_optional_constructor_signature(modules, constructor, item.ty.as_ref())
}

fn compile_optional_constructor_signature(
    modules: &ModuleTable,
    constructor: &crate::ConstructorDecl,
    signature: Option<&StoredSignature>,
) -> Option<Option<CompiledSignatureType>> {
    let Some(signature) = signature else {
        return Some(None);
    };
    let owner = modules.type_decl_by_id(constructor.owner)?;
    let lowered = lowering::lower_constructor_stored_signature_type_for_surface(
        modules,
        constructor.module,
        owner.order,
        constructor.owner,
        &constructor.type_vars,
        signature,
    )
    .ok()?;
    compile_signature_type(modules, &lowered).map(Some)
}

fn compile_act_operation_signature(
    modules: &ModuleTable,
    decl: &ModuleTypeDecl,
    signature: &Option<StoredSignature>,
) -> Option<Option<CompiledSignatureType>> {
    let Some(signature) = signature else {
        return Some(None);
    };
    let bare_type_vars = act_effect_type_var_names(modules, decl.id);
    let (type_var_aliases, type_name_aliases) = act_copy_aliases(modules, decl);
    let lowered = lowering::lower_stored_signature_type_for_surface(
        modules,
        decl.module,
        decl.order,
        signature,
        &bare_type_vars,
        &type_var_aliases,
        &type_name_aliases,
    )
    .ok()?;
    compile_signature_type(modules, &lowered).map(Some)
}

fn compile_role_method_signature(
    modules: &ModuleTable,
    method: &RoleMethodDecl,
) -> Option<Option<CompiledSignatureType>> {
    let Some(signature) = method.signature.as_ref() else {
        return Some(None);
    };
    let companion = modules.type_companion(method.owner)?;
    let role_inputs = modules.role_inputs(method.owner);
    let role_associated = modules.role_associated(method.owner);
    let bare_type_vars = role_inputs
        .iter()
        .chain(role_associated.iter())
        .cloned()
        .collect::<Vec<_>>();
    let type_var_aliases = role_inputs
        .first()
        .map(|first| vec![("self".to_string(), first.clone())])
        .unwrap_or_default();
    let lowered = lowering::lower_stored_signature_type_for_surface(
        modules,
        companion,
        method.order,
        signature,
        &bare_type_vars,
        &type_var_aliases,
        &[],
    )
    .ok()?;
    compile_signature_type(modules, &lowered).map(Some)
}

fn act_effect_type_var_names(modules: &ModuleTable, id: TypeDeclId) -> Vec<String> {
    if let Some(error) = modules.error_decl(id) {
        return error.type_vars.clone();
    }
    modules
        .act_type_vars(id)
        .map(|vars| vars.to_vec())
        .unwrap_or_default()
}

fn act_copy_aliases(
    modules: &ModuleTable,
    decl: &ModuleTypeDecl,
) -> (Vec<(String, String)>, Vec<(String, TypeDeclId)>) {
    let Some(copy) = modules.resolved_act_copy(decl.id) else {
        return (Vec::new(), Vec::new());
    };
    let type_name_aliases = modules
        .type_decl_by_id(copy.source)
        .map(|source| vec![(source.name.0, decl.id)])
        .unwrap_or_default();
    (copy.type_var_aliases.clone(), type_name_aliases)
}

fn restore_constructor_payload(
    modules: &ModuleTable,
    payload: &CompiledConstructorPayload,
) -> Option<ConstructorPayload> {
    match payload {
        CompiledConstructorPayload::Unit => Some(ConstructorPayload::Unit),
        CompiledConstructorPayload::Tuple(items) => items
            .iter()
            .map(|item| {
                Some(ConstructorPayloadItem {
                    ty: restore_optional_stored_signature(modules, item),
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(ConstructorPayload::Tuple),
        CompiledConstructorPayload::Record(fields) => fields
            .iter()
            .map(|field| {
                Some(ConstructorRecordPayloadField {
                    name: Name(field.name.clone()),
                    ty: restore_optional_stored_signature(modules, &field.ty),
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(ConstructorPayload::Record),
    }
}

fn restore_optional_stored_signature(
    modules: &ModuleTable,
    signature: &Option<CompiledSignatureType>,
) -> Option<StoredSignature> {
    signature
        .as_ref()
        .and_then(|signature| restore_signature_type(modules, signature))
        .map(StoredSignature::lowered)
}

fn compile_signature_type(
    modules: &ModuleTable,
    signature: &SignatureType,
) -> Option<CompiledSignatureType> {
    match signature {
        SignatureType::Builtin(builtin) => Some(CompiledSignatureType::Builtin(*builtin)),
        SignatureType::Named(id) => {
            let decl = modules.type_decl_by_id(*id)?;
            Some(CompiledSignatureType::Named(namespace_path(
                &modules.type_decl_path(&decl),
            )))
        }
        SignatureType::Var(var) => Some(CompiledSignatureType::Var(var.name().to_string())),
        SignatureType::EffectRow(row) => Some(CompiledSignatureType::EffectRow(
            compile_signature_effect_row(modules, row)?,
        )),
        SignatureType::Effectful { eff, ret } => Some(CompiledSignatureType::Effectful {
            eff: compile_signature_effect_row(modules, eff)?,
            ret: Box::new(compile_signature_type(modules, ret)?),
        }),
        SignatureType::Tuple(items) => items
            .iter()
            .map(|item| compile_signature_type(modules, item))
            .collect::<Option<Vec<_>>>()
            .map(CompiledSignatureType::Tuple),
        SignatureType::Apply { callee, args } => Some(CompiledSignatureType::Apply {
            callee: Box::new(compile_signature_type(modules, callee)?),
            args: args
                .iter()
                .map(|arg| compile_signature_type(modules, arg))
                .collect::<Option<Vec<_>>>()?,
        }),
        SignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => Some(CompiledSignatureType::Function {
            param: Box::new(compile_signature_type(modules, param)?),
            arg_eff: match arg_eff {
                Some(row) => Some(compile_signature_effect_row(modules, row)?),
                None => None,
            },
            ret_eff: match ret_eff {
                Some(row) => Some(compile_signature_effect_row(modules, row)?),
                None => None,
            },
            ret: Box::new(compile_signature_type(modules, ret)?),
        }),
    }
}

fn compile_signature_effect_row(
    modules: &ModuleTable,
    row: &SignatureEffectRow,
) -> Option<CompiledSignatureEffectRow> {
    Some(CompiledSignatureEffectRow {
        items: row
            .items()
            .iter()
            .map(|atom| match atom {
                SignatureEffectAtom::Type(ty) => Some(CompiledSignatureEffectAtom::Type(
                    compile_signature_type(modules, ty)?,
                )),
                SignatureEffectAtom::Wildcard => Some(CompiledSignatureEffectAtom::Wildcard),
            })
            .collect::<Option<Vec<_>>>()?,
        tail: row.tail().map(|tail| tail.name().to_string()),
    })
}

fn restore_signature_type(
    modules: &ModuleTable,
    signature: &CompiledSignatureType,
) -> Option<SignatureType> {
    match signature {
        CompiledSignatureType::Builtin(builtin) => Some(SignatureType::Builtin(*builtin)),
        CompiledSignatureType::Named(path) => {
            let decl = type_decl_for_namespace_path(modules, path)?;
            Some(SignatureType::Named(decl.id))
        }
        CompiledSignatureType::Var(name) => Some(SignatureType::Var(SignatureVar::new(name))),
        CompiledSignatureType::EffectRow(row) => Some(SignatureType::EffectRow(
            restore_signature_effect_row(modules, row)?,
        )),
        CompiledSignatureType::Effectful { eff, ret } => Some(SignatureType::Effectful {
            eff: restore_signature_effect_row(modules, eff)?,
            ret: Box::new(restore_signature_type(modules, ret)?),
        }),
        CompiledSignatureType::Tuple(items) => items
            .iter()
            .map(|item| restore_signature_type(modules, item))
            .collect::<Option<Vec<_>>>()
            .map(SignatureType::Tuple),
        CompiledSignatureType::Apply { callee, args } => Some(SignatureType::Apply {
            callee: Box::new(restore_signature_type(modules, callee)?),
            args: args
                .iter()
                .map(|arg| restore_signature_type(modules, arg))
                .collect::<Option<Vec<_>>>()?,
        }),
        CompiledSignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => Some(SignatureType::Function {
            param: Box::new(restore_signature_type(modules, param)?),
            arg_eff: match arg_eff {
                Some(row) => Some(restore_signature_effect_row(modules, row)?),
                None => None,
            },
            ret_eff: match ret_eff {
                Some(row) => Some(restore_signature_effect_row(modules, row)?),
                None => None,
            },
            ret: Box::new(restore_signature_type(modules, ret)?),
        }),
    }
}

fn restore_signature_effect_row(
    modules: &ModuleTable,
    row: &CompiledSignatureEffectRow,
) -> Option<SignatureEffectRow> {
    Some(SignatureEffectRow::new(
        row.items
            .iter()
            .map(|atom| match atom {
                CompiledSignatureEffectAtom::Type(ty) => Some(SignatureEffectAtom::Type(
                    restore_signature_type(modules, ty)?,
                )),
                CompiledSignatureEffectAtom::Wildcard => Some(SignatureEffectAtom::Wildcard),
            })
            .collect::<Option<Vec<_>>>()?,
        row.tail
            .as_ref()
            .map(|tail| SignatureVar::new(tail.clone())),
    ))
}

fn value_def_for_namespace_symbol(
    modules: &ModuleTable,
    namespace: &CompiledNamespaceSurface,
    symbol: u32,
) -> Option<DefId> {
    for module in &namespace.modules {
        let Some(live_module) = modules.module_by_path(&path_from_strings(&module.path)) else {
            continue;
        };
        let Some(value) = module.values.iter().find(|value| value.symbol == symbol) else {
            continue;
        };
        let name = Name(value.name.clone());
        let found = modules
            .value_decls(live_module, &name)
            .into_iter()
            .find(|decl| decl.order.index() == value.order)
            .map(|decl| decl.def);
        if found.is_some() {
            return found;
        }
    }
    None
}

fn value_def_for_namespace_path(modules: &ModuleTable, path: &[String]) -> Option<DefId> {
    let (name, module_path) = path.split_last()?;
    let module = modules.module_by_path(&path_from_strings(module_path))?;
    modules
        .value_decls(module, &Name(name.clone()))
        .into_iter()
        .find(|decl| {
            let mut found = namespace_path(&modules.module_path(module));
            found.push(decl.name.0.clone());
            found == path
        })
        .map(|decl| decl.def)
}

fn type_decl_for_namespace_path(
    modules: &ModuleTable,
    path: &[String],
) -> Option<crate::ModuleTypeDecl> {
    let (name, module_path) = path.split_last()?;
    let module = modules.module_by_path(&path_from_strings(module_path))?;
    modules
        .type_decls(module, &Name(name.clone()))
        .into_iter()
        .find(|decl| namespace_path(&modules.type_decl_path(decl)) == path)
}

fn path_from_strings(path: &[String]) -> Path {
    Path {
        segments: path.iter().cloned().map(Name).collect(),
    }
}

#[cfg(test)]
mod tests {
    use sources::{Name, Path, SourceFile};

    use crate::CompiledNamespaceSurface;
    use crate::lowering::lower_loaded_files;

    use super::*;

    #[test]
    fn lowering_surface_restores_act_type_vars_to_module_table() {
        let loaded = sources::load(vec![source(
            &[],
            "pub act signal 'a 'b:\n  pub ping: unit -> never\n",
        )]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let surface = CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
        let mut modules = lowering.modules.clone();
        let signal = modules
            .type_decls(modules.root_id(), &Name("signal".into()))
            .into_iter()
            .next()
            .unwrap();

        modules.act_type_vars.clear();
        assert_eq!(modules.act_type_vars(signal.id), None);

        surface.apply_to_module_table(&mut modules);

        assert_eq!(
            modules.act_type_vars(signal.id),
            Some(["a".to_string(), "b".to_string()].as_slice())
        );
    }

    #[test]
    fn lowering_surface_restores_lowered_signatures_to_module_table() {
        let loaded = sources::load(vec![source(
            &[],
            "pub act signal 'a:\n  pub ping: () -> 'a\n\npub struct Box 'a { value: 'a, self_value: self }\n\npub role Display 'a:\n  pub x.display: self\n",
        )]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let surface = CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
        let mut modules = lowering.modules.clone();
        clear_signature_metadata(&mut modules);

        surface.apply_to_module_table(&mut modules);

        let box_def = modules.value_decls(modules.root_id(), &Name("Box".into()))[0].def;
        let constructor = modules.constructor_by_def(box_def).unwrap();
        let ConstructorPayload::Record(fields) = &constructor.payload else {
            panic!("expected record payload");
        };
        assert!(
            fields
                .iter()
                .all(|field| matches!(field.ty, Some(StoredSignature::Lowered(_))))
        );

        let signal = modules.type_decls(modules.root_id(), &Name("signal".into()))[0].clone();
        assert!(
            modules
                .act_ops
                .get(&signal.id)
                .unwrap()
                .iter()
                .all(|op| matches!(op.signature, Some(StoredSignature::Lowered(_))))
        );

        let display = modules.type_decls(modules.root_id(), &Name("Display".into()))[0].clone();
        assert!(
            modules
                .role_methods(display.id)
                .iter()
                .all(|method| matches!(method.signature, Some(StoredSignature::Lowered(_))))
        );
    }

    fn clear_signature_metadata(modules: &mut ModuleTable) {
        for constructor in modules.constructors.values_mut() {
            match &mut constructor.payload {
                ConstructorPayload::Unit => {}
                ConstructorPayload::Tuple(items) => {
                    for item in items {
                        item.ty = None;
                    }
                }
                ConstructorPayload::Record(fields) => {
                    for field in fields {
                        field.ty = None;
                    }
                }
            }
        }
        for ops in modules.act_ops.values_mut() {
            for op in ops {
                op.signature = None;
            }
        }
        for methods in modules.role_methods.values_mut() {
            for method in methods {
                method.signature = None;
            }
        }
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
